import Paper26.MatrixCoordinates
import Paper26.ChartVolume
import Paper26.H1PosteriorBound
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Smooth priors for the actual matrix graph chart

The only external existence input is `NZSmoothLocalPriorInput C`, the exact
universal smooth local-prior statement of Nayak--Zhou, *Optimal Low-Rank
Quantum State Tomography with Bounded-Sample Joint Measurements*,
arXiv:2609.10514v1, Lemma 4.9, equation (61), with Fisher definition (59):
https://arxiv.org/html/2609.10514v1#S4.SS4.SSS2 .
Registry identifier: `P26-EXT-NZ-PRIOR`.

It retains all original quantifiers `d ≥ 2`, `1 ≤ r < d`, `a > 0`, the
actual rectangular operator-norm open ball, nonnegative smooth root,
compact support strictly inside that ball, unit squared integral, and the
original bound `C*p*d/a²`, where `p = 2*r*(d-r)`.  The real Fréchet-derivative
dual norm equals the Euclidean gradient norm, and `MatrixCoordinates`
provides the exact Frobenius/Euclidean and Lebesgue normalization.

The smooth-to-weak-H¹ bridge is proved here using Mathlib integration by
parts; it is not an external hypothesis.  The specialization `d=r+s`,
`a=1/2`, `r≤s`, the bound with universal constant `16*C`, normalization of
the actual matrix prior, and its actual graph-state pushforward are local
consequences.  No particular numerical universal constant is asserted.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal
open MeasureTheory Set

namespace Paper26.GraphPrior

open H1PosteriorBound MatrixCoordinates QuantumModel

local instance matrixMeasurableSpace (m n : Type*) : MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))

local instance matrixBorelSpace (m n : Type*) [Fintype m] [Fintype n] :
    BorelSpace (Matrix m n ℂ) := inferInstanceAs (BorelSpace (m → n → ℂ))

/-- Real root-gradient Fisher information, exactly the source definition (59). -/
def classicalFisher {p : ℕ} (ψ : ParameterSpace p → ℝ) : ℝ :=
  4 * ∫ x, ‖fderiv ℝ ψ x‖ ^ 2

/-- Every smooth compactly supported root is an actual weak H¹ root.
Both test-product integrability obligations and integration by parts are proved. -/
def smoothCompactRoot {p : ℕ} (ψ : ParameterSpace p → ℝ)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hc : HasCompactSupport ψ) : WeakH1Root p where
  root := ψ
  weakDerivative := fderiv ℝ ψ
  root_memLp := hψ.continuous.memLp_of_hasCompactSupport hc
  weakDerivative_memLp := (hψ.continuous_fderiv (by simp)).memLp_of_hasCompactSupport (hc.fderiv ℝ)
  compact_support := hc
  test_integration_by_parts := by
    intro φ hφ hcφ i
    let v := EuclideanSpace.basisFun (Fin p) ℝ i
    have hψv : Continuous (fun x => fderiv ℝ ψ x v) :=
      (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hφv : Continuous (fun x => fderiv ℝ φ x v) :=
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hi₁ : Integrable (fun x => ψ x * fderiv ℝ φ x v) volume :=
      (hψ.continuous.mul hφv).integrable_of_hasCompactSupport hc.mul_right
    have hi₂ : Integrable (fun x => fderiv ℝ ψ x v * φ x) volume :=
      (hψv.mul hφ.continuous).integrable_of_hasCompactSupport
        (hc.fderiv_apply ℝ v).mul_right
    have hi₀ : Integrable (fun x => ψ x * φ x) volume :=
      (hψ.continuous.mul hφ.continuous).integrable_of_hasCompactSupport hc.mul_right
    exact ⟨hi₁, hi₂, integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hi₂ hi₁ hi₀
      (hψ.differentiable (by simp)) (hφ.differentiable (by simp))⟩

/-- Squared real roots have the same actual mass in real and extended integrals. -/
theorem weak_mass_univ_eq_ofReal_integral {p : ℕ} (h : WeakH1Root p) :
    h.mass univ = ENNReal.ofReal (∫ x, h.root x ^ 2) := by
  unfold WeakH1Root.mass
  rw [Measure.restrict_univ]
  exact (ofReal_integral_eq_lintegral_ofReal h.root_memLp.integrable_sq
    (Filter.Eventually.of_forall (fun x => sq_nonneg (h.root x)))).symm

/-- The actual weak Fisher definition agrees with the source root-gradient integral. -/
theorem weak_fisher_eq_ofReal_integral {p : ℕ} (h : WeakH1Root p) :
    h.fisher = ENNReal.ofReal (4 * ∫ x, ‖h.weakDerivative x‖ ^ 2) := by
  have hi : Integrable (fun x => ‖h.weakDerivative x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm h.derivative_aestronglyMeasurable).mp
      h.weakDerivative_memLp
  have he : h.energy = ENNReal.ofReal (∫ x, ‖h.weakDerivative x‖ ^ 2) := by
    unfold WeakH1Root.energy
    rw [ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (fun x => sq_nonneg ‖h.weakDerivative x‖))]
    apply lintegral_congr
    intro x
    rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm_eq_enorm]
  rw [WeakH1Root.fisher, he, ENNReal.ofReal_mul (by norm_num)]
  norm_num

/-- Smooth roots have exactly their genuine Fréchet-derivative Fisher energy. -/
theorem smoothCompactRoot_fisher {p : ℕ} (ψ : ParameterSpace p → ℝ)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hc : HasCompactSupport ψ) :
    (smoothCompactRoot ψ hψ hc).fisher = ENNReal.ofReal (classicalFisher ψ) :=
  weak_fisher_eq_ofReal_integral _

/-- The actual matrix operator-norm open ball, expressed in the proved
Euclidean real coordinates. -/
def operatorBall (r s : ℕ) (a : ℝ) : Set (ParameterSpace (2 * r * s)) :=
  {x | ‖ChartVolume.operator ((coordinates r s).symm x)‖ < a}

/-- Raw smooth prior witness.  Its data are functions on the actual
Euclidean coordinates of the rectangular complex matrix parameter. -/
structure SmoothPriorWitness (r s : ℕ) (a : ℝ) where
  ψ : ParameterSpace (2 * r * s) → ℝ
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ
  nonnegative : ∀ x, 0 ≤ ψ x
  compact_support : HasCompactSupport ψ
  support_inside : tsupport ψ ⊆ operatorBall r s a
  integral_sq : (∫ x, ψ x ^ 2) = 1

/-- Precisely the original NZ Lemma 4.9 bound, before the P26 half-chart
specialization.  The universal constant is external; no `r*s²` bound is a field. -/
structure NZSmoothLocalPriorInput (C : ℝ) : Prop where
  local_prior : ∀ (d r : ℕ), 2 ≤ d → 1 ≤ r → r < d →
    ∀ (a : ℝ), 0 < a →
      ∃ w : SmoothPriorWitness r (d - r) a,
        classicalFisher w.ψ ≤ C * (2 * r * (d - r) : ℕ) * d / a ^ 2

/-- The original source has one positive universal constant for all dimensions and radii. -/
def NZPriorExistenceInput : Prop := ∃ C : ℝ, 0 < C ∧ NZSmoothLocalPriorInput C

namespace SmoothPriorWitness

variable {r s : ℕ} {a : ℝ} (w : SmoothPriorWitness r s a)

/-- The actual weak H¹ object used by posterior Fisher-volume bounds. -/
def weakRoot : WeakH1Root (2 * r * s) := smoothCompactRoot w.ψ w.smooth w.compact_support

@[simp] theorem weakRoot_root : w.weakRoot.root = w.ψ := rfl

@[simp] theorem weakRoot_derivative : w.weakRoot.weakDerivative = fderiv ℝ w.ψ := rfl

theorem weakRoot_normalized : w.weakRoot.mass univ = 1 := by
  rw [weak_mass_univ_eq_ofReal_integral]
  change ENNReal.ofReal (∫ x, w.ψ x ^ 2) = 1
  rw [w.integral_sq]
  norm_num

theorem weakRoot_fisher : w.weakRoot.fisher = ENNReal.ofReal (classicalFisher w.ψ) :=
  smoothCompactRoot_fisher _ _ _

/-- The actual density on the rectangular complex parameter entries. -/
def matrixDensity (X : Matrix (Fin s) (Fin r) ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (w.ψ (coordinates r s X) ^ 2)

theorem measurable_matrixDensity : Measurable w.matrixDensity :=
  ((w.smooth.continuous.measurable.comp (measurableEquiv r s).measurable).pow_const 2).ennreal_ofReal

/-- Its normalization is transported by the proved coordinate measure equality. -/
theorem matrixDensity_integral : (∫⁻ X, w.matrixDensity X ∂TailGeometry.matrixLebesgue) = 1 := by
  have hψm : Measurable (fun x => ENNReal.ofReal (w.ψ x ^ 2)) :=
    (w.smooth.continuous.measurable.pow_const 2).ennreal_ofReal
  change (∫⁻ X, ENNReal.ofReal (w.ψ (measurableEquiv r s X) ^ 2)
    ∂TailGeometry.matrixLebesgue) = 1
  calc
    _ = ∫⁻ x, ENNReal.ofReal (w.ψ x ^ 2) :=
      (volume_preserving_coordinates r s).lintegral_comp hψm
    _ = 1 := by
      simpa only [WeakH1Root.mass, Measure.restrict_univ, weakRoot_root] using w.weakRoot_normalized

/-- The normalized prior is an actual measure on complex matrices. -/
def matrixMeasure : Measure (Matrix (Fin s) (Fin r) ℂ) :=
  TailGeometry.matrixLebesgue.withDensity w.matrixDensity

instance matrixMeasure_probability : IsProbabilityMeasure w.matrixMeasure := by
  constructor
  change (TailGeometry.matrixLebesgue.withDensity w.matrixDensity) univ = 1
  calc
    _ = ∫⁻ X, w.matrixDensity X ∂TailGeometry.matrixLebesgue := by
      simpa only [Measure.restrict_univ] using
        (withDensity_apply (μ := TailGeometry.matrixLebesgue) w.matrixDensity MeasurableSet.univ)
    _ = 1 := w.matrixDensity_integral

/-- Nonzero prior density occurs strictly inside the original operator-norm ball. -/
theorem operator_lt_of_matrixDensity_ne_zero (X : Matrix (Fin s) (Fin r) ℂ)
    (hX : w.matrixDensity X ≠ 0) : ‖ChartVolume.operator X‖ < a := by
  have hψ : w.ψ (coordinates r s X) ≠ 0 := by
    intro hz
    simp [matrixDensity, hz] at hX
  have hs := w.support_inside (subset_closure (show coordinates r s X ∈ Function.support w.ψ from hψ))
  simpa only [operatorBall, Set.mem_setOf_eq, ContinuousLinearEquiv.symm_apply_apply] using hs

/-- The actual graph state for an Euclidean prior parameter. -/
def state [Nonempty (Fin r)] (_w : SmoothPriorWitness r s a) (x : ParameterSpace (2 * r * s)) : Density (Fin r ⊕ Fin s) :=
  GraphFamily.density ((coordinates r s).symm x)

theorem measurable_state [Nonempty (Fin r)] : Measurable w.state :=
  GraphFamily.measurable_density.comp (measurableEquiv r s).symm.measurable

theorem state_rank [Nonempty (Fin r)] (x : ParameterSpace (2 * r * s)) :
    (w.state x).matrix.rank = r := by
  simpa only [state, Fintype.card_fin] using GraphFamily.density_rank ((coordinates r s).symm x)

/-- The induced prior consists of actual graph-family density matrices. -/
def stateMeasure [Nonempty (Fin r)] : Measure (Density (Fin r ⊕ Fin s)) :=
  Measure.map GraphFamily.density w.matrixMeasure

instance stateMeasure_probability [Nonempty (Fin r)] : IsProbabilityMeasure w.stateMeasure :=
  Measure.isProbabilityMeasure_map GraphFamily.measurable_density.aemeasurable

end SmoothPriorWitness

/-- The P26 half-chart numerical specialization is proved from the raw
`C*p*d/a²` theorem: `p=2rs`, `d=r+s≤2s`, so `C₀=16C`. -/
theorem exists_halfChart_prior {C : ℝ} (hC : 0 < C) (N : NZSmoothLocalPriorInput C)
    (r s : ℕ) (hr : 0 < r) (hrs : r ≤ s) :
    ∃ w : SmoothPriorWitness r s (1 / 2 : ℝ),
      w.weakRoot.fisher ≤ ENNReal.ofReal ((16 * C) * r * (s : ℝ) ^ 2) := by
  have hs : 0 < s := lt_of_lt_of_le hr hrs
  obtain ⟨w, hw⟩ : ∃ w : SmoothPriorWitness r s (1 / 2 : ℝ),
      classicalFisher w.ψ ≤ C * (2 * r * s : ℕ) * (r + s : ℕ) / (1 / 2 : ℝ) ^ 2 := by
    have hlocal := N.local_prior (r + s) r (by omega) (by omega) (by omega)
      (1 / 2) (by norm_num)
    rw [show r + s - r = s by omega] at hlocal
    exact hlocal
  refine ⟨w, ?_⟩
  rw [w.weakRoot_fisher]
  apply ENNReal.ofReal_le_ofReal
  have hrsR : (r : ℝ) ≤ s := by exact_mod_cast hrs
  push_cast at hw
  norm_num at hw
  have hnonneg : 0 ≤ 8 * C * (r : ℝ) * s := by positivity
  have hmul := mul_le_mul_of_nonneg_left hrsR hnonneg
  nlinarith

/-- The universal-constant form of the prior existence required in Lemma 3.4. -/
theorem lemma_3_4_of_NZ (N : NZPriorExistenceInput) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (r s : ℕ), 0 < r → r ≤ s →
      ∃ w : SmoothPriorWitness r s (1 / 2 : ℝ),
        w.weakRoot.fisher ≤ ENNReal.ofReal (C₀ * r * (s : ℝ) ^ 2) := by
  obtain ⟨C, hC, hN⟩ := N
  exact ⟨16 * C, by positivity, fun r s hr hrs => exists_halfChart_prior hC hN r s hr hrs⟩

/-- The compact topological support of the actual H¹ root is inside the
Euclidean preimage of the closed operator-norm half-chart. -/
theorem halfChart_root_support (r s : ℕ) (w : SmoothPriorWitness r s (1 / 2 : ℝ)) :
    tsupport w.weakRoot.root ⊆
      {x | (coordinates r s).symm x ∈ ChartVolume.localChart r s} := by
  intro x hx
  have hs : ‖ChartVolume.operator ((coordinates r s).symm x)‖ < (1 / 2 : ℝ) :=
    w.support_inside hx
  exact hs.le

/-- Every half-chart prior is supported on the actual closed operator-norm
half-ball used by the local volume comparison. -/
theorem halfChart_prior_support (r s : ℕ) (w : SmoothPriorWitness r s (1 / 2 : ℝ)) :
    w.matrixMeasure ((ChartVolume.localChart r s)ᶜ) = 0 := by
  rw [SmoothPriorWitness.matrixMeasure, withDensity_apply_eq_zero w.measurable_matrixDensity]
  have hempty : {X | w.matrixDensity X ≠ 0} ∩ (ChartVolume.localChart r s)ᶜ = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro X hX
    exact hX.2 (show X ∈ ChartVolume.localChart r s from
      (w.operator_lt_of_matrixDensity_ne_zero X hX.1).le)
  rw [hempty, measure_empty]

end Paper26.GraphPrior
