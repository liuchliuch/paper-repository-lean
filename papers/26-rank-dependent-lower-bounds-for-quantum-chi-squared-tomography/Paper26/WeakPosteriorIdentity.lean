import Paper26.H1PosteriorBound
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Analytic bridges for the general posterior information identity

This file keeps weak H¹ roots, actual Bayes normalizers, and arbitrary measurable
outcome spaces. It does not assume Lemma 3.2 as an external field. The classical
weak-derivative uniqueness interface below is a generic distributional fact,
independent of likelihoods, posteriors, or information identities.

## Classical inputs and source scope

`WeakDerivativeUniquenessInput` is ordinary uniqueness of distributional weak
derivatives (Hajłasz, *Non-linear elliptic partial differential equations*,
Cortona lectures, §2.1 after Definition 2.1 and Lemma 1.3, printed p. 9).
`WeakLocallyLipschitzProductInput` is the ordinary compact-support weak Leibniz
rule: the same lectures' Proposition 2.18 and Theorem 2.23 give the ACL product
rule and identification with classical partial derivatives; Corollary 2.30
makes the weak gradient zero off the support. The a.e. Fréchet derivative is
identified by Rademacher. These are precise classical inputs, not proved in this
file and not entire posterior-information identities.

The final local-energy theorem explicitly assumes joint measurability of the
original likelihood roots and their classical derivative representatives. An
actual measurable experiment must supply these measure-theoretic facts; they
are not consequences of local Lipschitz regularity alone with no outcome
measurability. Conditional L² and score-integrability conditions, on the other
hand, are derived here from normalization and local gradient energies.

All Tonelli statements require `SFinite ν`. In particular they apply to every
finite reference measure, as in the quantum application. This file does not
claim the source's arbitrary-reference-measure wording without this explicit
condition. The identity is an ENNReal identity even when the data energy is
infinite; its finite-information specialization follows immediately by imposing
the source's finite prior-averaged data information.
-/
noncomputable section
open scoped ENNReal NNReal BigOperators
open MeasureTheory Set

namespace Paper26.WeakPosteriorIdentity

open H1PosteriorBound

variable {p : ℕ}

/-- Constant multiplication is proved directly on the weak test-function
identities and L² conditions, rather than supplied as an external input. -/
def scaleRoot (c : ℝ) (h : WeakH1Root p) : WeakH1Root p where
  root := fun x => c * h.root x
  weakDerivative := fun x => c • h.weakDerivative x
  root_memLp := h.root_memLp.const_mul c
  weakDerivative_memLp := h.weakDerivative_memLp.const_smul c
  compact_support := h.compact_support.comp_left (by simp)
  test_integration_by_parts := by
    intro φ hφ hc i
    rcases h.test_integration_by_parts φ hφ hc i with ⟨hl, hr, he⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa only [mul_assoc] using hl.const_mul c
    · simpa only [ContinuousLinearMap.smul_apply, smul_eq_mul, mul_assoc] using hr.const_mul c
    · simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, mul_assoc]
      rw [integral_const_mul, integral_const_mul, he]
      ring

@[simp] theorem scaleRoot_root (c : ℝ) (h : WeakH1Root p) (x : ParameterSpace p) :
    (scaleRoot c h).root x = c * h.root x := rfl

@[simp] theorem scaleRoot_derivative (c : ℝ) (h : WeakH1Root p) (x : ParameterSpace p) :
    (scaleRoot c h).weakDerivative x = c • h.weakDerivative x := rfl

theorem mass_scaleRoot (c : ℝ) (h : WeakH1Root p) (s : Set (ParameterSpace p)) :
    (scaleRoot c h).mass s = ENNReal.ofReal (c ^ 2) * h.mass s := by
  unfold WeakH1Root.mass
  simp only [scaleRoot_root, mul_pow,
    ENNReal.ofReal_mul (sq_nonneg c)]
  exact lintegral_const_mul'' _
    (ENNReal.continuous_ofReal.measurable.comp_aemeasurable
      (h.root_aestronglyMeasurable.aemeasurable.pow_const 2)).restrict

theorem fisher_scaleRoot (c : ℝ) (h : WeakH1Root p) :
    (scaleRoot c h).fisher = ENNReal.ofReal (c ^ 2) * h.fisher := by
  have he : (scaleRoot c h).energy = ENNReal.ofReal (c ^ 2) * h.energy := by
    unfold WeakH1Root.energy
    simp only [scaleRoot_derivative, enorm_smul, mul_pow]
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg c) 2, sq_abs]
    exact lintegral_const_mul'' _ (h.derivative_aestronglyMeasurable.enorm.pow_const 2)
  unfold WeakH1Root.fisher
  rw [he]
  ac_rfl

theorem mass_univ_ne_top (h : WeakH1Root p) : h.mass univ ≠ ∞ := by
  have he : h.mass univ = eLpNorm h.root 2 volume ^ (2 : ℕ) := by
    rw [h.mass_eq_rootMass]
    unfold FisherVolume.rootMass
    rw [Measure.restrict_univ]
    simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two] using
      (eLpNorm_nnreal_pow_eq_lintegral (μ := volume) (f := h.root)
        (p := (2 : ℝ≥0)) (by norm_num)).symm
  rw [he]
  exact ENNReal.pow_ne_top h.root_memLp.eLpNorm_lt_top.ne

/-- A generic uniqueness theorem for weak derivatives. No posterior object,
likelihood, normalization, or information equality occurs in this interface. -/
def WeakDerivativeUniquenessInput (p : ℕ) : Prop :=
  ∀ h k : WeakH1Root p, h.root =ᵐ[volume] k.root →
    h.weakDerivative =ᵐ[volume] k.weakDerivative

/-- Zero-mass weak roots have zero derivative energy, relative only to the
ordinary uniqueness of a distributional weak derivative. -/
theorem fisher_eq_zero_of_mass_zero (U : WeakDerivativeUniquenessInput p)
    (h : WeakH1Root p) (hm : h.mass univ = 0) : h.fisher = 0 := by
  have hr : h.root =ᵐ[volume] (fun _ => 0) := by
    have hm' : (∫⁻ x, ENNReal.ofReal (h.root x ^ (2 : ℕ))) = 0 := by
      simpa only [WeakH1Root.mass, Measure.restrict_univ] using hm
    have hz := (lintegral_eq_zero_iff'
      (ENNReal.continuous_ofReal.measurable.comp_aemeasurable
        (h.root_aestronglyMeasurable.aemeasurable.pow_const 2))).mp hm'
    filter_upwards [hz] with x hx
    have hs : h.root x ^ (2 : ℕ) ≤ 0 := ENNReal.ofReal_eq_zero.mp hx
    nlinarith [sq_nonneg (h.root x)]
  have hd : h.weakDerivative =ᵐ[volume] (fun _ => 0) := by
    have he := U h (scaleRoot 0 h) (by
      change h.root =ᵐ[volume] (fun x => (0 : ℝ) * h.root x)
      simpa only [zero_mul] using hr)
    change h.weakDerivative =ᵐ[volume] (fun x => (0 : ℝ) • h.weakDerivative x) at he
    simpa only [zero_smul] using he
  unfold WeakH1Root.fisher WeakH1Root.energy
  have hz : (∫⁻ x, ‖h.weakDerivative x‖ₑ ^ (2 : ℕ)) = 0 := by
    calc
      (∫⁻ x, ‖h.weakDerivative x‖ₑ ^ (2 : ℕ)) = ∫⁻ _x : ParameterSpace p, 0 := by
        apply lintegral_congr_ae
        filter_upwards [hd] with x hx
        rw [hx, ← ofReal_norm, norm_zero, ENNReal.ofReal_zero, zero_pow two_ne_zero]
      _ = 0 := by simp
  rw [hz, mul_zero]

/-- Normalize an actual weak product root by its actual marginal mass.
At zero marginal this total definition is the zero root. -/
def bayesRoot (productRoot : WeakH1Root p) : WeakH1Root p :=
  scaleRoot (Real.sqrt (productRoot.mass univ).toReal)⁻¹ productRoot

theorem marginal_mul_normalization_factor (h : WeakH1Root p)
    (hm : h.mass univ ≠ 0) :
    h.mass univ * ENNReal.ofReal (((Real.sqrt (h.mass univ).toReal)⁻¹) ^ 2) = 1 := by
  have hp : 0 < (h.mass univ).toReal :=
    ENNReal.toReal_pos hm (mass_univ_ne_top h)
  have he : (h.mass univ).toReal * ((Real.sqrt (h.mass univ).toReal)⁻¹) ^ 2 = 1 := by
    rw [inv_pow, Real.sq_sqrt hp.le]
    exact mul_inv_cancel₀ hp.ne'
  calc
    h.mass univ * ENNReal.ofReal (((Real.sqrt (h.mass univ).toReal)⁻¹) ^ 2) =
        ENNReal.ofReal (h.mass univ).toReal *
          ENNReal.ofReal (((Real.sqrt (h.mass univ).toReal)⁻¹) ^ 2) := by
      congr 1
      exact (ENNReal.ofReal_toReal (mass_univ_ne_top h)).symm
    _ = ENNReal.ofReal ((h.mass univ).toReal *
        ((Real.sqrt (h.mass univ).toReal)⁻¹) ^ 2) :=
      (ENNReal.ofReal_mul ENNReal.toReal_nonneg).symm
    _ = 1 := by rw [he, ENNReal.ofReal_one]

theorem bayesRoot_normalized (h : WeakH1Root p) (hm : h.mass univ ≠ 0) :
    (bayesRoot h).mass univ = 1 := by
  rw [bayesRoot, mass_scaleRoot, mul_comm]
  exact marginal_mul_normalization_factor h hm

/-- Marginal weighting cancels the actual Bayes normalizer. The zero marginal
case is proved from weak-derivative uniqueness, rather than omitted. -/
theorem marginal_mul_bayesRoot_fisher (U : WeakDerivativeUniquenessInput p)
    (h : WeakH1Root p) :
    h.mass univ * (bayesRoot h).fisher = h.fisher := by
  by_cases hm : h.mass univ = 0
  · rw [hm, zero_mul, fisher_eq_zero_of_mass_zero U h hm]
  · rw [bayesRoot, fisher_scaleRoot, ← mul_assoc,
      marginal_mul_normalization_factor h hm, one_mul]

/-- The actual Leibniz candidate for the weak derivative of `h*g`. -/
def weakProductDerivative (h : WeakH1Root p) (g : ParameterSpace p → ℝ)
    (x : ParameterSpace p) : ParameterSpace p →L[ℝ] ℝ :=
  g x • h.weakDerivative x + h.root x • fderiv ℝ g x

/-- Generic classical weak Leibniz rule, including identification of the
locally Lipschitz multiplier's weak derivative with its a.e. classical
Fréchet derivative. It quantifies over arbitrary functions and has no outcome,
Bayes, score, or information-identity conclusion.

A product-root representative may be chosen to have the displayed root and
weak derivative pointwise, since changing the a.e. representative does not
change weak integration by parts. The separate distributional uniqueness
input handles zero marginal roots. -/
def WeakLocallyLipschitzProductInput (p : ℕ) : Prop :=
  ∀ (h : WeakH1Root p) (g : ParameterSpace p → ℝ), LocallyLipschitz g →
    ∃ k : WeakH1Root p, (∀ x, k.root x = h.root x * g x) ∧
      ∀ x, k.weakDerivative x = weakProductDerivative h g x

/-- Build the actual product weak H¹ root using only the generic classical
Leibniz input. Non-locally-Lipschitz exceptional outcomes are assigned zero. -/
def weakProductRoot (P : WeakLocallyLipschitzProductInput p)
    (h : WeakH1Root p) (g : ParameterSpace p → ℝ) : WeakH1Root p := by
  classical
  exact if hg : LocallyLipschitz g then Classical.choose (P h g hg) else scaleRoot 0 h

theorem weakProductRoot_root (P : WeakLocallyLipschitzProductInput p)
    (h : WeakH1Root p) (g : ParameterSpace p → ℝ) (hg : LocallyLipschitz g)
    (x : ParameterSpace p) : (weakProductRoot P h g).root x = h.root x * g x := by
  classical
  simp only [weakProductRoot, dif_pos hg]
  exact (Classical.choose_spec (P h g hg)).1 x

theorem weakProductRoot_derivative (P : WeakLocallyLipschitzProductInput p)
    (h : WeakH1Root p) (g : ParameterSpace p → ℝ) (hg : LocallyLipschitz g)
    (x : ParameterSpace p) :
    (weakProductRoot P h g).weakDerivative x = weakProductDerivative h g x := by
  classical
  simp only [weakProductRoot, dif_pos hg]
  exact (Classical.choose_spec (P h g hg)).2 x

section Outcome
variable {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)

/-- The genuine marginal density of the product prior/likelihood roots. -/
def marginal (h : WeakH1Root p) (g : Y → ParameterSpace p → ℝ) (y : Y) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((h.root x * g y x) ^ 2)

theorem marginal_aemeasurable (h : WeakH1Root p) (g : Y → ParameterSpace p → ℝ)
    (hj : AEMeasurable
      (fun z : Y × ParameterSpace p => ENNReal.ofReal ((h.root z.2 * g z.1 z.2) ^ 2))
      (ν.prod volume)) : AEMeasurable (marginal h g) ν :=
  hj.lintegral_prod_right'

/-- The actual joint prior-times-likelihood density is measurable whenever
the original likelihood root is jointly measurable. -/
theorem jointDensity_aemeasurable
    (h : WeakH1Root p) (g : Y → ParameterSpace p → ℝ)
    (hG : AEStronglyMeasurable (fun z : Y × ParameterSpace p => g z.1 z.2)
      (ν.prod volume)) : AEMeasurable
      (fun z : Y × ParameterSpace p => ENNReal.ofReal ((h.root z.2 * g z.1 z.2) ^ 2))
      (ν.prod volume) :=
  ENNReal.continuous_ofReal.measurable.comp_aemeasurable
    ((h.root_aestronglyMeasurable.comp_snd.mul hG).pow 2).aemeasurable

/-- Tonelli proves that actual Bayes marginals integrate to one. Outcome spaces
are arbitrary measurable spaces; `SFinite ν` is the explicit Tonelli condition.
The joint density measurability and likelihood normalization are exact inputs,
not a posterior-normalization conclusion. -/
theorem marginal_integral_one [SFinite ν]
    (h : WeakH1Root p) (g : Y → ParameterSpace p → ℝ)
    (hj : AEMeasurable
      (fun z : Y × ParameterSpace p => ENNReal.ofReal ((h.root z.2 * g z.1 z.2) ^ 2))
      (ν.prod volume))
    (hg : ∀ x, AEMeasurable (fun y => ENNReal.ofReal (g y x ^ 2)) ν)
    (hn : ∀ x, (∫⁻ y, ENNReal.ofReal (g y x ^ 2) ∂ν) = 1)
    (hh : h.mass univ = 1) : (∫⁻ y, marginal h g y ∂ν) = 1 := by
  unfold marginal
  rw [lintegral_lintegral_swap hj]
  have he : ∀ x, (∫⁻ y, ENNReal.ofReal ((h.root x * g y x) ^ 2) ∂ν) =
      ENNReal.ofReal (h.root x ^ 2) := by
    intro x
    simp only [mul_pow, ENNReal.ofReal_mul (sq_nonneg (h.root x))]
    rw [lintegral_const_mul'' _ (hg x), hn x, mul_one]
  simp_rw [he]
  simpa only [WeakH1Root.mass, Measure.restrict_univ] using hh

theorem marginal_finite_ae [SFinite ν]
    (h : WeakH1Root p) (g : Y → ParameterSpace p → ℝ)
    (hj : AEMeasurable
      (fun z : Y × ParameterSpace p => ENNReal.ofReal ((h.root z.2 * g z.1 z.2) ^ 2))
      (ν.prod volume))
    (hg : ∀ x, AEMeasurable (fun y => ENNReal.ofReal (g y x ^ 2)) ν)
    (hn : ∀ x, (∫⁻ y, ENNReal.ofReal (g y x ^ 2) ∂ν) = 1)
    (hh : h.mass univ = 1) : ∀ᵐ y ∂ν, marginal h g y ≠ ∞ := by
  have hi : (∫⁻ y, marginal h g y ∂ν) ≠ ∞ := by
    rw [marginal_integral_one ν h g hj hg hn hh]
    exact ENNReal.one_ne_top
  exact (ae_lt_top' (marginal_aemeasurable ν h g hj) hi).mono fun _ hx => hx.ne

/-- A scalar conditional squared-energy calculation. Cross-term integrability
is derived internally from L² Hölder (`MemLp.integrable_mul`). -/
theorem integral_affine_square {g d : Y → ℝ}
    (hg : MemLp g 2 ν) (hd : MemLp d 2 ν)
    (hn : (∫ y, g y ^ 2 ∂ν) = 1) (hz : (∫ y, g y * d y ∂ν) = 0)
    (a b : ℝ) :
    (∫ y, (g y * a + b * d y) ^ 2 ∂ν) =
      a ^ 2 + b ^ 2 * (∫ y, d y ^ 2 ∂ν) := by
  have hgd : Integrable (fun y => g y * d y) ν := hg.integrable_mul hd
  have he : (fun y => (g y * a + b * d y) ^ 2) =
      (fun y => a ^ 2 * g y ^ 2 + b ^ 2 * d y ^ 2 +
        (2 * a * b) * (g y * d y)) := by
    funext y
    ring
  calc
    (∫ y, (g y * a + b * d y) ^ 2 ∂ν) =
        (∫ y, a ^ 2 * g y ^ 2 + b ^ 2 * d y ^ 2 ∂ν) +
          ∫ y, (2 * a * b) * (g y * d y) ∂ν := by
      rw [he]
      exact integral_add ((hg.integrable_sq.const_mul _).add (hd.integrable_sq.const_mul _))
        (hgd.const_mul _)
    _ = ((∫ y, a ^ 2 * g y ^ 2 ∂ν) + (∫ y, b ^ 2 * d y ^ 2 ∂ν)) +
          ∫ y, (2 * a * b) * (g y * d y) ∂ν := by
      congr 1
      exact integral_add (hg.integrable_sq.const_mul _) (hd.integrable_sq.const_mul _)
    _ = a ^ 2 + b ^ 2 * (∫ y, d y ^ 2 ∂ν) := by
      rw [integral_const_mul, integral_const_mul, integral_const_mul, hn, hz]
      ring

/-- Differentiation of a normalized outcome integral gives a zero score. The
premise is precisely the source's differentiation-under-the-integral regularity;
it contains no posterior information equality. -/
theorem normalized_integral_derivative_zero
    (g : Y → ParameterSpace p → ℝ)
    (hn : ∀ x, (∫ y, g y x ^ 2 ∂ν) = 1)
    {x : ParameterSpace p} (D : ParameterSpace p →L[ℝ] ℝ)
    (hd : HasFDerivAt (fun t => ∫ y, g y t ^ 2 ∂ν) D x) : D = 0 := by
  have he : (fun t => ∫ y, g y t ^ 2 ∂ν) = (fun _ : ParameterSpace p => (1 : ℝ)) :=
    funext hn
  rw [he] at hd
  exact hd.unique (hasFDerivAt_const 1 x)

/-- Coordinate expression of the Euclidean squared norm of a weak derivative. -/
def dualEnergy (D : ParameterSpace p →L[ℝ] ℝ) : ℝ :=
  ∑ i, (D (EuclideanSpace.basisFun (Fin p) ℝ i)) ^ 2

theorem dualEnergy_eq_norm_sq (D : ParameterSpace p →L[ℝ] ℝ) :
    dualEnergy D = ‖D‖ ^ 2 := by
  have he := (EuclideanSpace.basisFun (Fin p) ℝ).sum_sq_norm_inner_left
    ((InnerProductSpace.toDual ℝ (ParameterSpace p)).symm D)
  simpa only [dualEnergy, InnerProductSpace.toDual_symm_apply,
    Real.norm_eq_abs, sq_abs, LinearIsometryEquiv.norm_map] using he

/-- Source normalization and differentiation-under-the-integral regularity
imply that each coordinate of the square-root score has mean zero. -/
theorem score_coordinate_zero
    (g : Y → ParameterSpace p → ℝ)
    (hn : ∀ x, (∫ y, g y x ^ 2 ∂ν) = 1)
    {x : ParameterSpace p} (D : Y → (ParameterSpace p →L[ℝ] ℝ))
    (hscore : Integrable (fun y => (2 * g y x) • D y) ν)
    (hd : HasFDerivAt (fun t => ∫ y, g y t ^ 2 ∂ν)
      (∫ y, (2 * g y x) • D y ∂ν) x) (i : Fin p) :
    (∫ y, g y x * D y (EuclideanSpace.basisFun (Fin p) ℝ i) ∂ν) = 0 := by
  have hz := normalized_integral_derivative_zero ν g hn _ hd
  have hv := congrArg (fun L : ParameterSpace p →L[ℝ] ℝ =>
    L (EuclideanSpace.basisFun (Fin p) ℝ i)) hz
  change (∫ y, (2 * g y x) • D y ∂ν)
    (EuclideanSpace.basisFun (Fin p) ℝ i) = 0 at hv
  rw [ContinuousLinearMap.integral_apply hscore] at hv
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul] at hv
  have he : (fun y => 2 * g y x * D y (EuclideanSpace.basisFun (Fin p) ℝ i)) =
      (fun y => 2 * (g y x * D y (EuclideanSpace.basisFun (Fin p) ℝ i))) := by
    funext y
    ring
  rw [he, integral_const_mul] at hv
  linarith

/-- The continuous-outcome conditional energy identity at a fixed parameter.
Every cross term is proved integrable by L² Hölder inside
`integral_affine_square`; no finite outcome assumption is used. -/
theorem conditional_product_energy
    (g : Y → ℝ) (D : Y → (ParameterSpace p →L[ℝ] ℝ))
    (hg : MemLp g 2 ν)
    (hD : ∀ i : Fin p,
      MemLp (fun y => D y (EuclideanSpace.basisFun (Fin p) ℝ i)) 2 ν)
    (hn : (∫ y, g y ^ 2 ∂ν) = 1)
    (hz : ∀ i : Fin p,
      (∫ y, g y * D y (EuclideanSpace.basisFun (Fin p) ℝ i) ∂ν) = 0)
    (A : ParameterSpace p →L[ℝ] ℝ) (b : ℝ) :
    (∫ y, ‖g y • A + b • D y‖ ^ 2 ∂ν) =
      ‖A‖ ^ 2 + b ^ 2 * (∫ y, ‖D y‖ ^ 2 ∂ν) := by
  have he : ∀ y, ‖g y • A + b • D y‖ ^ 2 =
      ∑ i : Fin p, (g y * A (EuclideanSpace.basisFun (Fin p) ℝ i) +
        b * D y (EuclideanSpace.basisFun (Fin p) ℝ i)) ^ 2 := by
    intro y
    rw [← dualEnergy_eq_norm_sq]
    simp only [dualEnergy, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hd : (∫ y, ‖D y‖ ^ 2 ∂ν) =
      ∑ i : Fin p, ∫ y, (D y (EuclideanSpace.basisFun (Fin p) ℝ i)) ^ 2 ∂ν := by
    simp_rw [← dualEnergy_eq_norm_sq, dualEnergy]
    exact integral_finset_sum Finset.univ (fun i _ => (hD i).integrable_sq)
  calc
    (∫ y, ‖g y • A + b • D y‖ ^ 2 ∂ν) =
        ∑ i : Fin p, ∫ y, (g y * A (EuclideanSpace.basisFun (Fin p) ℝ i) +
          b * D y (EuclideanSpace.basisFun (Fin p) ℝ i)) ^ 2 ∂ν := by
      simp_rw [he]
      exact integral_finset_sum Finset.univ (fun i _ =>
        (((hg.const_mul (A (EuclideanSpace.basisFun (Fin p) ℝ i))).add
          ((hD i).const_mul b)).integrable_sq).congr
            (Filter.Eventually.of_forall (fun y => by
              dsimp only [Pi.add_apply]
              ring)))
    _ = ∑ i : Fin p, ((A (EuclideanSpace.basisFun (Fin p) ℝ i)) ^ 2 +
        b ^ 2 * (∫ y, (D y (EuclideanSpace.basisFun (Fin p) ℝ i)) ^ 2 ∂ν)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact integral_affine_square ν hg (hD i) hn (hz i) _ b
    _ = ‖A‖ ^ 2 + b ^ 2 * (∫ y, ‖D y‖ ^ 2 ∂ν) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hd]
      change dualEnergy A + _ = _
      rw [dualEnergy_eq_norm_sq]

/-- Coordinate L² conditions imply integrability of the actual squared
operator norm in finite Euclidean dimension. -/
theorem integrable_dual_norm_sq (D : Y → (ParameterSpace p →L[ℝ] ℝ))
    (hD : ∀ i : Fin p,
      MemLp (fun y => D y (EuclideanSpace.basisFun (Fin p) ℝ i)) 2 ν) :
    Integrable (fun y => ‖D y‖ ^ 2) ν := by
  have hi : Integrable (fun y => ∑ i : Fin p,
      (D y (EuclideanSpace.basisFun (Fin p) ℝ i)) ^ 2) ν :=
    integrable_finset_sum Finset.univ (fun i _ => (hD i).integrable_sq)
  exact hi.congr (Filter.Eventually.of_forall (fun y => dualEnergy_eq_norm_sq (D y)))

theorem enorm_sq_eq_ofReal_norm_sq (D : ParameterSpace p →L[ℝ] ℝ) :
    ‖D‖ₑ ^ (2 : ℕ) = ENNReal.ofReal (‖D‖ ^ (2 : ℕ)) := by
  rw [ENNReal.ofReal_pow (norm_nonneg D) 2, ofReal_norm]

/-- The conditional energy identity as an actual nonnegative integral. -/
theorem conditional_product_energy_lintegral
    (g : Y → ℝ) (D : Y → (ParameterSpace p →L[ℝ] ℝ))
    (hg : MemLp g 2 ν)
    (hD : ∀ i : Fin p,
      MemLp (fun y => D y (EuclideanSpace.basisFun (Fin p) ℝ i)) 2 ν)
    (hn : (∫ y, g y ^ 2 ∂ν) = 1)
    (hz : ∀ i : Fin p,
      (∫ y, g y * D y (EuclideanSpace.basisFun (Fin p) ℝ i) ∂ν) = 0)
    (A : ParameterSpace p →L[ℝ] ℝ) (b : ℝ) :
    (∫⁻ y, ‖g y • A + b • D y‖ₑ ^ (2 : ℕ) ∂ν) =
      ‖A‖ₑ ^ (2 : ℕ) + ENNReal.ofReal (b ^ 2) *
        (∫⁻ y, ‖D y‖ₑ ^ (2 : ℕ) ∂ν) := by
  have hprod : ∀ i : Fin p, MemLp
      (fun y => (g y • A + b • D y) (EuclideanSpace.basisFun (Fin p) ℝ i)) 2 ν := by
    intro i
    refine (memLp_congr_ae ?_).1 ((hg.const_mul
      (A (EuclideanSpace.basisFun (Fin p) ℝ i))).add ((hD i).const_mul b))
    apply Filter.Eventually.of_forall
    intro y
    simp only [Pi.add_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hi := integrable_dual_norm_sq ν _ hprod
  have hd := integrable_dual_norm_sq ν D hD
  have hpnon : (0 : ℝ) ≤ ∫ y, ‖D y‖ ^ (2 : ℕ) ∂ν :=
    integral_nonneg (fun _ => sq_nonneg _)
  calc
    (∫⁻ y, ‖g y • A + b • D y‖ₑ ^ (2 : ℕ) ∂ν) =
        ENNReal.ofReal (∫ y, ‖g y • A + b • D y‖ ^ (2 : ℕ) ∂ν) := by
      rw [ofReal_integral_eq_lintegral_ofReal hi
        (Filter.Eventually.of_forall (fun _ => sq_nonneg _))]
      exact lintegral_congr (fun y => enorm_sq_eq_ofReal_norm_sq _)
    _ = ENNReal.ofReal (‖A‖ ^ 2 + b ^ 2 * (∫ y, ‖D y‖ ^ 2 ∂ν)) := by
      rw [conditional_product_energy ν g D hg hD hn hz A b]
    _ = ‖A‖ₑ ^ (2 : ℕ) + ENNReal.ofReal (b ^ 2) *
        (∫⁻ y, ‖D y‖ₑ ^ (2 : ℕ) ∂ν) := by
      rw [ENNReal.ofReal_add (sq_nonneg _) (mul_nonneg (sq_nonneg _) hpnon),
        ENNReal.ofReal_mul (sq_nonneg _),
        ofReal_integral_eq_lintegral_ofReal hd
          (Filter.Eventually.of_forall (fun _ => sq_nonneg _)),
        ← enorm_sq_eq_ofReal_norm_sq A]
      congr 1
      congr 1
      exact lintegral_congr (fun y => (enorm_sq_eq_ofReal_norm_sq (D y)).symm)

/-- A real square-root density with finite actual squared mass is L². -/
theorem memLp_two_of_lintegral_sq_ne_top {g : Y → ℝ}
    (hg : AEStronglyMeasurable g ν)
    (hfin : (∫⁻ y, ENNReal.ofReal (g y ^ 2) ∂ν) ≠ ∞) : MemLp g 2 ν := by
  exact (memLp_two_iff_integrable_sq hg).2
    ((lintegral_ofReal_ne_top_iff_integrable (hg.pow 2)
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).1 hfin)

/-- A finite true gradient energy gives L² membership for the entire dual
vector; the finite-dimensional coordinate conditions are then consequences. -/
theorem memLp_two_of_lintegral_dual_energy_ne_top
    {D : Y → (ParameterSpace p →L[ℝ] ℝ)} (hD : AEStronglyMeasurable D ν)
    (hfin : (∫⁻ y, ‖D y‖ₑ ^ (2 : ℕ) ∂ν) ≠ ∞) : MemLp D 2 ν := by
  apply (memLp_two_iff_integrable_sq_norm hD).2
  apply (lintegral_ofReal_ne_top_iff_integrable (hD.norm.pow 2)
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).1
  change (∫⁻ y, ENNReal.ofReal (‖D y‖ ^ (2 : ℕ)) ∂ν) ≠ ∞
  simpa only [← enorm_sq_eq_ofReal_norm_sq] using hfin

/-- Coordinate L² is a native consequence of dual-vector L². -/
theorem coordinate_memLp_two
    {D : Y → (ParameterSpace p →L[ℝ] ℝ)} (hD : MemLp D 2 ν) (i : Fin p) :
    MemLp (fun y => D y (EuclideanSpace.basisFun (Fin p) ℝ i)) 2 ν :=
  hD.continuousLinearMap_comp
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin p) ℝ i))

/-- The vector square-root score is integrable by L² Hölder. This is proved
from the two energies and is not a new regularity assumption. -/
theorem score_integrable_of_memLp_two {g : Y → ℝ}
    {D : Y → (ParameterSpace p →L[ℝ] ℝ)} (hg : MemLp g 2 ν) (hD : MemLp D 2 ν) :
    Integrable (fun y => (2 * g y) • D y) ν := by
  exact memLp_one_iff_integrable.1 (hD.smul (hg.const_mul 2))

/-- A nonnegative locally integrable energy is finite almost everywhere. A
countable measurable exhaustion records precisely the local-to-a.e. step;
closed balls give the usual Euclidean specialization. -/
theorem ae_ne_top_of_local_lintegral
    (f : ParameterSpace p → ℝ≥0∞) (hf : AEMeasurable f volume)
    (K : ℕ → Set (ParameterSpace p)) (hK : ∀ n, MeasurableSet (K n))
    (hcover : ∀ x, ∃ n, x ∈ K n)
    (hfin : ∀ n, (∫⁻ x in K n, f x) ≠ ∞) :
    ∀ᵐ x ∂(volume : Measure (ParameterSpace p)), f x ≠ ∞ := by
  have hlocal : ∀ n, ∀ᵐ x ∂(volume : Measure (ParameterSpace p)),
      x ∈ K n → f x ≠ ∞ := by
    intro n
    apply (ae_restrict_iff' (hK n)).1
    exact (ae_lt_top' hf.restrict (hfin n)).mono (fun _ hx => hx.ne)
  filter_upwards [ae_all_iff.2 hlocal] with x hx
  obtain ⟨n, hn⟩ := hcover x
  exact hx n hn

/-- Jointly measurable gradients and local squared energies imply the a.e.
conditional full-vector L² condition needed by the posterior calculation. -/
theorem gradient_memLp_two_ae_of_local_energy [SFinite ν]
    (g : Y → ParameterSpace p → ℝ)
    (hD : AEStronglyMeasurable
      (fun z : Y × ParameterSpace p => fderiv ℝ (g z.1) z.2) (ν.prod volume))
    (K : ℕ → Set (ParameterSpace p)) (hK : ∀ n, MeasurableSet (K n))
    (hcover : ∀ x, ∃ n, x ∈ K n)
    (hfin : ∀ n, (∫⁻ x in K n,
      (∫⁻ y, ‖fderiv ℝ (g y) x‖ₑ ^ (2 : ℕ) ∂ν)) ≠ ∞) :
    ∀ᵐ x ∂(volume : Measure (ParameterSpace p)),
      MemLp (fun y => fderiv ℝ (g y) x) 2 ν := by
  have hfinite := ae_ne_top_of_local_lintegral
    (fun x => ∫⁻ y, ‖fderiv ℝ (g y) x‖ₑ ^ (2 : ℕ) ∂ν)
    (hD.enorm.pow_const 2).lintegral_prod_left' K hK hcover hfin
  filter_upwards [hD.prodMk_right, hfinite] with x hx hxf
  exact memLp_two_of_lintegral_dual_energy_ne_top ν hx hxf

/-- Euclidean closed balls provide the countable exhaustion, so finite local
energies on closed balls directly give the source's conditional L² property. -/
theorem gradient_memLp_two_ae_of_closedBall_energy [SFinite ν]
    (g : Y → ParameterSpace p → ℝ)
    (hD : AEStronglyMeasurable
      (fun z : Y × ParameterSpace p => fderiv ℝ (g z.1) z.2) (ν.prod volume))
    (hfin : ∀ n : ℕ, (∫⁻ x in Metric.closedBall (0 : ParameterSpace p) (n : ℝ),
      (∫⁻ y, ‖fderiv ℝ (g y) x‖ₑ ^ (2 : ℕ) ∂ν)) ≠ ∞) :
    ∀ᵐ x ∂(volume : Measure (ParameterSpace p)),
      MemLp (fun y => fderiv ℝ (g y) x) 2 ν := by
  apply gradient_memLp_two_ae_of_local_energy ν g hD
    (fun n => Metric.closedBall 0 (n : ℝ)) (fun _ => Metric.isClosed_closedBall.measurableSet) _ hfin
  intro x
  obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
  exact ⟨n, by simpa only [Metric.mem_closedBall, dist_zero_right] using hn.le⟩

/-- Joint product energy measurability follows directly from joint likelihood
and gradient measurability and the actual prior's weak H¹ representatives. -/
theorem weakProductDerivative_energy_aemeasurable
    (h : WeakH1Root p) (g : Y → ParameterSpace p → ℝ)
    (hG : AEStronglyMeasurable (fun z : Y × ParameterSpace p => g z.1 z.2)
      (ν.prod volume))
    (hD : AEStronglyMeasurable
      (fun z : Y × ParameterSpace p => fderiv ℝ (g z.1) z.2) (ν.prod volume)) :
    AEMeasurable
      (fun z : Y × ParameterSpace p => ‖weakProductDerivative h (g z.1) z.2‖ₑ ^ (2 : ℕ))
      (ν.prod volume) := by
  exact ((hG.smul h.derivative_aestronglyMeasurable.comp_snd).add
    (h.root_aestronglyMeasurable.comp_snd.smul hD)).enorm.pow_const 2

/-- The actual likelihood Fisher trace averaged against the prior density. -/
def dataInformation (h : WeakH1Root p) (g : Y → ParameterSpace p → ℝ) : ℝ≥0∞ :=
  4 * ∫⁻ x, ENNReal.ofReal (h.root x ^ 2) *
    (∫⁻ y, ‖fderiv ℝ (g y) x‖ₑ ^ (2 : ℕ) ∂ν)

/-- The actual Bayes posterior as a compactly supported weak H¹ root. The
classical product rule supplies membership, and `bayesRoot` proves scaling
internally. The exceptional non-locally-Lipschitz outcomes receive zero. -/
def bayesPosterior (P : WeakLocallyLipschitzProductInput p)
    (h : WeakH1Root p) (g : Y → ParameterSpace p → ℝ) (y : Y) : WeakH1Root p :=
  bayesRoot (weakProductRoot P h (g y))

omit [MeasurableSpace Y] in
/-- At every regular outcome the posterior root is exactly the Bayes
square-root formula with the genuine likelihood marginal. -/
theorem bayesPosterior_root (P : WeakLocallyLipschitzProductInput p)
    (h : WeakH1Root p) (g : Y → ParameterSpace p → ℝ) {y : Y}
    (hy : LocallyLipschitz (g y)) (x : ParameterSpace p) :
    (bayesPosterior P h g y).root x =
      (Real.sqrt (marginal h g y).toReal)⁻¹ * (h.root x * g y x) := by
  have hm : marginal h g y = (weakProductRoot P h (g y)).mass univ := by
    unfold marginal WeakH1Root.mass
    rw [Measure.restrict_univ]
    exact lintegral_congr (fun t => by rw [weakProductRoot_root P h (g y) hy t])
  simp only [bayesPosterior, bayesRoot, scaleRoot_root, weakProductRoot_root P h (g y) hy, hm]

omit [MeasurableSpace Y] in
/-- Every regular positive-marginal outcome has a normalized compactly
supported weak H¹ posterior. Zero marginals have zero weight in the information
identity below. -/
theorem bayesPosterior_normalized (P : WeakLocallyLipschitzProductInput p)
    (h : WeakH1Root p) (g : Y → ParameterSpace p → ℝ) {y : Y}
    (hy : LocallyLipschitz (g y)) (hm : marginal h g y ≠ 0) :
    (bayesPosterior P h g y).mass univ = 1 := by
  have he : marginal h g y = (weakProductRoot P h (g y)).mass univ := by
    unfold marginal WeakH1Root.mass
    rw [Measure.restrict_univ]
    exact lintegral_congr (fun t => by rw [weakProductRoot_root P h (g y) hy t])
  exact bayesRoot_normalized _ (he ▸ hm)

omit [MeasurableSpace Y] in
/-- Marginal weighting removes the genuine Bayes normalizer at any regular
outcome, including zero-likelihood marginals. -/
theorem marginal_mul_bayesPosterior_fisher
    (P : WeakLocallyLipschitzProductInput p) (U : WeakDerivativeUniquenessInput p)
    (h : WeakH1Root p) (g : Y → ParameterSpace p → ℝ) {y : Y}
    (hy : LocallyLipschitz (g y)) :
    marginal h g y * (bayesPosterior P h g y).fisher =
      4 * ∫⁻ x, ‖weakProductDerivative h (g y) x‖ₑ ^ (2 : ℕ) := by
  have hm : marginal h g y = (weakProductRoot P h (g y)).mass univ := by
    unfold marginal WeakH1Root.mass
    rw [Measure.restrict_univ]
    exact lintegral_congr (fun x => by rw [weakProductRoot_root P h (g y) hy x])
  rw [hm, bayesPosterior, marginal_mul_bayesRoot_fisher U]
  unfold WeakH1Root.fisher WeakH1Root.energy
  congr 1
  exact lintegral_congr (fun x => by rw [weakProductRoot_derivative P h (g y) hy x])

/-- The actual marginal-weighted posterior Fisher function is measurable. This
is a consequence of likelihood energy measurability and the proved Bayes
cancellation, rather than a separate posterior regularity input. -/
theorem weightedPosteriorFisher_aemeasurable
    (P : WeakLocallyLipschitzProductInput p) (U : WeakDerivativeUniquenessInput p)
    (h : WeakH1Root p) (g : Y → ParameterSpace p → ℝ)
    (hLL : ∀ᵐ y ∂ν, LocallyLipschitz (g y))
    (hjoint : AEMeasurable
      (fun z : Y × ParameterSpace p => ‖weakProductDerivative h (g z.1) z.2‖ₑ ^ (2 : ℕ))
      (ν.prod volume)) :
    AEMeasurable (fun y => marginal h g y * (bayesPosterior P h g y).fisher) ν := by
  apply ((aemeasurable_const.mul hjoint.lintegral_prod_right') : AEMeasurable
    (fun y => 4 * ∫⁻ x, ‖weakProductDerivative h (g y) x‖ₑ ^ (2 : ℕ)) ν).congr
  filter_upwards [hLL] with y hy
  exact (marginal_mul_bayesPosterior_fisher P U h g hy).symm

/-- Lemma 3.2 for the explicit dominated regularity conditions below.

The classical inputs are only a likelihood-independent weak Leibniz rule and
weak-derivative uniqueness. Normalization, a.e. local Lipschitz regularity,
coordinate L² integrability, score integrability and actual differentiation
under the outcome integral are separate experiment hypotheses. Joint energy
measurability and `SFinite ν` are explicit Tonelli conditions. The final
information identity is proved, never included in an input field. -/
theorem bayes_information_identity [SFinite ν]
    (P : WeakLocallyLipschitzProductInput p) (U : WeakDerivativeUniquenessInput p)
    (h : WeakH1Root p) (g : Y → ParameterSpace p → ℝ)
    (hLL : ∀ᵐ y ∂ν, LocallyLipschitz (g y))
    (hjoint : AEMeasurable
      (fun z : Y × ParameterSpace p => ‖weakProductDerivative h (g z.1) z.2‖ₑ ^ (2 : ℕ))
      (ν.prod volume))
    (hn : ∀ x, (∫ y, g y x ^ 2 ∂ν) = 1)
    (hG : ∀ᵐ x ∂(volume : Measure (ParameterSpace p)), MemLp (fun y => g y x) 2 ν)
    (hD : ∀ᵐ x ∂(volume : Measure (ParameterSpace p)), ∀ i : Fin p,
      MemLp (fun y => fderiv ℝ (g y) x (EuclideanSpace.basisFun (Fin p) ℝ i)) 2 ν)
    (hscore : ∀ᵐ x ∂(volume : Measure (ParameterSpace p)),
      Integrable (fun y => (2 * g y x) • fderiv ℝ (g y) x) ν)
    (hdiff : ∀ᵐ x ∂(volume : Measure (ParameterSpace p)),
      HasFDerivAt (fun t => ∫ y, g y t ^ 2 ∂ν)
        (∫ y, (2 * g y x) • fderiv ℝ (g y) x ∂ν) x) :
    (∫⁻ y, marginal h g y * (bayesPosterior P h g y).fisher ∂ν) =
      h.fisher + dataInformation ν h g := by
  have hcancel : ∀ᵐ y ∂ν, marginal h g y * (bayesPosterior P h g y).fisher =
      4 * ∫⁻ x, ‖weakProductDerivative h (g y) x‖ₑ ^ (2 : ℕ) := by
    exact hLL.mono (fun _ hy => marginal_mul_bayesPosterior_fisher P U h g hy)
  have hpoint : ∀ᵐ x ∂(volume : Measure (ParameterSpace p)),
      (∫⁻ y, ‖weakProductDerivative h (g y) x‖ₑ ^ (2 : ℕ) ∂ν) =
        ‖h.weakDerivative x‖ₑ ^ (2 : ℕ) + ENNReal.ofReal (h.root x ^ 2) *
          (∫⁻ y, ‖fderiv ℝ (g y) x‖ₑ ^ (2 : ℕ) ∂ν) := by
    filter_upwards [hG, hD, hscore, hdiff] with x hxG hxD hxS hxDiff
    exact conditional_product_energy_lintegral ν (fun y => g y x)
      (fun y => fderiv ℝ (g y) x) hxG hxD (hn x)
      (fun i => score_coordinate_zero ν g hn _ hxS hxDiff i) _ _
  calc
    (∫⁻ y, marginal h g y * (bayesPosterior P h g y).fisher ∂ν) =
        ∫⁻ y, 4 * (∫⁻ x, ‖weakProductDerivative h (g y) x‖ₑ ^ (2 : ℕ)) ∂ν :=
      lintegral_congr_ae hcancel
    _ = 4 * (∫⁻ y, (∫⁻ x, ‖weakProductDerivative h (g y) x‖ₑ ^ (2 : ℕ)) ∂ν) :=
      lintegral_const_mul'' _ hjoint.lintegral_prod_right'
    _ = 4 * (∫⁻ x, ∫⁻ y, ‖weakProductDerivative h (g y) x‖ₑ ^ (2 : ℕ) ∂ν) := by
      rw [lintegral_lintegral_swap hjoint]
    _ = 4 * (∫⁻ x, ‖h.weakDerivative x‖ₑ ^ (2 : ℕ) +
        ENNReal.ofReal (h.root x ^ 2) *
          (∫⁻ y, ‖fderiv ℝ (g y) x‖ₑ ^ (2 : ℕ) ∂ν)) := by
      congr 1
      exact lintegral_congr_ae hpoint
    _ = h.fisher + dataInformation ν h g := by
      rw [lintegral_add_left' (h.derivative_aestronglyMeasurable.enorm.pow_const 2)]
      unfold WeakH1Root.fisher WeakH1Root.energy dataInformation
      rw [mul_add]

/-- The source's measurable normalized likelihoods and locally integrable
squared gradient energy supply all conditional L² and score-integrability
hypotheses of the information identity.

The explicit joint measurability hypotheses refer only to the original
likelihood roots and their parameter derivatives. They do not contain a Bayes
posterior or information-identity conclusion. `K` may be any countable
measurable exhaustion on which the local energy is finite. -/
theorem bayes_information_identity_of_local_energy [SFinite ν]
    (P : WeakLocallyLipschitzProductInput p) (U : WeakDerivativeUniquenessInput p)
    (h : WeakH1Root p) (g : Y → ParameterSpace p → ℝ)
    (hLL : ∀ᵐ y ∂ν, LocallyLipschitz (g y))
    (hg : ∀ x, AEStronglyMeasurable (fun y => g y x) ν)
    (hGjoint : AEStronglyMeasurable (fun z : Y × ParameterSpace p => g z.1 z.2)
      (ν.prod volume))
    (hDjoint : AEStronglyMeasurable
      (fun z : Y × ParameterSpace p => fderiv ℝ (g z.1) z.2) (ν.prod volume))
    (hn : ∀ x, (∫⁻ y, ENNReal.ofReal (g y x ^ 2) ∂ν) = 1)
    (K : ℕ → Set (ParameterSpace p)) (hK : ∀ n, MeasurableSet (K n))
    (hcover : ∀ x, ∃ n, x ∈ K n)
    (hfin : ∀ n, (∫⁻ x in K n,
      (∫⁻ y, ‖fderiv ℝ (g y) x‖ₑ ^ (2 : ℕ) ∂ν)) ≠ ∞)
    (hdiff : ∀ᵐ x ∂(volume : Measure (ParameterSpace p)),
      HasFDerivAt (fun t => ∫ y, g y t ^ 2 ∂ν)
        (∫ y, (2 * g y x) • fderiv ℝ (g y) x ∂ν) x) :
    (∫⁻ y, marginal h g y * (bayesPosterior P h g y).fisher ∂ν) =
      h.fisher + dataInformation ν h g := by
  have hG : ∀ x, MemLp (fun y => g y x) 2 ν := by
    intro x
    exact memLp_two_of_lintegral_sq_ne_top ν (hg x) (by rw [hn x]; simp)
  have hnreal : ∀ x, (∫ y, g y x ^ 2 ∂ν) = 1 := by
    intro x
    apply (ENNReal.ofReal_eq_ofReal_iff
      (integral_nonneg (fun _ => sq_nonneg _)) (by norm_num : (0 : ℝ) ≤ 1)).1
    rw [ofReal_integral_eq_lintegral_ofReal (hG x).integrable_sq
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _)), hn x, ENNReal.ofReal_one]
  have hD := gradient_memLp_two_ae_of_local_energy ν g hDjoint K hK hcover hfin
  apply bayes_information_identity ν P U h g hLL
    (weakProductDerivative_energy_aemeasurable ν h g hGjoint hDjoint) hnreal
    (Filter.Eventually.of_forall hG) _ _ hdiff
  · exact hD.mono (fun _ hx i => coordinate_memLp_two ν hx i)
  · exact hD.mono (fun x hx => score_integrable_of_memLp_two ν (hG x) hx)

end Outcome
end Paper26.WeakPosteriorIdentity
