import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Finite smooth posterior-information identity

This module proves the actual derivative and integral identities behind
Lemma 3.2 for finitely many differentiable square-root likelihoods. It does
not assert the H¹ extension, continuous outcomes, or quantum likelihood
regularity. Normalization is differentiated; the zero cross term is proved,
not supplied as a hypothesis.
-/
noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Paper26.PosteriorIdentity

variable {E Y I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Fintype Y] [Fintype I]

/-- Differentiating likelihood normalization gives its zero score identity
in every actual tangent direction. -/
theorem normalized_root_derivative_zero
    (g : Y → E → ℝ) {x : E}
    (hg : ∀ y, DifferentiableAt ℝ (g y) x)
    (hn : ∀ z, ∑ y, (g y z) ^ 2 = 1) (v : E) :
    ∑ y, g y x * fderiv ℝ (g y) x v = 0 := by
  have he : (fun z => ∑ y, g y z * g y z) = (fun _ : E => (1 : ℝ)) := by
    funext z
    simpa only [pow_two] using hn z
  have hd : fderiv ℝ (fun z => ∑ y, g y z * g y z) x = 0 := by
    rw [he]
    simp
  rw [fderiv_fun_sum (u := Finset.univ)
    (A := fun y z => g y z * g y z) (fun y _ => (hg y).mul (hg y))] at hd
  have hv := congrArg (fun L : E →L[ℝ] ℝ => L v) hd
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.zero_apply] at hv
  simp_rw [fderiv_fun_mul (hg _) (hg _), ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul] at hv
  have htwice : (∑ y, (g y x * fderiv ℝ (g y) x v +
      g y x * fderiv ℝ (g y) x v)) =
      2 * (∑ y, g y x * fderiv ℝ (g y) x v) := by
    rw [Finset.sum_add_distrib]
    ring
  rw [htwice] at hv
  linarith

/-- Product rule plus differentiated normalization, in one tangent direction. -/
theorem product_direction_energy
    (h : E → ℝ) (g : Y → E → ℝ) {x : E}
    (hh : DifferentiableAt ℝ h x)
    (hg : ∀ y, DifferentiableAt ℝ (g y) x)
    (hn : ∀ z, ∑ y, (g y z) ^ 2 = 1) (v : E) :
    (∑ y, (fderiv ℝ (fun z => h z * g y z) x v) ^ 2) =
      (fderiv ℝ h x v) ^ 2 +
        (h x) ^ 2 * (∑ y, (fderiv ℝ (g y) x v) ^ 2) := by
  have hz := normalized_root_derivative_zero g hg hn v
  have hp : ∀ y, (fderiv ℝ (fun z => h z * g y z) x v) ^ 2 =
      (g y x) ^ 2 * (fderiv ℝ h x v) ^ 2 +
      (h x) ^ 2 * (fderiv ℝ (g y) x v) ^ 2 +
      (2 * h x * fderiv ℝ h x v) *
        (g y x * fderiv ℝ (g y) x v) := by
    intro y
    rw [fderiv_fun_mul hh (hg y)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    ring
  simp_rw [hp]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, ← Finset.mul_sum, hn x, hz]
  ring

/-- Squared gradient energy expressed in a finite list of genuine tangent
coordinates. Choosing the Euclidean orthonormal basis gives the usual
Euclidean gradient energy. -/
def coordinateEnergy (v : I → E) (h : E → ℝ) (x : E) : ℝ :=
  ∑ i, (fderiv ℝ h x (v i)) ^ 2

/-- Pointwise finite-coordinate form of the posterior energy identity. -/
theorem product_coordinate_energy
    (v : I → E) (h : E → ℝ) (g : Y → E → ℝ) {x : E}
    (hh : DifferentiableAt ℝ h x)
    (hg : ∀ y, DifferentiableAt ℝ (g y) x)
    (hn : ∀ z, ∑ y, (g y z) ^ 2 = 1) :
    (∑ y, coordinateEnergy v (fun z => h z * g y z) x) =
      coordinateEnergy v h x + (h x) ^ 2 *
        (∑ y, coordinateEnergy v (g y) x) := by
  unfold coordinateEnergy
  rw [Finset.sum_comm]
  simp_rw [product_direction_energy h g hh hg hn]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]

/-- The normalized likelihoods give the integral identity when the two energy
terms are integrable. The derivative identity is used before integration. -/
theorem integral_product_coordinate_energy
    [MeasurableSpace E] (μ : Measure E) (v : I → E)
    (h : E → ℝ) (g : Y → E → ℝ)
    (hh : Differentiable ℝ h) (hg : ∀ y, Differentiable ℝ (g y))
    (hn : ∀ z, ∑ y, (g y z) ^ 2 = 1)
    (hi : Integrable (coordinateEnergy v h) μ)
    (hj : Integrable (fun x => (h x) ^ 2 *
      (∑ y, coordinateEnergy v (g y) x)) μ) :
    (∫ x, ∑ y, coordinateEnergy v (fun z => h z * g y z) x ∂μ) =
      (∫ x, coordinateEnergy v h x ∂μ) +
        ∫ x, (h x) ^ 2 * (∑ y, coordinateEnergy v (g y) x) ∂μ := by
  have he : (fun x => ∑ y, coordinateEnergy v (fun z => h z * g y z) x) =
      (fun x => coordinateEnergy v h x +
        (h x) ^ 2 * (∑ y, coordinateEnergy v (g y) x)) := by
    funext x
    exact product_coordinate_energy v h g (hh x) (fun y => hg y x) hn
  rw [he, integral_add hi hj]

/-- Euclidean coordinate gradient, obtained by evaluating the Fréchet
 derivative on the standard orthonormal coordinate vectors. -/
def coordinateGradient {p : ℕ} (h : EuclideanSpace ℝ (Fin p) → ℝ)
    (x : EuclideanSpace ℝ (Fin p)) : EuclideanSpace ℝ (Fin p) :=
  WithLp.toLp 2 (fun i => fderiv ℝ h x (EuclideanSpace.basisFun (Fin p) ℝ i))

theorem coordinateGradient_norm_sq {p : ℕ}
    (h : EuclideanSpace ℝ (Fin p) → ℝ) (x : EuclideanSpace ℝ (Fin p)) :
    ‖coordinateGradient h x‖ ^ 2 =
      coordinateEnergy (EuclideanSpace.basisFun (Fin p) ℝ) h x := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [coordinateGradient, coordinateEnergy, Real.norm_eq_abs, sq_abs]
  rfl

/-- The actual pointwise Euclidean squared-gradient identity for finite
outcomes. Only differentiability is required, so C¹ likelihoods are covered. -/
theorem product_gradient_energy {p : ℕ}
    (h : EuclideanSpace ℝ (Fin p) → ℝ)
    (g : Y → EuclideanSpace ℝ (Fin p) → ℝ)
    {x : EuclideanSpace ℝ (Fin p)}
    (hh : DifferentiableAt ℝ h x)
    (hg : ∀ y, DifferentiableAt ℝ (g y) x)
    (hn : ∀ z, ∑ y, (g y z) ^ 2 = 1) :
    (∑ y, ‖coordinateGradient (fun z => h z * g y z) x‖ ^ 2) =
      ‖coordinateGradient h x‖ ^ 2 + (h x) ^ 2 *
        (∑ y, ‖coordinateGradient (g y) x‖ ^ 2) := by
  simp_rw [coordinateGradient_norm_sq]
  exact product_coordinate_energy _ h g hh hg hn


/-- A constant rescaling has its actual squared effect on derivative energy. -/
theorem coordinateEnergy_const_mul (v : I → E) (c : ℝ) (h : E → ℝ)
    {x : E} (hh : DifferentiableAt ℝ h x) :
    coordinateEnergy v (fun z => c * h z) x = c ^ 2 * coordinateEnergy v h x := by
  unfold coordinateEnergy
  simp_rw [fderiv_const_mul hh c, ContinuousLinearMap.smul_apply,
    smul_eq_mul, mul_pow]
  rw [Finset.mul_sum]

/-- Finite-outcome version with the outcome sum outside the integral. -/
theorem sum_integral_product_coordinate_energy
    [MeasurableSpace E] (μ : Measure E) (v : I → E)
    (h : E → ℝ) (g : Y → E → ℝ)
    (hh : Differentiable ℝ h) (hg : ∀ y, Differentiable ℝ (g y))
    (hn : ∀ z, ∑ y, (g y z) ^ 2 = 1)
    (hi : Integrable (coordinateEnergy v h) μ)
    (hj : Integrable (fun x => (h x) ^ 2 *
      (∑ y, coordinateEnergy v (g y) x)) μ)
    (hk : ∀ y, Integrable (coordinateEnergy v (fun z => h z * g y z)) μ) :
    (∑ y, ∫ x, coordinateEnergy v (fun z => h z * g y z) x ∂μ) =
      (∫ x, coordinateEnergy v h x ∂μ) +
        ∫ x, (h x) ^ 2 * (∑ y, coordinateEnergy v (g y) x) ∂μ := by
  rw [← integral_finset_sum Finset.univ (fun y _ => hk y)]
  exact integral_product_coordinate_energy μ v h g hh hg hn hi hj

/-- Fisher energy of a genuine root function, in the chosen finite tangent
coordinates. Euclidean orthonormal coordinates give four times the integral
of the squared Euclidean gradient. -/
def rootFisher [MeasurableSpace E] (μ : Measure E) (v : I → E) (h : E → ℝ) : ℝ :=
  4 * ∫ x, coordinateEnergy v h x ∂μ

/-- Trace Fisher information of the finite likelihood family `g_y²`. -/
def likelihoodFisherTrace (v : I → E) (g : Y → E → ℝ) (x : E) : ℝ :=
  4 * ∑ y, coordinateEnergy v (g y) x

/-- The information identity before posterior normalization. -/
theorem sum_product_rootFisher
    [MeasurableSpace E] (μ : Measure E) (v : I → E)
    (h : E → ℝ) (g : Y → E → ℝ)
    (hh : Differentiable ℝ h) (hg : ∀ y, Differentiable ℝ (g y))
    (hn : ∀ z, ∑ y, (g y z) ^ 2 = 1)
    (hi : Integrable (coordinateEnergy v h) μ)
    (hj : Integrable (fun x => (h x) ^ 2 *
      (∑ y, coordinateEnergy v (g y) x)) μ)
    (hk : ∀ y, Integrable (coordinateEnergy v (fun z => h z * g y z)) μ) :
    (∑ y, rootFisher μ v (fun z => h z * g y z)) =
      rootFisher μ v h + ∫ x, (h x) ^ 2 * likelihoodFisherTrace v g x ∂μ := by
  unfold rootFisher likelihoodFisherTrace
  rw [← Finset.mul_sum,
    sum_integral_product_coordinate_energy μ v h g hh hg hn hi hj hk]
  have he : (fun x => (h x) ^ 2 * (4 * ∑ y, coordinateEnergy v (g y) x)) =
      (fun x => 4 * ((h x) ^ 2 * ∑ y, coordinateEnergy v (g y) x)) := by
    funext x
    ring
  rw [he, integral_const_mul]
  ring

/-- Actual marginal probability, obtained by integrating prior times
likelihood, rather than an abstract weight supplied to the identity. -/
def marginal [MeasurableSpace E] (μ : Measure E) (h g : E → ℝ) : ℝ :=
  ∫ x, (h x * g x) ^ 2 ∂μ

/-- The square root of the actual posterior density for a positive-marginal
outcome. Nonnegative prior/likelihood roots make this root nonnegative. -/
def posteriorRoot [MeasurableSpace E] (μ : Measure E) (h g : E → ℝ) : E → ℝ :=
  fun x => (Real.sqrt (marginal μ h g))⁻¹ * (h x * g x)

/-- The actual finite marginals sum to one for a normalized prior root. -/
theorem sum_marginal
    [MeasurableSpace E] (μ : Measure E) (h : E → ℝ) (g : Y → E → ℝ)
    (hn : ∀ z, ∑ y, (g y z) ^ 2 = 1)
    (hprior : (∫ x, (h x) ^ 2 ∂μ) = 1)
    (hi : ∀ y, Integrable (fun x => (h x * g y x) ^ 2) μ) :
    (∑ y, marginal μ h (g y)) = 1 := by
  unfold marginal
  rw [← integral_finset_sum Finset.univ (fun y _ => hi y)]
  have he : (fun x => ∑ y, (h x * g y x) ^ 2) = (fun x => (h x) ^ 2) := by
    funext x
    simp_rw [mul_pow]
    rw [← Finset.mul_sum, hn x, mul_one]
  rw [he, hprior]

/-- Each included positive-marginal outcome has a normalized posterior. -/
theorem posteriorRoot_normalized
    [MeasurableSpace E] (μ : Measure E) (h g : E → ℝ)
    (hm : 0 < marginal μ h g) :
    (∫ x, (posteriorRoot μ h g x) ^ 2 ∂μ) = 1 := by
  unfold posteriorRoot
  have he : ∀ x, ((Real.sqrt (marginal μ h g))⁻¹ * (h x * g x)) ^ 2 =
      (Real.sqrt (marginal μ h g))⁻¹ ^ 2 * (h x * g x) ^ 2 := by
    intro x
    rw [mul_pow]
  simp_rw [he]
  rw [integral_const_mul, inv_pow, Real.sq_sqrt hm.le]
  exact inv_mul_cancel₀ hm.ne'

/-- Normalizing a positive-marginal posterior and multiplying by its marginal
recovers precisely the unnormalized energy. -/
theorem marginal_mul_posterior_rootFisher
    [MeasurableSpace E] (μ : Measure E) (v : I → E)
    (h g : E → ℝ) (hh : Differentiable ℝ h) (hg : Differentiable ℝ g)
    (hm : 0 < marginal μ h g) :
    marginal μ h g * rootFisher μ v (posteriorRoot μ h g) =
      rootFisher μ v (fun x => h x * g x) := by
  have he : marginal μ h g * (Real.sqrt (marginal μ h g))⁻¹ ^ 2 = 1 := by
    rw [inv_pow, Real.sq_sqrt hm.le]
    exact mul_inv_cancel₀ hm.ne'
  unfold rootFisher posteriorRoot
  simp_rw [coordinateEnergy_const_mul v _ (fun x => h x * g x)
    ((hh _).mul (hg _))]
  rw [integral_const_mul]
  calc
    _ = (marginal μ h g * (Real.sqrt (marginal μ h g))⁻¹ ^ 2) *
        (4 * ∫ x, coordinateEnergy v (fun x => h x * g x) x ∂μ) := by ring
    _ = _ := by rw [he, one_mul]

/-- Lemma 3.2 for a finite differentiable experiment whose included outcomes
have positive marginal probability. The posterior and weights are defined by
the actual Bayes formula. General H¹ roots, continuous outcome spaces and the
removal of zero-marginal outcomes are outside this theorem's stated scope. -/
theorem finite_positive_posterior_information_identity
    [MeasurableSpace E] (μ : Measure E) (v : I → E)
    (h : E → ℝ) (g : Y → E → ℝ)
    (hh : Differentiable ℝ h) (hg : ∀ y, Differentiable ℝ (g y))
    (hn : ∀ z, ∑ y, (g y z) ^ 2 = 1)
    (hm : ∀ y, 0 < marginal μ h (g y))
    (hi : Integrable (coordinateEnergy v h) μ)
    (hj : Integrable (fun x => (h x) ^ 2 *
      (∑ y, coordinateEnergy v (g y) x)) μ)
    (hk : ∀ y, Integrable (coordinateEnergy v (fun z => h z * g y z)) μ) :
    (∑ y, marginal μ h (g y) * rootFisher μ v (posteriorRoot μ h (g y))) =
      rootFisher μ v h + ∫ x, (h x) ^ 2 * likelihoodFisherTrace v g x ∂μ := by
  calc
    _ = ∑ y, rootFisher μ v (fun z => h z * g y z) := by
      apply Finset.sum_congr rfl
      intro y _
      exact marginal_mul_posterior_rootFisher μ v h (g y) hh (hg y) (hm y)
    _ = _ := sum_product_rootFisher μ v h g hh hg hn hi hj hk


/-- Nonnegative root functions have zero actual derivative at every zero;
this handles zero-marginal outcomes without a positivity assumption on their
likelihoods. -/
theorem coordinateEnergy_zero_of_nonneg (v : I → E) (f : E → ℝ) {x : E}
    (hf : ∀ z, 0 ≤ f z) (hx : f x = 0) : coordinateEnergy v f x = 0 := by
  have hmin : IsLocalMin f x := by
    apply Filter.Eventually.of_forall
    intro z
    change f x ≤ f z
    rw [hx]
    exact hf z
  have hd := hmin.fderiv_eq_zero
  simp [coordinateEnergy, hd]

/-- An outcome of zero actual marginal probability contributes no
unnormalized Fisher energy. Nonnegativity is the genuine root assumption. -/
theorem zero_marginal_rootFisher
    [MeasurableSpace E] (μ : Measure E) (v : I → E) (h g : E → ℝ)
    (hn : ∀ x, 0 ≤ h x * g x)
    (hi : Integrable (fun x => (h x * g x) ^ 2) μ)
    (hm : marginal μ h g = 0) :
    rootFisher μ v (fun x => h x * g x) = 0 := by
  have hae : (fun x => (h x * g x) ^ 2) =ᵐ[μ] 0 := by
    apply (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (h x * g x)) hi).mp
    exact hm
  have he : coordinateEnergy v (fun x => h x * g x) =ᵐ[μ] 0 := by
    filter_upwards [hae] with x hx
    exact coordinateEnergy_zero_of_nonneg v (fun x => h x * g x) hn
      (sq_eq_zero_iff.mp hx)
  unfold rootFisher
  rw [integral_congr_ae he]
  simp

/-- Bayes normalization cancels marginal weight, including impossible
outcomes. The derivative-zero fact above supplies the nontrivial zero case. -/
theorem marginal_mul_posterior_rootFisher_nonnegative
    [MeasurableSpace E] (μ : Measure E) (v : I → E)
    (h g : E → ℝ) (hh : Differentiable ℝ h) (hg : Differentiable ℝ g)
    (hn : ∀ x, 0 ≤ h x * g x)
    (hi : Integrable (fun x => (h x * g x) ^ 2) μ) :
    marginal μ h g * rootFisher μ v (posteriorRoot μ h g) =
      rootFisher μ v (fun x => h x * g x) := by
  have hm : 0 ≤ marginal μ h g := integral_nonneg (fun x => sq_nonneg _)
  rcases eq_or_lt_of_le hm with he | he
  · have hz : marginal μ h g = 0 := he.symm
    rw [hz, zero_mul, zero_marginal_rootFisher μ v h g hn hi hz]
  · exact marginal_mul_posterior_rootFisher μ v h g hh hg he

/-- Lemma 3.2's actual Bayes/Fisher identity for a finite differentiable
nonnegative-root experiment, including zero-probability outcomes. The
energies and squared roots have the stated integrability assumptions. For
standard Euclidean coordinates this is the finite smooth version of (24).
No H¹ or arbitrary continuous-outcome extension is claimed. -/
theorem finite_posterior_information_identity
    [MeasurableSpace E] (μ : Measure E) (v : I → E)
    (h : E → ℝ) (g : Y → E → ℝ)
    (hh : Differentiable ℝ h) (hg : ∀ y, Differentiable ℝ (g y))
    (hpos : ∀ x, 0 ≤ h x) (gpos : ∀ y x, 0 ≤ g y x)
    (hn : ∀ z, ∑ y, (g y z) ^ 2 = 1)
    (hdensity : ∀ y, Integrable (fun x => (h x * g y x) ^ 2) μ)
    (hi : Integrable (coordinateEnergy v h) μ)
    (hj : Integrable (fun x => (h x) ^ 2 *
      (∑ y, coordinateEnergy v (g y) x)) μ)
    (hk : ∀ y, Integrable (coordinateEnergy v (fun z => h z * g y z)) μ) :
    (∑ y, marginal μ h (g y) * rootFisher μ v (posteriorRoot μ h (g y))) =
      rootFisher μ v h + ∫ x, (h x) ^ 2 * likelihoodFisherTrace v g x ∂μ := by
  calc
    _ = ∑ y, rootFisher μ v (fun z => h z * g y z) := by
      apply Finset.sum_congr rfl
      intro y _
      exact marginal_mul_posterior_rootFisher_nonnegative μ v h (g y) hh (hg y)
        (fun x => mul_nonneg (hpos x) (gpos y x)) (hdensity y)
    _ = _ := sum_product_rootFisher μ v h g hh hg hn hi hj hk


lemma coordinateEnergy_nonneg (v : I → E) (h : E → ℝ) (x : E) :
    0 ≤ coordinateEnergy v h x :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- C¹ roots have continuous energy, providing the measurability needed for
integrability by domination rather than assuming posterior energies. -/
theorem continuous_coordinateEnergy (v : I → E) (h : E → ℝ)
    (hh : ContDiff ℝ 1 h) : Continuous (coordinateEnergy v h) := by
  unfold coordinateEnergy
  apply continuous_finset_sum
  intro i _
  exact ((hh.continuous_fderiv (by norm_num)).clm_apply continuous_const).pow 2

/-- A finite C¹ Euclidean instance of Lemma 3.2. Only the original prior-root
square, prior energy and expected likelihood energy are assumed integrable;
individual posterior-root and posterior-energy integrability are derived.
Zero-marginal outcomes are included. Setting the prior-root square integral
to one additionally makes the actual marginals a probability distribution
by `sum_marginal`.
-/
theorem finite_smooth_posterior_information_identity {p : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin p)))
    (h : EuclideanSpace ℝ (Fin p) → ℝ)
    (g : Y → EuclideanSpace ℝ (Fin p) → ℝ)
    (hh : ContDiff ℝ 1 h) (hg : ∀ y, ContDiff ℝ 1 (g y))
    (hpos : ∀ x, 0 ≤ h x) (gpos : ∀ y x, 0 ≤ g y x)
    (hn : ∀ z, ∑ y, (g y z) ^ 2 = 1)
    (hprior : Integrable (fun x => (h x) ^ 2) μ)
    (hi : Integrable (coordinateEnergy (EuclideanSpace.basisFun (Fin p) ℝ) h) μ)
    (hj : Integrable (fun x => (h x) ^ 2 *
      (∑ y, coordinateEnergy (EuclideanSpace.basisFun (Fin p) ℝ) (g y) x)) μ) :
    (∑ y, marginal μ h (g y) *
      rootFisher μ (EuclideanSpace.basisFun (Fin p) ℝ) (posteriorRoot μ h (g y))) =
      rootFisher μ (EuclideanSpace.basisFun (Fin p) ℝ) h +
        ∫ x, (h x) ^ 2 *
          likelihoodFisherTrace (EuclideanSpace.basisFun (Fin p) ℝ) g x ∂μ := by
  let v := EuclideanSpace.basisFun (Fin p) ℝ
  have hdensity : ∀ y, Integrable (fun x => (h x * g y x) ^ 2) μ := by
    intro y
    apply hprior.mono' ((hh.continuous.mul (hg y).continuous).pow 2).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow]
    have hy : (g y x) ^ 2 ≤ 1 := by
      rw [← hn x]
      exact Finset.single_le_sum (fun z _ => sq_nonneg (g z x)) (Finset.mem_univ y)
    calc
      (h x) ^ 2 * (g y x) ^ 2 ≤ (h x) ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hy (sq_nonneg _)
      _ = (h x) ^ 2 := mul_one _
  have hsum : Integrable
      (fun x => ∑ y, coordinateEnergy v (fun z => h z * g y z) x) μ := by
    apply (hi.add hj).congr
    apply Filter.Eventually.of_forall
    intro x
    exact (product_coordinate_energy v h g (hh.differentiable_one x)
      (fun y => (hg y).differentiable_one x) hn).symm
  have hk : ∀ y, Integrable (coordinateEnergy v (fun z => h z * g y z)) μ := by
    intro y
    apply hsum.mono'
      (continuous_coordinateEnergy v _ (hh.mul (hg y))).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (coordinateEnergy_nonneg _ _ _)]
    exact Finset.single_le_sum
      (fun z _ => coordinateEnergy_nonneg v (fun t => h t * g z t) x)
      (Finset.mem_univ y)
  exact finite_posterior_information_identity μ v h g hh.differentiable_one
    (fun y => (hg y).differentiable_one) hpos gpos hn hdensity hi hj hk


/-- The orthonormal-coordinate energy is exactly the squared operator norm of
 the scalar Fréchet derivative, by the Riesz representation isometry. -/
theorem coordinateEnergy_basis_eq_fderiv_norm_sq {p : ℕ}
    (h : EuclideanSpace ℝ (Fin p) → ℝ) (x : EuclideanSpace ℝ (Fin p)) :
    coordinateEnergy (EuclideanSpace.basisFun (Fin p) ℝ) h x =
      ‖fderiv ℝ h x‖ ^ 2 := by
  have he := (EuclideanSpace.basisFun (Fin p) ℝ).sum_sq_norm_inner_left
    ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin p))).symm (fderiv ℝ h x))
  simpa only [coordinateEnergy, InnerProductSpace.toDual_symm_apply,
    Real.norm_eq_abs, sq_abs, LinearIsometryEquiv.norm_map] using he

/-- Pointwise Euclidean identity directly in scalar Fréchet-derivative norms. -/
theorem product_fderiv_energy {p : ℕ}
    (h : EuclideanSpace ℝ (Fin p) → ℝ)
    (g : Y → EuclideanSpace ℝ (Fin p) → ℝ)
    {x : EuclideanSpace ℝ (Fin p)}
    (hh : DifferentiableAt ℝ h x)
    (hg : ∀ y, DifferentiableAt ℝ (g y) x)
    (hn : ∀ z, ∑ y, (g y z) ^ 2 = 1) :
    (∑ y, ‖fderiv ℝ (fun z => h z * g y z) x‖ ^ 2) =
      ‖fderiv ℝ h x‖ ^ 2 + (h x) ^ 2 * (∑ y, ‖fderiv ℝ (g y) x‖ ^ 2) := by
  have he := product_coordinate_energy (EuclideanSpace.basisFun (Fin p) ℝ) h g hh hg hn
  simpa only [coordinateEnergy_basis_eq_fderiv_norm_sq] using he

end Paper26.PosteriorIdentity
