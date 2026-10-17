import BoundaryReduction.GaussianKL
import Mathlib.Probability.Moments.Tilted
import Mathlib.Probability.Moments.ComplexMGF

open Real Set MeasureTheory ProbabilityTheory
open scoped Classical NNReal ENNReal
namespace BoundaryReduction.Gaussian

variable {d : ℕ}

lemma dual_mgf_unique (P Q : Measure (Space d)) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hmgf : ∀ L : StrongDual ℝ (Space d), mgf L P = mgf L Q)
    (hpos : ∀ (L : StrongDual ℝ (Space d)) (t : ℝ), 0 < mgf L P t) : P = Q := by
  apply Measure.ext_of_charFunDual
  ext L
  have hfull : integrableExpSet L P = Set.univ := by
    ext t
    change Integrable (fun x => exp (t*L x)) P ↔ t ∈ (Set.univ : Set ℝ)
    simp only [Set.mem_univ, iff_true]
    exact mgf_pos_iff.mp (hpos L t)
  have hc := eqOn_complexMGF_of_mgf (hmgf L)
    (show (1*Complex.I : ℂ) ∈ {z : ℂ | z.re ∈ interior (integrableExpSet L P)} by simp [hfull])
  have hp := complexMGF_mul_I (μ := P) L.continuous.measurable.aemeasurable (1:ℝ)
  have hq := complexMGF_mul_I (μ := Q) L.continuous.measurable.aemeasurable (1:ℝ)
  norm_num only [Complex.ofReal_one, one_mul] at hc hp hq
  rw [hp, hq] at hc
  simpa only [charFunDual_eq_charFun_map_one] using hc

variable (K : Space d →L[ℝ] Space d) (Z : Measure (Space d)) [IsGaussian Z]
variable (hcenter : (∫ x, x ∂Z) = 0)
include hcenter

lemma gaussian_dual_mgf (L : StrongDual ℝ (Space d)) (t : ℝ) :
    mgf L Z t = exp (variance L Z*t^2/2) := by
  have hm : (∫ x, L x ∂Z) = 0 := by rw [IsGaussian.integral_dual, hcenter, map_zero]
  have h := mgf_gaussianReal (IsGaussian.map_eq_gaussianReal (μ := Z) L) t
  rw [hm] at h
  simpa [Real.coe_toNNReal, max_eq_left (variance_nonneg _ _)] using h

lemma gaussian_dual_exp_integrable (L : StrongDual ℝ (Space d)) :
    Integrable (fun x => exp (L x)) Z := by
  have hp : 0 < mgf L Z 1 := by rw [gaussian_dual_mgf Z hcenter]; exact exp_pos _
  simpa using mgf_pos_iff.mp hp

variable (hcov : ∀ (L : StrongDual ℝ (Space d)) (v : Space d),
  covariance L (precisionForm K v) Z = L v)
include hcov

lemma precision_variance_of_covariance (v : Space d) :
    variance (precisionForm K v) Z = inner ℝ v (K v) := by
  have h := hcov (precisionForm K v) v
  rw [covariance_self (by fun_prop)] at h
  exact h

lemma mgf_precision_tilt (v : Space d) (L : StrongDual ℝ (Space d)) (t : ℝ) :
    mgf L (Z.tilted (precisionForm K v)) t = exp (variance L Z*t^2/2+t*L v) := by
  have hvar : variance (precisionForm K v+t • L) Z =
      inner ℝ v (K v)+2*t*L v+t^2*variance L Z := by
    have h := variance_add (IsGaussian.memLp_dual Z (precisionForm K v) 2 (by simp))
      (IsGaussian.memLp_dual Z (t • L) 2 (by simp))
    simp only [ContinuousLinearMap.coe_add, ContinuousLinearMap.coe_smul',
      Pi.smul_apply, smul_eq_mul] at h ⊢
    rw [covariance_smul_right, covariance_comm, hcov,
      variance_smul, precision_variance_of_covariance K Z hcenter hcov] at h
    have heq : (⇑(precisionForm K v+t • L) : Space d → ℝ) =
        (precisionForm K v : Space d → ℝ)+t • (L : Space d → ℝ) := by
      ext x
      rfl
    rw [heq]
    nlinarith
  have hm := gaussian_dual_mgf Z hcenter (precisionForm K v+t • L) 1
  have hn := gaussian_dual_mgf Z hcenter (precisionForm K v) 1
  rw [hvar] at hm
  rw [precision_variance_of_covariance K Z hcenter hcov] at hn
  unfold mgf
  rw [integral_exp_tilted]
  have heq : (fun x => exp ((precisionForm K v+fun x => t*L x) x)) =
      fun x => exp ((precisionForm K v+t • L) x) := rfl
  rw [heq]
  simp only [mgf, one_mul] at hm hn
  rw [hm, hn, ← exp_sub]
  congr 1
  ring

lemma mgf_gaussian_shift (v : Space d) (L : StrongDual ℝ (Space d)) (t : ℝ) :
    mgf L (Z.map (fun x => x+v)) t = exp (variance L Z*t^2/2+t*L v) := by
  rw [mgf_map (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def, map_add]
  rw [mgf_add_const, gaussian_dual_mgf Z hcenter, ← exp_add]

/-- The finite-dimensional Gaussian tilt is exactly translation by its mean. -/
theorem gaussian_tilt_eq_shift (v : Space d) :
    Z.tilted (precisionForm K v) = Z.map (fun x => x+v) := by
  letI := isProbabilityMeasure_tilted (gaussian_dual_exp_integrable Z hcenter (precisionForm K v))
  apply dual_mgf_unique
  · intro L
    ext t
    rw [mgf_precision_tilt K Z hcenter hcov, mgf_gaussian_shift K Z hcenter hcov]
  · intro L t
    rw [mgf_precision_tilt K Z hcenter hcov]
    exact exp_pos _

variable {Γ : Set (Space d)} [CompactSpace Γ]
variable (W : Measure Γ) [IsProbabilityMeasure W]

lemma component_integral_as_translation (r : Γ) (g : Space d → ℝ)
    (hg : AEStronglyMeasurable g (Z.map (fun x => x+(r : Space d)))) :
    (∫ z, g (z+(r : Space d)) ∂Z) = ∫ x, exp (exponent K r x)*g x ∂Z := by
  have hm := gaussian_dual_mgf Z hcenter (precisionForm K (r : Space d)) 1
  rw [precision_variance_of_covariance K Z hcenter hcov] at hm
  simp only [mgf, one_mul] at hm
  have hmap := integral_map (by fun_prop : AEMeasurable (fun x : Space d => x+(r : Space d)) Z) hg
  rw [← gaussian_tilt_eq_shift K Z hcenter hcov, integral_tilted] at hmap
  rw [hm] at hmap
  simpa only [smul_eq_mul, exponent, precisionForm_apply, exp_sub, one_pow, mul_one] using hmap.symm

lemma expectedLog_component_identity
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R) (r : Γ) :
    expectedLog K W Z (r : Space d) = ∫ x, exp (exponent K r x)*phi K W x ∂Z := by
  exact component_integral_as_translation K Z hcenter hcov r (phi K W)
    (lipschitz_phi K W R hR).continuous.aestronglyMeasurable

end BoundaryReduction.Gaussian

namespace BoundaryReduction.Gaussian
open MeasureTheory ProbabilityTheory
variable {d : ℕ} (K : Space d →L[ℝ] Space d) (Z : Measure (Space d)) [IsGaussian Z]

lemma precisionForm_add (u v : Space d) :
    precisionForm K (u+v) = precisionForm K u+precisionForm K v := by
  ext x
  simp [precisionForm_apply, inner_add_left]

lemma precision_covariance_of_variance
    (hvariance : ∀ v : Space d, variance (precisionForm K v) Z = inner ℝ v (K v))
    (hsym : ∀ u v : Space d, inner ℝ u (K v) = inner ℝ v (K u)) (u v : Space d) :
    covariance (precisionForm K u) (precisionForm K v) Z = inner ℝ u (K v) := by
  have h := variance_add (IsGaussian.memLp_dual Z (precisionForm K u) 2 (by simp))
    (IsGaussian.memLp_dual Z (precisionForm K v) 2 (by simp))
  have heq : (⇑(precisionForm K (u+v)) : Space d → ℝ) =
      (precisionForm K u : Space d → ℝ)+(precisionForm K v : Space d → ℝ) := by
    ext x
    simp [precisionForm_apply, inner_add_left]
  rw [← heq, hvariance, hvariance, hvariance] at h
  simp only [map_add, inner_add_left, inner_add_right] at h
  have hh := hsym u v
  nlinarith

/-- The inverse covariance identity follows from its quadratic variance form,
symmetry, and invertibility of the precision operator. -/
lemma precision_covariance_identity
    (hvariance : ∀ v : Space d, variance (precisionForm K v) Z = inner ℝ v (K v))
    (hsym : ∀ u v : Space d, inner ℝ u (K v) = inner ℝ v (K u))
    (hsurj : Function.Surjective K) (L : StrongDual ℝ (Space d)) (v : Space d) :
    covariance L (precisionForm K v) Z = L v := by
  obtain ⟨u,hu⟩ := hsurj ((InnerProductSpace.toDual ℝ (Space d)).symm L)
  have hL : precisionForm K u = L := by
    ext x
    rw [precisionForm_apply, hsym, real_inner_comm, hu, InnerProductSpace.toDual_symm_apply]
  rw [← hL]
  exact precision_covariance_of_variance K Z hvariance hsym u v

end BoundaryReduction.Gaussian
