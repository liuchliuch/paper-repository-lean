import BoundaryReduction.GaussianEntropy
import Mathlib.MeasureTheory.Integral.Prod

open Real Set MeasureTheory ProbabilityTheory
open scoped Classical NNReal
namespace BoundaryReduction.Gaussian

variable {d : ℕ} {Γ : Set (Space d)} [CompactSpace Γ]
variable (K : Space d →L[ℝ] Space d)
variable (Z : Measure (Space d)) [IsGaussian Z]

/-- The scalar linear form whose Gaussian MGF yields the likelihood normalizer. -/
noncomputable def precisionForm (v : Space d) : StrongDual ℝ (Space d) :=
  (innerSL ℝ v).comp K

lemma precisionForm_apply (v x : Space d) : precisionForm K v x = inner ℝ v (K x) := rfl

variable (hcenter : (∫ x, x ∂Z) = 0)
variable (hvariance : ∀ v : Space d,
  variance (precisionForm K v) Z = inner ℝ v (K v))

include hcenter hvariance

lemma precision_mgf (v : Space d) :
    mgf (precisionForm K v) Z 1 = exp (inner ℝ v (K v)/2) := by
  have hm : (∫ x, precisionForm K v x ∂Z) = 0 := by
    rw [IsGaussian.integral_dual, hcenter, map_zero]
  have h := mgf_gaussianReal (IsGaussian.map_eq_gaussianReal (μ := Z) (precisionForm K v)) 1
  rw [hm] at h
  have hq : 0 ≤ inner ℝ v (K v) := by rw [← hvariance]; exact variance_nonneg _ _
  simpa [Real.coe_toNNReal, hvariance, max_eq_left hq] using h

lemma integrable_component (r : Γ) : Integrable (fun x => exp (exponent K r x)) Z := by
  have hm := precision_mgf K Z hcenter hvariance (r : Space d)
  have hi : Integrable (fun x => exp (precisionForm K (r : Space d) x)) Z := by
    have hp : 0 < mgf (precisionForm K (r : Space d)) Z 1 := by rw [hm]; exact exp_pos _
    simpa using mgf_pos_iff.mp hp
  have hh := hi.div_const (exp (inner ℝ (r : Space d) (K (r : Space d))/2))
  simpa only [exponent, exp_sub, precisionForm_apply] using hh

lemma integral_component (r : Γ) : (∫ x, exp (exponent K r x) ∂Z) = 1 := by
  have hm := precision_mgf K Z hcenter hvariance (r : Space d)
  simp only [mgf, one_mul] at hm
  simp only [exponent, exp_sub, div_eq_mul_inv]
  rw [integral_mul_const]
  change (∫ x, exp (precisionForm K (r : Space d) x) ∂Z) * _ = 1
  rw [hm]
  simp only [div_eq_mul_inv]
  exact mul_inv_cancel₀ (exp_pos _).ne'

variable (W : Measure Γ) [IsProbabilityMeasure W]

lemma integrable_joint_likelihood :
    Integrable (fun p : Γ × Space d => exp (exponent K p.1 p.2)) (W.prod Z) := by
  have hc : Continuous (fun p : Γ × Space d => exp (exponent K p.1 p.2)) := by
    unfold exponent
    fun_prop
  apply (integrable_prod_iff hc.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun r => integrable_component K Z hcenter hvariance r)
  · have heq : (fun r : Γ => ∫ x, ‖exp (exponent K r x)‖ ∂Z) = fun _ => (1:ℝ) := by
      ext r
      simp only [Real.norm_eq_abs, abs_of_pos (exp_pos _), integral_component K Z hcenter hvariance]
    rw [heq]
    exact integrable_const _

lemma integrable_likelihood : Integrable (likelihood K W) Z :=
  (integrable_joint_likelihood K Z hcenter hvariance W).integral_prod_right

/-- The actual compact Gaussian mixture likelihood has null expectation one. -/
theorem integral_likelihood : (∫ x, likelihood K W x ∂Z) = 1 := by
  have h := integral_integral_swap (f := fun r : Γ => fun x : Space d => exp (exponent K r x))
    (μ := W) (ν := Z) (integrable_joint_likelihood K Z hcenter hvariance W)
  have hleft : (∫ r : Γ, ∫ x, exp (exponent K r x) ∂Z ∂W) = 1 := by
    simp only [integral_component K Z hcenter hvariance]
    simp
  exact h.symm.trans hleft

/-- The value at the null mean in (4.18), derived from the normalized likelihood. -/
theorem expectedLog_zero_nonpos (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R) :
    expectedLog K W Z 0 ≤ 0 := by
  have hi : Integrable (phi K W) Z := by simpa using integrable_phi_shift K W Z R hR 0
  have hL := integrable_likelihood K Z hcenter hvariance W
  have hpt : ∀ x : Space d, phi K W x ≤ likelihood K W x-1 :=
    fun x => log_le_sub_one_of_pos (likelihood_pos K W x)
  have h := integral_mono hi (hL.sub (integrable_const 1)) hpt
  simp only [Pi.sub_apply] at h
  rw [integral_sub hL (integrable_const 1), integral_likelihood K Z hcenter hvariance W] at h
  simpa [expectedLog] using h

end BoundaryReduction.Gaussian
