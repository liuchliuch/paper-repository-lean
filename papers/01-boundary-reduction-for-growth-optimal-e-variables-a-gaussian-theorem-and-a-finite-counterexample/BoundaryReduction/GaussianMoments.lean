import BoundaryReduction.GaussianExterior

open Real Set MeasureTheory ProbabilityTheory InformationTheory
open scoped Classical NNReal ENNReal
namespace BoundaryReduction.Gaussian

lemma integral_add_fun {α : Type*} [MeasurableSpace α] {P : Measure α} {f g : α → ℝ}
    (hf : Integrable f P) (hg : Integrable g P) :
    (∫ x, f x+g x ∂P) = (∫ x, f x ∂P)+(∫ x, g x ∂P) := integral_add hf hg

variable {d : ℕ} {Γ : Set (Space d)} [CompactSpace Γ]
variable (K : Space d →L[ℝ] Space d) (Z : Measure (Space d)) [IsGaussian Z]

lemma integrable_joint_norm_sq (W : ProbabilityMeasure Γ)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v)) :
    Integrable (fun p : Γ × Space d => exp (exponent K p.1 p.2)*‖p.2‖^2)
      ((W : Measure Γ).prod Z) := by
  have hb := (gaussian_integrable_exp_norm Z ((R:ℝ)*‖K‖+2)).comp_snd (W : Measure Γ)
  have hc : Continuous (fun p : Γ × Space d => exp (exponent K p.1 p.2)*‖p.2‖^2) := by
    unfold exponent
    fun_prop
  apply hb.mono' hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro p
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hp := (likelihood_envelope K (pointPrior p.1 : Measure Γ) R hR hK p.2).2
  rw [likelihood_point] at hp
  have ht : ‖p.2‖ ≤ exp ‖p.2‖ := by linarith [add_one_le_exp ‖p.2‖]
  have ht2 : ‖p.2‖^2 ≤ (exp ‖p.2‖)^2 := by nlinarith [norm_nonneg p.2, exp_pos ‖p.2‖]
  calc
    _ ≤ exp ((R:ℝ)*‖K‖*‖p.2‖)*(exp ‖p.2‖)^2 :=
      mul_le_mul hp ht2 (sq_nonneg _) (exp_pos _).le
    _ = _ := by
      rw [show ((R:ℝ)*‖K‖+2)*‖p.2‖ = (R:ℝ)*‖K‖*‖p.2‖+(‖p.2‖+‖p.2‖) by ring,
        exp_add, exp_add, pow_two]

variable (hcenter : (∫ x, x ∂Z) = 0)
include hcenter

lemma gaussian_shift_norm_sq (r : Space d) :
    (∫ z, ‖z+r‖^2 ∂Z) = (∫ z, ‖z‖^2 ∂Z)+‖r‖^2 := by
  have hn : Integrable (fun z : Space d => ‖z‖^2) Z :=
    (IsGaussian.memLp_two_fun_id (μ := Z)).integrable_norm_pow (by norm_num)
  have hi : Integrable (fun z : Space d => inner ℝ z r) Z := by
    have h := IsGaussian.integrable_dual Z (innerSL ℝ r)
    simpa only [innerSL_apply, real_inner_comm] using h
  have hz : (∫ z, inner ℝ z r ∂Z) = 0 := by
    have h := IsGaussian.integral_dual (μ := Z) (innerSL ℝ r)
    simpa only [hcenter, map_zero, innerSL_apply, real_inner_comm] using h
  simp_rw [norm_add_sq_real]
  rw [integral_add_fun (f := fun z : Space d => ‖z‖^2+2*inner ℝ z r)
    (g := fun _ => ‖r‖^2) (hn.add (hi.const_mul 2)) (integrable_const _),
    integral_add_fun hn (hi.const_mul 2), integral_const_mul, hz]
  simp

variable (hcov : ∀ (L : StrongDual ℝ (Space d)) (v : Space d), covariance L (precisionForm K v) Z = L v)
include hcov

/-- Gaussian mixture second moments separate a boundary prior from the null. -/
lemma mixture_norm_sq (W : ProbabilityMeasure Γ)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v)) :
    (∫ x, ‖x‖^2 ∂mixtureMeasure K Z W) =
      (∫ z, ‖z‖^2 ∂Z)+(∫ r : Γ, ‖(r : Space d)‖^2 ∂(W : Measure Γ)) := by
  have hmeas : Measurable (fun x => ENNReal.ofReal (likelihood K (W : Measure Γ) x)) :=
    (continuous_likelihood K (W : Measure Γ) R hR).measurable.ennreal_ofReal
  rw [mixtureMeasure, integral_withDensity_eq_integral_toReal_smul hmeas
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (likelihood_pos K (W : Measure Γ) _).le, smul_eq_mul]
  have hs := integral_integral_swap (f := fun r : Γ => fun x : Space d => exp (exponent K r x)*‖x‖^2)
    (integrable_joint_norm_sq K Z W R hR hK)
  have heq : (fun x : Space d => ∫ r : Γ, exp (exponent K r x)*‖x‖^2 ∂(W : Measure Γ)) =
      fun x => likelihood K (W : Measure Γ) x*‖x‖^2 := by
    ext x
    rw [integral_mul_const]
    rfl
  rw [heq] at hs
  rw [← hs]
  have hg : ∀ r : Γ, (∫ x, exp (exponent K r x)*‖x‖^2 ∂Z) =
      (∫ z, ‖z‖^2 ∂Z)+‖(r : Space d)‖^2 := by
    intro r
    rw [← component_integral_as_translation K Z hcenter hcov r (fun x => ‖x‖^2) (by fun_prop),
      gaussian_shift_norm_sq Z hcenter]
  simp_rw [hg]
  have hr : Integrable (fun r : Γ => ‖(r : Space d)‖^2) (W : Measure Γ) := by
    simpa using (continuous_subtype_val.norm.pow 2).continuousOn.integrableOn_compact
      (μ := (W : Measure Γ)) isCompact_univ
  rw [integral_add_fun (integrable_const _) hr]
  simp

/-- Strictly positive information for every compact prior supported away from zero. -/
theorem mixtureEntropy_pos (W : ProbabilityMeasure Γ)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v)) (hΓ0 : (0 : Space d) ∉ Γ) :
    0 < mixtureEntropy K Z W := by
  have hvar := precision_variance_of_covariance K Z hcenter hcov
  have hn := mixtureEntropy_nonneg K Z hcenter hvar W R hR hK
  by_contra! h
  have hzero : mixtureEntropy K Z W = 0 := le_antisymm h hn
  letI := mixture_isProbability K Z hcenter hvar W
  have hkl : klDiv (mixtureMeasure K Z W) Z = 0 := by
    rw [mixture_klDiv K Z hcenter hvar W R hR hK, hzero]
    simp
  have heq : mixtureMeasure K Z W = Z := klDiv_eq_zero_iff.mp hkl
  have hm := mixture_norm_sq K Z hcenter hcov W R hR hK
  rw [heq] at hm
  have hr : Integrable (fun r : Γ => ‖(r : Space d)‖^2) (W : Measure Γ) := by
    simpa using (continuous_subtype_val.norm.pow 2).continuousOn.integrableOn_compact
      (μ := (W : Measure Γ)) isCompact_univ
  have hp : 0 < ∫ r : Γ, ‖(r : Space d)‖^2 ∂(W : Measure Γ) := by
    rw [integral_pos_iff_support_of_nonneg (fun r => sq_nonneg _) hr]
    have hs : Function.support (fun r : Γ => ‖(r : Space d)‖^2) = Set.univ := by
      ext r
      have hr0 : (r : Space d) ≠ 0 := by intro he; exact hΓ0 (he ▸ r.2)
      simp [norm_ne_zero_iff.mpr hr0]
    simp [hs]
  linarith

end BoundaryReduction.Gaussian
