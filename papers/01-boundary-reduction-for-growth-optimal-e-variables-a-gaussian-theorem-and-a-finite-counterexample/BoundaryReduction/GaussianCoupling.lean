import BoundaryReduction.GaussianRelativeKL
import BoundaryReduction.IntegralLogSum

open Real Set MeasureTheory ProbabilityTheory InformationTheory
open scoped Classical NNReal ENNReal
namespace BoundaryReduction.Gaussian

variable {d : ℕ} {Γ : Set (Space d)} [CompactSpace Γ]
variable (K : Space d →L[ℝ] Space d) (Z : Measure (Space d)) [IsGaussian Z]

lemma phi_point (r : Γ) (x : Space d) : phi K (pointPrior r : Measure Γ) x = exponent K r x := by
  simp [phi,likelihood_point]

lemma likelihood_mapPrior (W : ProbabilityMeasure Γ) (T : Γ → Γ) (hT : Measurable T) (x : Space d) :
    likelihood K (CompactPrior.mapPrior W T hT : Measure Γ) x =
      ∫ r : Γ, exp (exponent K (T r) x) ∂(W : Measure Γ) := by
  unfold likelihood CompactPrior.mapPrior
  simp only [ProbabilityMeasure.coe_mk]
  exact integral_map hT.aemeasurable (Real.continuous_exp.comp (continuous_exponent K x)).aestronglyMeasurable

lemma coupling_pointwise_bound (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v)) (r s : Γ) (x : Space d) :
    |exp (exponent K s x)*(exponent K s x-exponent K r x)| ≤
      (2*((R:ℝ)*‖K‖+(R:ℝ)^2*‖K‖/2))*exp (((R:ℝ)*‖K‖+1)*‖x‖) := by
  have h1 := cross_pointwise_bound K (pointPrior s) (pointPrior s) R hR hK x
  have h2 := cross_pointwise_bound K (pointPrior s) (pointPrior r) R hR hK x
  simp only [likelihood_point,phi_point] at h1 h2
  calc
    _ = |exp (exponent K s x)*exponent K s x-exp (exponent K s x)*exponent K r x| := by rw [mul_sub]
    _ ≤ |exp (exponent K s x)*exponent K s x|+|exp (exponent K s x)*exponent K r x| := abs_sub _ _
    _ ≤ _ := by linarith

lemma integrable_joint_coupling (W : ProbabilityMeasure Γ) (T : Γ → Γ) (hT : Measurable T)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v)) :
    Integrable (fun p : Γ × Space d => exp (exponent K (T p.1) p.2)*
      (exponent K (T p.1) p.2-exponent K p.1 p.2)) ((W : Measure Γ).prod Z) := by
  have hb := ((gaussian_integrable_exp_norm Z ((R:ℝ)*‖K‖+1)).const_mul
    (2*((R:ℝ)*‖K‖+(R:ℝ)^2*‖K‖/2))).comp_snd (W : Measure Γ)
  have hc : Continuous (fun p : (Γ × Γ) × Space d =>
      exp (exponent K p.1.2 p.2)*(exponent K p.1.2 p.2-exponent K p.1.1 p.2)) := by
    unfold exponent
    fun_prop
  have hm := hc.measurable.comp
    ((measurable_fst.prodMk (hT.comp measurable_fst)).prodMk measurable_snd)
  apply hb.mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun p => by
    rw [Real.norm_eq_abs]
    exact coupling_pointwise_bound K R hR hK p.1 (T p.1) p.2)

variable (hcenter : (∫ x, x ∂Z) = 0)
variable (hcov : ∀ (L : StrongDual ℝ (Space d)) (v : Space d), covariance L (precisionForm K v) Z = L v)
include hcenter hcov

lemma component_relative_entropy
    (hsym : ∀ u v : Space d, inner ℝ u (K v) = inner ℝ v (K u)) (r s : Γ) :
    (∫ x, exp (exponent K s x)*(exponent K s x-exponent K r x) ∂Z) =
      inner ℝ ((s : Space d)-(r : Space d)) (K ((s : Space d)-(r : Space d)))/2 := by
  rw [← component_integral_as_translation K Z hcenter hcov s
    (fun x => exponent K s x-exponent K r x) (by
      have hc : Continuous (fun x => exponent K s x-exponent K r x) := by unfold exponent; fun_prop
      exact hc.aestronglyMeasurable)]
  have heq (z : Space d) : exponent K s (z+(s : Space d))-exponent K r (z+(s : Space d)) =
      precisionForm K ((s : Space d)-(r : Space d)) z+
        inner ℝ ((s : Space d)-(r : Space d)) (K ((s : Space d)-(r : Space d)))/2 := by
    simp only [exponent, precisionForm_apply, map_add, map_sub, inner_add_right,
      inner_sub_left, inner_sub_right]
    rw [hsym (s : Space d) (r : Space d)]
    ring
  simp_rw [heq]
  rw [integral_add_fun (IsGaussian.integrable_dual Z _) (integrable_const _),
    IsGaussian.integral_dual, hcenter, map_zero]
  simp

/-- Common-prior Gaussian log-sum bound, with the actual relative entropy. -/
theorem mapPrior_relative_kl_bound (W : ProbabilityMeasure Γ) (T : Γ → Γ) (hT : Measurable T)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v))
    (hsym : ∀ u v : Space d, inner ℝ u (K v) = inner ℝ v (K u)) :
    (klDiv (mixtureMeasure K Z (CompactPrior.mapPrior W T hT)) (mixtureMeasure K Z W)).toReal ≤
      ∫ r : Γ, inner ℝ ((T r : Space d)-(r : Space d)) (K ((T r : Space d)-(r : Space d)))/2 ∂(W : Measure Γ) := by
  let V := CompactPrior.mapPrior W T hT
  have hj := integrable_joint_coupling K Z W T hT R hR hK
  have hlog : ∀ᵐ x ∂Z, likelihood K (V : Measure Γ) x*
      (phi K (V : Measure Γ) x-phi K (W : Measure Γ) x) ≤
      ∫ r : Γ, exp (exponent K (T r) x)*(exponent K (T r) x-exponent K r x) ∂(W : Measure Γ) := by
    filter_upwards [hj.prod_left_ae] with x hx
    have hia : Integrable (fun r : Γ => exp (exponent K (T r) x)) (W : Measure Γ) := by
      have hh := integrable_exp_shift K (V : Measure Γ) x 0
      simp only [sub_zero] at hh
      exact hh.comp_measurable hT
    have hib : Integrable (fun r : Γ => exp (exponent K r x)) (W : Measure Γ) := by
      simpa only [sub_zero] using integrable_exp_shift K (W : Measure Γ) x 0
    have hpos : 0 < ∫ r : Γ, exp (exponent K (T r) x) ∂(W : Measure Γ) := by
      rw [← likelihood_mapPrior K W T hT x]
      exact likelihood_pos K (V : Measure Γ) x
    have heq : (fun r : Γ => exp (exponent K (T r) x)*log (exp (exponent K (T r) x)/exp (exponent K r x))) =
        (fun r : Γ => exp (exponent K (T r) x)*(exponent K (T r) x-exponent K r x)) := by
      ext r
      rw [log_div (exp_pos _).ne' (exp_pos _).ne',log_exp,log_exp]
    have hs := integral_log_sum (fun r : Γ => exp_pos (exponent K (T r) x))
      (fun r : Γ => exp_pos (exponent K r x)) hia hib (by rw [heq]; exact hx)
      hpos (likelihood_pos K (W : Measure Γ) x)
    rw [heq, ← likelihood_mapPrior K W T hT x] at hs
    change likelihood K (V : Measure Γ) x*log (likelihood K (V : Measure Γ) x/likelihood K (W : Measure Γ) x) ≤ _ at hs
    rwa [log_div (likelihood_pos K (V : Measure Γ) x).ne' (likelihood_pos K (W : Measure Γ) x).ne'] at hs
  have hleft : Integrable (fun x => likelihood K (V : Measure Γ) x*
      (phi K (V : Measure Γ) x-phi K (W : Measure Γ) x)) Z := by
    simpa only [mul_sub] using (integrable_cross K Z V V R hR hK).sub (integrable_cross K Z V W R hR hK)
  have hb := integral_mono_ae hleft hj.integral_prod_right hlog
  have hl : (∫ x, likelihood K (V : Measure Γ) x*(phi K (V : Measure Γ) x-phi K (W : Measure Γ) x) ∂Z) =
      (klDiv (mixtureMeasure K Z V) (mixtureMeasure K Z W)).toReal := by
    simp_rw [mul_sub]
    rw [integral_sub (integrable_cross K Z V V R hR hK) (integrable_cross K Z V W R hR hK),
      relative_klDiv K Z hcenter hcov V W R hR hK,
      ENNReal.toReal_ofReal (sub_nonneg.mpr (cross_le_entropy K Z hcenter hcov V W R hR hK))]
    rfl
  have hswap := integral_integral_swap (f := fun r : Γ => fun x : Space d =>
    exp (exponent K (T r) x)*(exponent K (T r) x-exponent K r x)) hj
  rw [hl,← hswap] at hb
  simpa only [component_relative_entropy K Z hcenter hcov hsym] using hb

/-- The explicit quadratic rate (4.22). -/
theorem mapPrior_relative_kl_le_ae (W : ProbabilityMeasure Γ) (T : Γ → Γ) (hT : Measurable T)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v))
    (hsym : ∀ u v : Space d, inner ℝ u (K v) = inner ℝ v (K u))
    {δ : ℝ} (hδ : 0 ≤ δ) (happrox : ∀ᵐ r ∂(W : Measure Γ), ‖(T r : Space d)-(r : Space d)‖ ≤ δ) :
    (klDiv (mixtureMeasure K Z (CompactPrior.mapPrior W T hT)) (mixtureMeasure K Z W)).toReal ≤ ‖K‖*δ^2/2 := by
  apply (mapPrior_relative_kl_bound K Z hcenter hcov W T hT R hR hK hsym).trans
  have hi := (integrable_joint_coupling K Z W T hT R hR hK).integral_prod_left
  have hquad : Integrable (fun r : Γ => inner ℝ ((T r : Space d)-(r : Space d))
      (K ((T r : Space d)-(r : Space d)))/2) (W : Measure Γ) :=
    hi.congr (Filter.Eventually.of_forall (fun r => component_relative_entropy K Z hcenter hcov hsym r (T r)))
  apply le_trans (integral_mono_ae hquad (integrable_const (‖K‖*δ^2/2)) ?_) (by simp)
  filter_upwards [happrox] with r hn
  let v : Space d := (T r : Space d)-(r : Space d)
  have hinner := real_inner_le_norm v (K v)
  have hop := K.le_opNorm v
  have hnorm : ‖v‖^2 ≤ δ^2 := sq_le_sq₀ (norm_nonneg v) hδ |>.mpr hn
  have hprod := mul_le_mul_of_nonneg_left hop (norm_nonneg v)
  nlinarith [mul_le_mul_of_nonneg_left hnorm (norm_nonneg K)]

end BoundaryReduction.Gaussian
