import BoundaryReduction.GaussianTranslation

open Real Set MeasureTheory ProbabilityTheory
open scoped Classical NNReal ENNReal
namespace BoundaryReduction.Gaussian

variable {d : ℕ} {Γ : Set (Space d)} [CompactSpace Γ]
variable (K : Space d →L[ℝ] Space d) (Z : Measure (Space d)) [IsGaussian Z]

noncomputable def pointPrior (r : Γ) : ProbabilityMeasure Γ := ⟨Measure.dirac r, inferInstance⟩

lemma likelihood_point (r : Γ) (x : Space d) :
    likelihood K (pointPrior r : Measure Γ) x = exp (exponent K r x) := by
  simp [likelihood, pointPrior]

/-- Convex combination of two actual countably additive Borel priors. -/
noncomputable def priorMix (V W : ProbabilityMeasure Γ) (a : ℝ) (ha : a ∈ Icc (0:ℝ) 1) :
    ProbabilityMeasure Γ :=
  ⟨(ENNReal.ofReal (1-a)) • (W : Measure Γ)+(ENNReal.ofReal a) • (V : Measure Γ), by
    constructor
    simp only [Measure.add_apply, MeasurableSet.univ, Measure.smul_apply,
      measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add (by linarith [ha.2]) ha.1]
    norm_num⟩

lemma likelihood_mix (V W : ProbabilityMeasure Γ) (a : ℝ) (ha : a ∈ Icc (0:ℝ) 1) (x : Space d) :
    likelihood K (priorMix V W a ha : Measure Γ) x =
      (1-a)*likelihood K (W : Measure Γ) x+a*likelihood K (V : Measure Γ) x := by
  have hiW : Integrable (fun r : Γ => exp (exponent K r x)) (W : Measure Γ) := by
    simpa using integrable_exp_shift K (W : Measure Γ) x 0
  have hiV : Integrable (fun r : Γ => exp (exponent K r x)) (V : Measure Γ) := by
    simpa using integrable_exp_shift K (V : Measure Γ) x 0
  unfold likelihood priorMix
  simp only [ProbabilityMeasure.coe_mk]
  rw [integral_add_measure]
  · simp only [integral_smul_measure, ENNReal.toReal_ofReal ha.1,
      ENNReal.toReal_ofReal (show 0 ≤ 1-a by linarith [ha.2]), smul_eq_mul]
  · exact hiW.smul_measure ENNReal.ofReal_ne_top
  · exact hiV.smul_measure ENNReal.ofReal_ne_top

lemma cross_pointwise_bound (V W : ProbabilityMeasure Γ)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v)) (x : Space d) :
    |likelihood K (V : Measure Γ) x*phi K (W : Measure Γ) x| ≤
      ((R:ℝ)*‖K‖+(R:ℝ)^2*‖K‖/2)*exp (((R:ℝ)*‖K‖+1)*‖x‖) := by
  let A := (R:ℝ)*‖K‖
  let b := (R:ℝ)^2*‖K‖/2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have he := likelihood_envelope K (V : Measure Γ) R hR hK x
  have hp := phi_envelope K (W : Measure Γ) R hR hK x
  have ht := norm_nonneg x
  have ht_exp : ‖x‖ ≤ exp ‖x‖ := by linarith [add_one_le_exp ‖x‖]
  have h1_exp : 1 ≤ exp ‖x‖ := (one_le_exp_iff).mpr ht
  have hlin : A*‖x‖+b ≤ (A+b)*exp ‖x‖ := by
    nlinarith [mul_le_mul_of_nonneg_left ht_exp hA,
      mul_le_mul_of_nonneg_left h1_exp hb]
  rw [abs_mul, abs_of_pos (likelihood_pos K (V : Measure Γ) x)]
  calc
    _ ≤ exp (A*‖x‖)*(A*‖x‖+b) := mul_le_mul he.2 hp (abs_nonneg _) (exp_pos _).le
    _ ≤ exp (A*‖x‖)*((A+b)*exp ‖x‖) := mul_le_mul_of_nonneg_left hlin (exp_pos _).le
    _ = (A+b)*exp ((A+1)*‖x‖) := by
      rw [show (A+1)*‖x‖ = A*‖x‖+‖x‖ by ring, exp_add]
      ring

lemma integrable_cross (V W : ProbabilityMeasure Γ)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v)) :
    Integrable (fun x => likelihood K (V : Measure Γ) x*phi K (W : Measure Γ) x) Z := by
  have hb := (gaussian_integrable_exp_norm Z ((R:ℝ)*‖K‖+1)).const_mul
    ((R:ℝ)*‖K‖+(R:ℝ)^2*‖K‖/2)
  apply hb.mono'
    (((continuous_likelihood K (V : Measure Γ) R hR).mul
      (lipschitz_phi K (W : Measure Γ) R hR).continuous).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs]
    exact cross_pointwise_bound K V W R hR hK x)

/-- The upper quadratic entropy remainder, requiring only the scalar logarithm inequality. -/
lemma entropy_remainder_upper {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    u*log u-v*log v-(u-v)*(1+log v) ≤ (u-v)^2/v := by
  have h := mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos (div_pos hu hv)) hu.le
  rw [log_div hu.ne' hv.ne'] at h
  have heq : u*(u/v-1) = u^2/v-u := by ring
  rw [heq] at h
  have heq2 : (u-v)^2/v = u^2/v-2*u+v := by field_simp <;> ring
  rw [heq2]
  nlinarith

/-- The lower tangent bound for entropy. -/
lemma entropy_remainder_nonneg {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    0 ≤ u*log u-v*log v-(u-v)*(1+log v) := by
  have h := mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos (div_pos hv hu)) hu.le
  rw [log_div hv.ne' hu.ne'] at h
  have heq : u*(v/u-1) = v-u := by field_simp <;> ring
  rw [heq] at h
  nlinarith

lemma integrable_joint_cross (V W : ProbabilityMeasure Γ)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v)) :
    Integrable (fun p : Γ × Space d => exp (exponent K p.1 p.2)*phi K (W : Measure Γ) p.2)
      ((V : Measure Γ).prod Z) := by
  have hb := ((gaussian_integrable_exp_norm Z ((R:ℝ)*‖K‖+1)).const_mul
    ((R:ℝ)*‖K‖+(R:ℝ)^2*‖K‖/2)).comp_snd (V : Measure Γ)
  have hc : Continuous (fun p : Γ × Space d => exp (exponent K p.1 p.2)) := by
    unfold exponent
    fun_prop
  apply hb.mono' ((hc.mul ((lipschitz_phi K (W : Measure Γ) R hR).continuous.comp continuous_snd)).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro p
  rw [Real.norm_eq_abs]
  have h := cross_pointwise_bound K (pointPrior p.1) W R hR hK p.2
  rwa [likelihood_point] at h

variable (hcenter : (∫ x, x ∂Z) = 0)
variable (hcov : ∀ (L : StrongDual ℝ (Space d)) (v : Space d),
  covariance L (precisionForm K v) Z = L v)
include hcenter hcov

lemma cross_as_prior_average (V W : ProbabilityMeasure Γ)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v)) :
    (∫ r : Γ, expectedLog K (W : Measure Γ) Z (r : Space d) ∂(V : Measure Γ)) =
      ∫ x, likelihood K (V : Measure Γ) x*phi K (W : Measure Γ) x ∂Z := by
  simp_rw [expectedLog_component_identity K Z hcenter hcov (W : Measure Γ) R hR]
  rw [integral_integral_swap (f := fun r : Γ => fun x : Space d =>
    exp (exponent K r x)*phi K (W : Measure Γ) x)
    (integrable_joint_cross K Z V W R hR hK)]
  congr 1
  ext x
  rw [integral_mul_const]
  rfl

lemma integrable_expectedLog_prior (V W : ProbabilityMeasure Γ)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v)) :
    Integrable (fun r : Γ => expectedLog K (W : Measure Γ) Z (r : Space d)) (V : Measure Γ) := by
  have h := (integrable_joint_cross K Z V W R hR hK).integral_prod_left
  exact h.congr (Filter.Eventually.of_forall (fun r =>
    (expectedLog_component_identity K Z hcenter hcov (W : Measure Γ) R hR r).symm))

/-- The actual entropy tangent inequality for arbitrary Borel priors. -/
lemma cross_le_entropy (V W : ProbabilityMeasure Γ)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v)) :
    (∫ x, likelihood K (V : Measure Γ) x*phi K (W : Measure Γ) x ∂Z) ≤ mixtureEntropy K Z V := by
  have hvar := precision_variance_of_covariance K Z hcenter hcov
  have hEV := integrable_entropy K Z (V : Measure Γ) R hR hK
  have hLV := integrable_likelihood K Z hcenter hvar (V : Measure Γ)
  have hLW := integrable_likelihood K Z hcenter hvar (W : Measure Γ)
  have hpt : ∀ x : Space d,
      likelihood K (V : Measure Γ) x*phi K (W : Measure Γ) x ≤
        likelihood K (V : Measure Γ) x*phi K (V : Measure Γ) x-
          likelihood K (V : Measure Γ) x+likelihood K (W : Measure Γ) x := by
    intro x
    have h := entropy_remainder_nonneg (likelihood_pos K (V : Measure Γ) x)
      (likelihood_pos K (W : Measure Γ) x)
    dsimp [phi]
    nlinarith
  have hi := integral_mono (integrable_cross K Z V W R hR hK)
    ((hEV.sub hLV).add hLW) hpt
  simp only [Pi.add_apply, Pi.sub_apply] at hi
  have hs := integral_add (hEV.sub hLV) hLW
  have ht := integral_sub hEV hLV
  simp only [Pi.sub_apply] at hs ht
  rw [hs, ht, integral_likelihood K Z hcenter hvar (V : Measure Γ),
    integral_likelihood K Z hcenter hvar (W : Measure Γ)] at hi
  simpa only [sub_add_cancel, mixtureEntropy] using hi

/-- Sufficiency in Proposition 4.2, using the actual Gaussian shift expectations. -/
theorem minimizer_of_boundary_condition (W : ProbabilityMeasure Γ)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v))
    (hboundary : ∀ r : Γ, mixtureEntropy K Z W ≤ expectedLog K (W : Measure Γ) Z (r : Space d)) :
    ∀ V : ProbabilityMeasure Γ, mixtureEntropy K Z W ≤ mixtureEntropy K Z V := by
  intro V
  have hi := integral_mono (integrable_const (mixtureEntropy K Z W))
    (integrable_expectedLog_prior K Z hcenter hcov V W R hR hK) hboundary
  simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] at hi
  rw [cross_as_prior_average K Z hcenter hcov V W R hR hK] at hi
  exact hi.trans (cross_le_entropy K Z hcenter hcov V W R hR hK)

end BoundaryReduction.Gaussian
