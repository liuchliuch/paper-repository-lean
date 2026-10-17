import BoundaryReduction.GaussianMoments

open Real Set MeasureTheory ProbabilityTheory
open scoped Classical NNReal ENNReal
namespace BoundaryReduction.Gaussian

variable {d : ℕ} {Γ : Set (Space d)} [CompactSpace Γ]
variable (K : Space d →L[ℝ] Space d) (Z : Measure (Space d)) [IsGaussian Z]

noncomputable def priorMeasure (W : ProbabilityMeasure Γ) : Measure (Space d) :=
  (W : Measure Γ).map Subtype.val

lemma priorMeasure_isProbability (W : ProbabilityMeasure Γ) : IsProbabilityMeasure (priorMeasure W) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

lemma priorMeasure_injective : Function.Injective (priorMeasure (Γ := Γ)) := by
  intro V W h
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext
  intro s _
  have hΓ : MeasurableSet Γ := (isCompact_iff_compactSpace.mpr inferInstance).measurableSet
  have he := MeasurableEmbedding.subtype_coe hΓ
  have hh := congrArg (fun P : Measure (Space d) => P (Subtype.val '' s)) h
  simpa only [priorMeasure, he.map_apply, Set.preimage_image_eq _ Subtype.val_injective] using hh

lemma priorMeasure_mgf_pos (W : ProbabilityMeasure Γ) (L : StrongDual ℝ (Space d)) (t : ℝ) :
    0 < mgf L (priorMeasure W) t := by
  have hi : Integrable (fun r : Γ => exp (t*L (r : Space d))) (W : Measure Γ) := by
    have hc : Continuous (fun r : Γ => exp (t*L (r : Space d))) := by fun_prop
    simpa using hc.continuousOn.integrableOn_compact (μ := (W : Measure Γ)) isCompact_univ
  have hp := integral_exp_pos hi
  unfold mgf priorMeasure
  rw [integral_map (by fun_prop) (by fun_prop)]
  exact hp

lemma integrable_joint_mgf (W : ProbabilityMeasure Γ) (L : StrongDual ℝ (Space d)) (t : ℝ)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v)) :
    Integrable (fun p : Γ × Space d => exp (exponent K p.1 p.2)*exp (t*L p.2))
      ((W : Measure Γ).prod Z) := by
  have hb := (gaussian_integrable_exp_norm Z ((R:ℝ)*‖K‖+|t| *‖L‖)).comp_snd (W : Measure Γ)
  have hc : Continuous (fun p : Γ × Space d => exp (exponent K p.1 p.2)*exp (t*L p.2)) := by
    unfold exponent
    fun_prop
  apply hb.mono' hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro p
  rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hp := (likelihood_envelope K (pointPrior p.1 : Measure Γ) R hR hK p.2).2
  rw [likelihood_point] at hp
  have hL : t*L p.2 ≤ |t| *‖L‖*‖p.2‖ := by
    have h := mul_le_mul_of_nonneg_left (L.le_opNorm p.2) (abs_nonneg t)
    rw [Real.norm_eq_abs] at h
    have hab := le_abs_self (t*L p.2)
    rw [abs_mul] at hab
    nlinarith
  have he := exp_le_exp.mpr hL
  calc
    _ ≤ exp ((R:ℝ)*‖K‖*‖p.2‖)*exp (|t| *‖L‖*‖p.2‖) :=
      mul_le_mul hp he (exp_pos _).le (exp_pos _).le
    _ = _ := by rw [← exp_add]; congr 1; ring

variable (hcenter : (∫ x, x ∂Z) = 0)
variable (hcov : ∀ (L : StrongDual ℝ (Space d)) (v : Space d), covariance L (precisionForm K v) Z = L v)
include hcenter hcov

/-- MGF factorization for the actual Gaussian location mixture. -/
lemma mixture_mgf (W : ProbabilityMeasure Γ) (L : StrongDual ℝ (Space d)) (t : ℝ)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v)) :
    mgf L (mixtureMeasure K Z W) t = mgf L Z t*mgf L (priorMeasure W) t := by
  have hmeas : Measurable (fun x => ENNReal.ofReal (likelihood K (W : Measure Γ) x)) :=
    (continuous_likelihood K (W : Measure Γ) R hR).measurable.ennreal_ofReal
  unfold mgf mixtureMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hmeas
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (likelihood_pos K (W : Measure Γ) _).le, smul_eq_mul]
  have hs := integral_integral_swap (f := fun r : Γ => fun x : Space d =>
    exp (exponent K r x)*exp (t*L x)) (integrable_joint_mgf K Z W L t R hR hK)
  have heq : (fun x : Space d => ∫ r : Γ, exp (exponent K r x)*exp (t*L x) ∂(W : Measure Γ)) =
      fun x => likelihood K (W : Measure Γ) x*exp (t*L x) := by
    ext x
    rw [integral_mul_const]
    rfl
  rw [heq] at hs
  rw [← hs]
  have hr : ∀ r : Γ, (∫ x, exp (exponent K r x)*exp (t*L x) ∂Z) =
      exp (variance L Z*t^2/2)*exp (t*L (r : Space d)) := by
    intro r
    rw [← component_integral_as_translation K Z hcenter hcov r (fun x => exp (t*L x)) (by fun_prop)]
    have h := mgf_gaussian_shift K Z hcenter hcov (r : Space d) L t
    unfold mgf at h
    rw [integral_map (by fun_prop) (by fun_prop)] at h
    rw [h, exp_add]
  simp_rw [hr]
  rw [integral_const_mul]
  have he : (∫ r : Γ, exp (t*L (r : Space d)) ∂(W : Measure Γ)) =
      ∫ x, exp (t*L x) ∂priorMeasure W := by
    unfold priorMeasure
    rw [integral_map (by fun_prop) (by fun_prop)]
  rw [he]
  have hg := gaussian_dual_mgf Z hcenter L t
  unfold mgf at hg
  rw [hg]

/-- Gaussian convolution is injective on compact Borel priors. -/
theorem mixtureMeasure_injective
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v)) : Function.Injective (mixtureMeasure K Z : ProbabilityMeasure Γ → Measure (Space d)) := by
  intro V W h
  apply priorMeasure_injective
  letI := priorMeasure_isProbability V
  letI := priorMeasure_isProbability W
  apply dual_mgf_unique
  · intro L
    ext t
    have he := congrArg (fun P : Measure (Space d) => mgf L P t) h
    dsimp only at he
    rw [mixture_mgf K Z hcenter hcov V L t R hR hK,
      mixture_mgf K Z hcenter hcov W L t R hR hK] at he
    have hp : 0 < mgf L Z t := by rw [gaussian_dual_mgf Z hcenter]; exact exp_pos _
    exact mul_left_cancel₀ hp.ne' he
  · intro L t
    exact priorMeasure_mgf_pos V L t

end BoundaryReduction.Gaussian
