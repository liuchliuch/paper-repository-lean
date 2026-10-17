import BoundaryReduction.GaussianMixture
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

open Real Set MeasureTheory
open scoped Classical NNReal BoundedContinuousFunction
namespace BoundaryReduction.Gaussian

variable {d : ℕ} {Γ : Set (Space d)} [CompactSpace Γ]
variable (K : Space d →L[ℝ] Space d)
variable (Z : Measure (Space d)) [ProbabilityTheory.IsGaussian Z]

/-- Every linear exponential of the norm is Gaussian-integrable, by Fernique. -/
lemma gaussian_integrable_exp_norm (A : ℝ) :
    Integrable (fun x : Space d => exp (A*‖x‖)) Z := by
  obtain ⟨c,hc,hint⟩ := ProbabilityTheory.IsGaussian.exists_integrable_exp_sq Z
  have hb : Integrable (fun x : Space d => exp (A^2/(4*c))*exp (c*‖x‖^2)) Z :=
    hint.const_mul _
  apply hb.mono'
    ((Real.continuous_exp.comp (continuous_const.mul continuous_norm)).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro x
  change |exp (A*‖x‖)| ≤ _
  rw [abs_of_pos (exp_pos _), ← exp_add]
  apply exp_le_exp.mpr
  have he : 4*c*(A*‖x‖-c*‖x‖^2) ≤ A^2 := by
    nlinarith [sq_nonneg (2*c*‖x‖-A)]
  have hd : A*‖x‖-c*‖x‖^2 ≤ A^2/(4*c) :=
    (le_div_iff₀ (show 0 < 4*c by positivity)).mpr (by nlinarith [he])
  linarith

lemma continuous_likelihood (W : Measure Γ) [IsProbabilityMeasure W]
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R) : Continuous (likelihood K W) := by
  have h := Real.continuous_exp.comp (lipschitz_phi K W R hR).continuous
  have heq : (fun x => exp (phi K W x)) = likelihood K W := by
    ext x
    exact exp_log (likelihood_pos K W x)
  change Continuous (fun x => exp (phi K W x)) at h
  rwa [heq] at h

/-- The entropy functional in (4.6), in its density integral form. -/
noncomputable def mixtureEntropy (W : ProbabilityMeasure Γ) : ℝ :=
  ∫ x, likelihood K (W : Measure Γ) x * phi K (W : Measure Γ) x ∂Z

lemma entropy_pointwise_bound (W : Measure Γ) [IsProbabilityMeasure W]
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v)) (x : Space d) :
    |likelihood K W x*phi K W x| ≤
      ((R:ℝ)*‖K‖+(R:ℝ)^2*‖K‖/2)*exp (((R:ℝ)*‖K‖+1)*‖x‖) := by
  let A := (R:ℝ)*‖K‖
  let b := (R:ℝ)^2*‖K‖/2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have he := likelihood_envelope K W R hR hK x
  have hp := phi_envelope K W R hR hK x
  have ht := norm_nonneg x
  have ht_exp : ‖x‖ ≤ exp ‖x‖ := by linarith [add_one_le_exp ‖x‖]
  have h1_exp : 1 ≤ exp ‖x‖ := (one_le_exp_iff).mpr ht
  have hlin : A*‖x‖+b ≤ (A+b)*exp ‖x‖ := by
    nlinarith [mul_le_mul_of_nonneg_left ht_exp hA,
      mul_le_mul_of_nonneg_left h1_exp hb]
  rw [abs_mul, abs_of_pos (likelihood_pos K W x)]
  calc
    _ ≤ exp (A*‖x‖)*(A*‖x‖+b) :=
      mul_le_mul he.2 hp (abs_nonneg _) (exp_pos _).le
    _ ≤ exp (A*‖x‖)*((A+b)*exp ‖x‖) :=
      mul_le_mul_of_nonneg_left hlin (exp_pos _).le
    _ = (A+b)*exp ((A+1)*‖x‖) := by
      rw [show (A+1)*‖x‖ = A*‖x‖+‖x‖ by ring, exp_add]
      ring

lemma integrable_entropy (W : Measure Γ) [IsProbabilityMeasure W]
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v)) :
    Integrable (fun x => likelihood K W x*phi K W x) Z := by
  have hb := (gaussian_integrable_exp_norm Z ((R:ℝ)*‖K‖+1)).const_mul
    ((R:ℝ)*‖K‖+(R:ℝ)^2*‖K‖/2)
  apply hb.mono'
    (((continuous_likelihood K W R hR).mul (lipschitz_phi K W R hR).continuous).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs]
    exact entropy_pointwise_bound K W R hR hK x)

lemma continuous_likelihood_prior (x : Space d) :
    Continuous (fun W : ProbabilityMeasure Γ => likelihood K (W : Measure Γ) x) := by
  let f : Γ →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun r => exp (exponent K r x), Real.continuous_exp.comp (continuous_exponent K x)⟩
  exact ProbabilityMeasure.continuous_integral_boundedContinuousFunction f

lemma continuous_phi_prior (x : Space d) :
    Continuous (fun W : ProbabilityMeasure Γ => phi K (W : Measure Γ) x) := by
  exact (continuous_likelihood_prior K x).log (fun W => (likelihood_pos K (W : Measure Γ) x).ne')

/-- Weak continuity of the actual compact-prior entropy integral in Section 4.1. -/
theorem continuous_mixtureEntropy
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v)) :
    Continuous (mixtureEntropy K Z : ProbabilityMeasure Γ → ℝ) := by
  apply continuous_of_dominated
    (bound := fun x => ((R:ℝ)*‖K‖+(R:ℝ)^2*‖K‖/2)*exp (((R:ℝ)*‖K‖+1)*‖x‖))
  · intro W
    exact (integrable_entropy K Z (W : Measure Γ) R hR hK).aestronglyMeasurable
  · intro W
    exact Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs]
      exact entropy_pointwise_bound K (W : Measure Γ) R hR hK x)
  · exact (gaussian_integrable_exp_norm Z ((R:ℝ)*‖K‖+1)).const_mul _
  · exact Filter.Eventually.of_forall (fun x =>
      (continuous_likelihood_prior K x).mul (continuous_phi_prior K x))

end BoundaryReduction.Gaussian
