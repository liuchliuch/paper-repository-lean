import Paper38.CosineExample
import Mathlib.Probability.Distributions.Gaussian.Real

/-! Actual Gaussian expectation identities for Example 9.1. -/

noncomputable section

open Real Set MeasureTheory ProbabilityTheory

namespace Paper38.Cosine

lemma integrable_cexp_I_gaussian (μ : ℝ) (v : NNReal) :
    Integrable (fun x : ℝ => Complex.exp ((x : ℂ) * Complex.I)) (gaussianReal μ v) := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  filter_upwards [] with x
  simp [Complex.norm_exp]

lemma integral_cos_gaussian (μ : ℝ) (v : NNReal) :
    (∫ x : ℝ, Real.cos x ∂gaussianReal μ v) = attenuation v * Real.cos μ := by
  have h := congrArg Complex.re (charFun_gaussianReal (μ := μ) (v := v) 1)
  rw [charFun_apply_real] at h
  simp only [Complex.ofReal_one, one_mul, one_pow, mul_one] at h
  calc
    (∫ x : ℝ, Real.cos x ∂gaussianReal μ v) =
        RCLike.re (∫ x : ℝ, Complex.exp ((x : ℂ) * Complex.I) ∂gaussianReal μ v) := by
      simpa [Complex.exp_re] using integral_re (integrable_cexp_I_gaussian μ v)
    _ = attenuation v * Real.cos μ := by simpa [Complex.exp_re, attenuation, neg_div] using h

lemma integral_sin_gaussian (μ : ℝ) (v : NNReal) :
    (∫ x : ℝ, Real.sin x ∂gaussianReal μ v) = attenuation v * Real.sin μ := by
  have h := congrArg Complex.im (charFun_gaussianReal (μ := μ) (v := v) 1)
  rw [charFun_apply_real] at h
  simp only [Complex.ofReal_one, one_mul, one_pow, mul_one] at h
  calc
    (∫ x : ℝ, Real.sin x ∂gaussianReal μ v) =
        RCLike.im (∫ x : ℝ, Complex.exp ((x : ℂ) * Complex.I) ∂gaussianReal μ v) := by
      simpa [Complex.exp_im] using integral_im (integrable_cexp_I_gaussian μ v)
    _ = attenuation v * Real.sin μ := by simpa [Complex.exp_im, attenuation, neg_div] using h

lemma integrable_sin_gaussian (μ : ℝ) (v : NNReal) :
    Integrable (fun x : ℝ => Real.sin x) (gaussianReal μ v) := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  filter_upwards [] with x
  exact Real.abs_sin_le_one x

lemma integrable_cos_gaussian (μ : ℝ) (v : NNReal) :
    Integrable (fun x : ℝ => Real.cos x) (gaussianReal μ v) := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  filter_upwards [] with x
  exact Real.abs_cos_le_one x

/-- The first formula of (9.2), as an actual integral of the potential derivative. -/
lemma gaussian_meanForce (ε μ : ℝ) (v : NNReal) :
    (∫ x : ℝ, deriv (potential ε) x ∂gaussianReal μ v) = meanForce ε μ v := by
  simp only [deriv_potential, force]
  have hid : Integrable (fun x : ℝ => x) (gaussianReal μ v) := by
    simpa using (memLp_id_gaussianReal (μ := μ) (v := v) 1).integrable (by norm_num)
  rw [integral_sub hid
      ((integrable_sin_gaussian μ v).const_mul ε), integral_const_mul,
      integral_id_gaussianReal, integral_sin_gaussian]
  unfold meanForce
  ring

/-- The second formula of (9.2), as an actual integral of the Hessian. -/
lemma gaussian_meanCurvature (ε μ : ℝ) (v : NNReal) :
    (∫ x : ℝ, deriv (deriv (potential ε)) x ∂gaussianReal μ v) = meanCurvature ε μ v := by
  simp only [second_deriv_potential, curvature]
  rw [integral_sub (integrable_const 1) ((integrable_cos_gaussian μ v).const_mul ε),
      integral_const_mul, integral_const, integral_cos_gaussian]
  simp [meanCurvature]
  ring

lemma integral_sq_gaussian (μ : ℝ) (v : NNReal) :
    (∫ x : ℝ, x ^ 2 ∂gaussianReal μ v) = μ ^ 2 + v := by
  have hv := variance_eq_sub (memLp_id_gaussianReal (μ := μ) (v := v) 2)
  simp only [variance_id_gaussianReal, integral_id_gaussianReal, id_eq, Pi.pow_apply] at hv
  linarith

/-- The expected potential underlying the energy (9.4). -/
lemma gaussian_expected_potential (ε μ : ℝ) (v : NNReal) :
    (∫ x : ℝ, potential ε x ∂gaussianReal μ v) =
      (μ ^ 2 + v) / 2 + ε + ε * attenuation v * Real.cos μ := by
  have hsq : Integrable (fun x : ℝ => x ^ 2) (gaussianReal μ v) :=
    (memLp_id_gaussianReal (μ := μ) (v := v) 2).integrable_sq
  have hpert : Integrable (fun x : ℝ => ε * (1 + Real.cos x)) (gaussianReal μ v) := by
    simpa using (((integrable_const 1).add (integrable_cos_gaussian μ v)).const_mul ε)
  unfold potential
  rw [integral_add (hsq.div_const 2) hpert,
      integral_div, integral_const_mul,
      integral_add (integrable_const 1) (integrable_cos_gaussian μ v),
      integral_const, integral_cos_gaussian, integral_sq_gaussian]
  simp
  ring

/-- (9.4) differs from the Gaussian expected-potential entropy representative
by exactly the irrelevant additive constant `ε`. -/
lemma gaussian_energy_identity (ε μ : ℝ) (v : NNReal) :
    (∫ x : ℝ, potential ε x ∂gaussianReal μ v) - Real.log (v : ℝ) / 2 =
      energy ε μ v + ε := by
  rw [gaussian_expected_potential]
  unfold energy
  ring

end Paper38.Cosine
