import GeometricMedianCoresets.GaussianProjection
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-! Explicit Gaussian absolute first moment, with the normalization used in Lemma 2.1. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace GeometricMedianCoresets.GaussianProjection

lemma integral_pos_mul_exp :
    (∫ r : ℝ in Ioi 0, r * Real.exp (-(1/2:ℝ) * r ^ 2)) = 1 := by
  have hc := integral_mul_cexp_neg_mul_sq (b := (1/2:ℂ)) (by norm_num)
  have hcast := integral_ofReal (𝕜 := ℂ)
    (μ := (volume : Measure ℝ).restrict (Ioi 0))
    (f := fun r : ℝ => r * Real.exp (-(1/2:ℝ) * r ^ 2))
  have heq : (fun r : ℝ => (↑(r * Real.exp (-(1/2:ℝ) * r ^ 2)) : ℂ)) =
      fun r : ℝ => (r:ℂ) * Complex.exp (-(1/2:ℂ) * (r:ℂ) ^ 2) := by
    funext r
    simp only [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg,
      Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_pow, Complex.ofReal_ofNat]
  have hcast' : (↑(∫ r : ℝ in Ioi 0, r * Real.exp (-(1/2:ℝ) * r ^ 2)) : ℂ) = 1 := by
    calc _ = ∫ r : ℝ in Ioi 0, (↑(r * Real.exp (-(1/2:ℝ) * r ^ 2)) : ℂ) := hcast.symm
      _ = ∫ r : ℝ in Ioi 0, (r:ℂ) * Complex.exp (-(1/2:ℂ) * (r:ℂ) ^ 2) :=
        integral_congr_ae (Filter.Eventually.of_forall fun r => congrFun heq r)
      _ = 1 := by simpa using hc
  exact Complex.ofReal_inj.1 hcast'

/-- The absolute first moment of a standard real Gaussian. -/
theorem firstMoment_eq : firstMoment = Real.sqrt (2 / Real.pi) := by
  have hraw : (∫ r : ℝ, |r| * Real.exp (-(1/2:ℝ) * r ^ 2)) = 2 := by
    have heq : (fun r : ℝ => |r| * Real.exp (-(1/2:ℝ) * r ^ 2)) =
        (fun r : ℝ => |r| * Real.exp (-(1/2:ℝ) * |r| ^ 2)) := by
      simp only [sq_abs]
    rw [heq]
    have habs := integral_comp_abs (f := fun r : ℝ => r * Real.exp (-(1/2:ℝ) * r ^ 2))
    rw [habs, integral_pos_mul_exp]
    norm_num
  unfold firstMoment
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    integral_withDensity_eq_integral_toReal_smul (measurable_gaussianPDF 0 1)
      (Filter.Eventually.of_forall fun _ => gaussianPDF_lt_top) ]
  simp only [toReal_gaussianPDF, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero,
    smul_eq_mul]
  have heq : (fun r : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-r ^ 2 / 2) * |r|) =
      fun r => (Real.sqrt (2 * Real.pi))⁻¹ *
        (|r| * Real.exp (-(1/2:ℝ) * r ^ 2)) := by
    funext r
    rw [show -r ^ 2 / 2 = -(1/2:ℝ) * r ^ 2 by ring]
    ring
  rw [heq, integral_const_mul, hraw]
  have hπ := Real.pi_pos
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)
  have hsp := Real.sqrt_pos.2 (by positivity : 0 < 2 * Real.pi)
  have htarget := Real.sq_sqrt (by positivity : 0 ≤ 2 / Real.pi)
  have hnonneg := Real.sqrt_nonneg (2 / Real.pi)
  have he : (Real.sqrt (2 / Real.pi) * Real.sqrt (2 * Real.pi)) ^ 2 = 4 := by
    rw [mul_pow, htarget, hs]
    field_simp
    norm_num
  have he' : Real.sqrt (2 / Real.pi) * Real.sqrt (2 * Real.pi) = 2 := by
    nlinarith [mul_nonneg hnonneg hsp.le]
  have hx : Real.sqrt (2 / Real.pi) = 2 / Real.sqrt (2 * Real.pi) :=
    (eq_div_iff hsp.ne').2 he'
  rw [hx]
  ring

end GeometricMedianCoresets.GaussianProjection
