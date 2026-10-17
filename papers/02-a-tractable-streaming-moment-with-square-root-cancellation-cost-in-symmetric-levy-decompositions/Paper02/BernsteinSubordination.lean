import Paper02.Bernstein
import Paper02.MeasureDual
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Gaussian jump measures for Bernstein subordination

The elementary Bernstein kernel `1 - exp (-u*t)` becomes a genuine symmetric
Lévy exponent after composing with `t = x²`.  The jump measure is the law of
an absolute centred Gaussian of variance `2*u`, with its possible zero atom
removed.  No Lévy-membership hypothesis is used in this construction.
-/

noncomputable section

namespace Paper02.Bernstein

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

/-- Finite measures automatically obey the Lévy integrability condition. -/
lemma levyIntegrable_of_finite (ν : Measure ℝ) [IsFiniteMeasure ν] : LevyIntegrable ν := by
  rw [Paper02.LSym.levyIntegrable_iff]
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  filter_upwards [] with s
  rw [Real.norm_eq_abs, abs_of_nonneg (le_min (sq_nonneg s) zero_le_one)]
  exact min_le_right _ _

/-- Remove zero and fold a finite real measure onto the positive half-line. -/
def positiveFold (μ : Measure ℝ) : Measure ℝ := (μ.map abs).restrict (Ioi 0)

instance positiveFold_finite (μ : Measure ℝ) [IsFiniteMeasure μ] :
    IsFiniteMeasure (positiveFold μ) := by unfold positiveFold; infer_instance

lemma positiveFold_support (μ : Measure ℝ) : (positiveFold μ).restrict (Iic 0) = 0 := by
  unfold positiveFold
  rw [Measure.restrict_restrict measurableSet_Iic]
  have hset : Iic (0 : ℝ) ∩ Ioi 0 = ∅ := by ext s; simp
  rw [hset, Measure.restrict_empty]

/-- Folding does not alter a cosine jump integral; at zero its integrand vanishes. -/
lemma integral_positiveFold (μ : Measure ℝ) (x : ℝ) :
    ∫ s in Ioi (0 : ℝ), (1 - Real.cos (x * s)) ∂positiveFold μ =
      ∫ s, (1 - Real.cos (x * s)) ∂μ := by
  unfold positiveFold
  rw [Measure.restrict_restrict measurableSet_Ioi, inter_self,
    ← integral_indicator measurableSet_Ioi,
    integral_map (by fun_prop : AEMeasurable abs μ)]
  · apply integral_congr_ae
    filter_upwards [] with s
    by_cases hs : s = 0
    · subst s
      simp
    · rw [indicator_of_mem (by exact abs_pos.mpr hs)]
      rcases le_total 0 s with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_nonpos h, mul_neg, Real.cos_neg]
  · exact ((by fun_prop : Continuous (fun s : ℝ => 1 - Real.cos (x * s))).measurable.indicator
      measurableSet_Ioi).aestronglyMeasurable

/-- Cosine transform of a centred Gaussian, extracted from its characteristic function. -/
lemma gaussian_cosine_integral (v : ℝ≥0) (x : ℝ) :
    ∫ s, Real.cos (x * s) ∂gaussianReal 0 v = Real.exp (-(v : ℝ) * x ^ 2 / 2) := by
  have hi : Integrable (fun s : ℝ => Complex.exp ((x * s : ℝ) * Complex.I))
      (gaussianReal 0 v) := by
    apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
    filter_upwards [] with s
    simp [Complex.norm_exp]
  simp only [Complex.ofReal_mul] at hi
  have h := congrArg Complex.re (charFun_gaussianReal (μ := 0) (v := v) x)
  rw [charFun_apply_real] at h
  have hre : (∫ s, Complex.exp ((x : ℂ) * (s : ℂ) * Complex.I) ∂gaussianReal 0 v).re =
      ∫ s, (Complex.exp ((x : ℂ) * (s : ℂ) * Complex.I)).re ∂gaussianReal 0 v :=
    (integral_re hi).symm
  rw [hre] at h
  simpa [Complex.exp_re, Complex.mul_re, Complex.mul_im, ← Complex.ofReal_pow, mul_assoc, neg_div] using h

/-- The jump density used in (B.2) gives an actual `LSymCert`, including its support. -/
theorem isLSym_one_sub_exp (u : ℝ) (hu : 0 ≤ u) :
    IsLSym (fun x : ℝ => 1 - Real.exp (-u * x ^ 2)) := by
  let v : ℝ≥0 := ⟨2 * u, by positivity⟩
  let μ := gaussianReal 0 v
  refine ⟨{
    A := 0
    A_nonneg := le_rfl
    ν := positiveFold μ
    ν_pos := bot_le
    ν_support := positiveFold_support μ
    ν_integrable := levyIntegrable_of_finite _
    apply_eq := ?_ }⟩
  intro x
  rw [zero_mul, zero_add, integral_positiveFold]
  have hi : Integrable (fun s : ℝ => Real.cos (x * s)) μ := by
    apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
    filter_upwards [] with s
    simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (x * s)
  rw [integral_sub (integrable_const _) hi, integral_const,
    gaussian_cosine_integral]
  simp only [μ, v, measureReal_univ_eq_one, smul_eq_mul, one_mul]
  change 1 - Real.exp (-u * x ^ 2) = 1 - Real.exp (-(2 * u) * x ^ 2 / 2)
  congr 2
  ring


/-- The exact centred Gaussian second moment, needed in the Lévy integrability bound. -/
lemma gaussian_second_moment (v : ℝ≥0) :
    ∫ z : ℝ, z ^ 2 ∂gaussianReal 0 v = (v : ℝ) := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa only [integral_id_gaussianReal, sub_zero] using h

lemma gaussian_integrable_sq (v : ℝ≥0) :
    Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 v) := by
  exact (memLp_id_gaussianReal 2).integrable_sq

/-- The moment bound in the proof of (B.2), on a fixed standard Gaussian space. -/
lemma gaussian_scaled_min_bound (u : ℝ) (hu : 0 ≤ u) :
    (∫ z : ℝ, min ((Real.sqrt (2 * u) * |z|) ^ 2) 1 ∂gaussianReal 0 1) ≤
      2 * min u 1 := by
  have heq (z : ℝ) : (Real.sqrt (2 * u) * |z|) ^ 2 = 2 * u * z ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity), sq_abs]
  simp_rw [heq]
  have hi : Integrable (fun z : ℝ => min (2 * u * z ^ 2) 1) (gaussianReal 0 1) := by
    apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (by positivity) zero_le_one)]
    exact min_le_right _ _
  have hmass : (∫ z : ℝ, min (2 * u * z ^ 2) 1 ∂gaussianReal 0 1) ≤ 1 := by
    have h := integral_mono hi (integrable_const (1 : ℝ)) (fun z => min_le_right (2 * u * z ^ 2) 1)
    simpa using h
  have hmoment : (∫ z : ℝ, min (2 * u * z ^ 2) 1 ∂gaussianReal 0 1) ≤ 2 * u := by
    have h := integral_mono hi ((gaussian_integrable_sq 1).const_mul (2 * u))
      (fun z => min_le_left (2 * u * z ^ 2) 1)
    rw [integral_const_mul, gaussian_second_moment] at h
    simpa using h
  by_cases hu1 : u ≤ 1
  · rw [min_eq_left hu1]
    exact hmoment
  · rw [min_eq_right (le_of_not_ge hu1)]
    linarith

end Paper02.Bernstein
