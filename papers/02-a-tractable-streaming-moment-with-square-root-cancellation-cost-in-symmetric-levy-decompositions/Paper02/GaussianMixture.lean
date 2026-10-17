import Paper02.BernsteinSubordination
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Prod

noncomputable section
namespace Paper02.Bernstein
open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal

/-- A measurable Gaussian family, realized by scaling one fixed standard Gaussian. -/
def scaledGaussian (u : ℝ) : Measure ℝ :=
  (gaussianReal 0 1).map (fun z : ℝ => Real.sqrt (2 * u) * z)

instance scaledGaussian_probability (u : ℝ) : IsProbabilityMeasure (scaledGaussian u) := by
  unfold scaledGaussian
  exact Measure.isProbabilityMeasure_map (by fun_prop)

lemma scaledGaussian_measurable : Measurable scaledGaussian := by
  have hj : Measurable (fun p : ℝ × ℝ => Real.sqrt (2 * p.1) * p.2) := by fun_prop
  have hm := (Measure.measurable_map _ hj).comp
    (Measurable.map_prodMk_left (ν := gaussianReal (0 : ℝ) 1) (α := ℝ))
  convert hm using 1
  funext u
  simp only [Function.comp_apply]
  rw [Measure.map_map hj (by fun_prop)]
  rfl

lemma scaledGaussian_eq (u : ℝ) (hu : 0 ≤ u) :
    scaledGaussian u = gaussianReal 0 ⟨2 * u, by positivity⟩ := by
  unfold scaledGaussian
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · apply NNReal.eq
    simp only [NNReal.coe_mk, mul_one]
    exact Real.sq_sqrt (by positivity)

/-- The complete nonnegative Gaussian mixture, before its zero atom is removed. -/
def gaussianMixture (μ : Measure ℝ) : Measure ℝ := μ.bind scaledGaussian

/-- Its positive jump measure, constructed from the actual Gaussian mixture. -/
def gaussianLevyMeasure (μ : Measure ℝ) : Measure ℝ := positiveFold (gaussianMixture μ)

lemma gaussianLevyMeasure_support (μ : Measure ℝ) :
    (gaussianLevyMeasure μ).restrict (Iic 0) = 0 := positiveFold_support _

/-- Folding preserves every even nonnegative measurable function vanishing at zero. -/
lemma lintegral_positiveFold (μ : Measure ℝ) (F : ℝ → ℝ≥0∞) (hF : Measurable F)
    (hzero : F 0 = 0) (heven : ∀ z, F |z| = F z) :
    ∫⁻ s, F s ∂positiveFold μ = ∫⁻ s, F s ∂μ := by
  unfold positiveFold
  rw [← lintegral_indicator measurableSet_Ioi,
    lintegral_map (hF.indicator measurableSet_Ioi) (by fun_prop)]
  apply lintegral_congr
  intro z
  by_cases hz : z = 0
  · subst z
    simp [hzero]
  · rw [indicator_of_mem (show |z| ∈ Ioi (0 : ℝ) from abs_pos.mpr hz)]
    exact heven z

lemma lintegral_gaussianLevyMeasure (μ : Measure ℝ) (F : ℝ → ℝ≥0∞) (hF : Measurable F)
    (hzero : F 0 = 0) (heven : ∀ z, F |z| = F z) :
    ∫⁻ s, F s ∂gaussianLevyMeasure μ = ∫⁻ u, ∫⁻ s, F s ∂scaledGaussian u ∂μ := by
  rw [gaussianLevyMeasure, lintegral_positiveFold _ _ hF hzero heven,
    gaussianMixture, Measure.lintegral_bind scaledGaussian_measurable.aemeasurable hF.aemeasurable]

lemma gaussianLevyMeasure_integrable (μ : Measure ℝ)
    (hpos : ∀ᵐ u ∂μ, 0 ≤ u) (hμ : Integrable (fun u : ℝ => min u 1) μ) :
    LevyIntegrable (gaussianLevyMeasure μ) := by
  unfold LevyIntegrable
  rw [lintegral_gaussianLevyMeasure _ _ (by fun_prop) (by simp)
    (fun z => by simp)]
  have hinner : ∀ᵐ u ∂μ,
      (∫⁻ s, ENNReal.ofReal (min (s ^ 2) 1) ∂scaledGaussian u) ≤
        ENNReal.ofReal (2 * min u 1) := by
    filter_upwards [hpos] with u hu
    rw [scaledGaussian, lintegral_map (by fun_prop) (by fun_prop)]
    have hi : Integrable (fun z : ℝ => min ((Real.sqrt (2 * u) * z) ^ 2) 1)
        (gaussianReal 0 1) := by
      apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
      filter_upwards [] with z
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (sq_nonneg _) zero_le_one)]
      exact min_le_right _ _
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (fun z => le_min (sq_nonneg _) zero_le_one))]
    apply ENNReal.ofReal_le_ofReal
    have he : (fun z : ℝ => min ((Real.sqrt (2 * u) * z) ^ 2) 1) =
        (fun z : ℝ => min ((Real.sqrt (2 * u) * |z|) ^ 2) 1) := by
      funext z
      simp only [mul_pow, sq_abs]
    rw [he]
    exact gaussian_scaled_min_bound u hu
  refine lt_of_le_of_lt (lintegral_mono_ae hinner) ?_
  apply (lintegral_ofReal_ne_top_iff_integrable
    (hμ.const_mul 2).aestronglyMeasurable ?_).mpr (hμ.const_mul 2) |>.lt_top
  filter_upwards [hpos] with u hu
  exact mul_nonneg (by norm_num) (le_min hu zero_le_one)

lemma scaledGaussian_lintegral_kernel (u : ℝ) (hu : 0 ≤ u) (x : ℝ) :
    ∫⁻ s, ENNReal.ofReal (1 - Real.cos (x * s)) ∂scaledGaussian u =
      ENNReal.ofReal (1 - Real.exp (-u * x ^ 2)) := by
  rw [scaledGaussian_eq u hu]
  have hi : Integrable (fun s : ℝ => Real.cos (x * s))
      (gaussianReal 0 ⟨2 * u, by positivity⟩) := by
    apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
    filter_upwards [] with s
    simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (x * s)
  have hj : Integrable (fun s : ℝ => 1 - Real.cos (x * s))
      (gaussianReal 0 ⟨2 * u, by positivity⟩) := (integrable_const _).sub hi
  rw [← ofReal_integral_eq_lintegral_ofReal hj
    (Filter.Eventually.of_forall (fun s => Paper02.LSym.one_sub_cos_nonneg _)),
    integral_sub (integrable_const _) hi, integral_const, gaussian_cosine_integral]
  simp only [measureReal_univ_eq_one, smul_eq_mul, one_mul, NNReal.coe_mk]
  congr 3
  ring

/-- Tonelli's identity for the jump kernel of an arbitrary positive Gaussian mixture. -/
lemma gaussianLevyMeasure_kernel (μ : Measure ℝ) (hpos : ∀ᵐ u ∂μ, 0 ≤ u) (x : ℝ) :
    ∫ s in Ioi (0 : ℝ), (1 - Real.cos (x * s)) ∂gaussianLevyMeasure μ =
      ∫ u, (1 - Real.exp (-u * x ^ 2)) ∂μ := by
  rw [gaussianLevyMeasure, integral_positiveFold]
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun s => Paper02.LSym.one_sub_cos_nonneg _)) (by fun_prop),
    gaussianMixture, Measure.lintegral_bind scaledGaussian_measurable.aemeasurable (by fun_prop)]
  have he : (fun u => ∫⁻ s, ENNReal.ofReal (1 - Real.cos (x * s)) ∂scaledGaussian u) =ᵐ[μ]
      (fun u => ENNReal.ofReal (1 - Real.exp (-u * x ^ 2))) := by
    filter_upwards [hpos] with u hu
    exact scaledGaussian_lintegral_kernel u hu x
  rw [lintegral_congr_ae he, integral_eq_lintegral_of_nonneg_ae ?_ (by fun_prop)]
  filter_upwards [hpos] with u hu
  exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hu (sq_nonneg x)]))

/-- Gaussian subordination for every positive Bernstein jump measure obeying
its original first-moment-at-zero integrability condition. -/
theorem isLSym_gaussian_mixture (μ : Measure ℝ)
    (hpos : ∀ᵐ u ∂μ, 0 ≤ u) (hμ : Integrable (fun u : ℝ => min u 1) μ) :
    IsLSym (fun x : ℝ => ∫ u, (1 - Real.exp (-u * x ^ 2)) ∂μ) := by
  refine ⟨{
    A := 0
    A_nonneg := le_rfl
    ν := gaussianLevyMeasure μ
    ν_pos := bot_le
    ν_support := gaussianLevyMeasure_support μ
    ν_integrable := gaussianLevyMeasure_integrable μ hpos hμ
    apply_eq := ?_ }⟩
  intro x
  rw [zero_mul, zero_add, gaussianLevyMeasure_kernel μ hpos]

end Paper02.Bernstein
