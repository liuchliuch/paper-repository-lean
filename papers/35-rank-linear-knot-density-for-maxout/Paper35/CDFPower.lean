import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Linarith

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter Function
open scoped Topology ENNReal

/-!
# CDF power normalization

The proof works for every atomless real probability law.  It proves the
probability integral transform using the intermediate value theorem and
measure monotonicity, then integrates a monomial against Lebesgue measure
on the unit interval.  Its density specializations establish (4.6)
without continuity assumptions on the density.
-/

noncomputable section

namespace Paper35.CDFPower

/-- Atomless real probability laws have continuous CDFs. -/
theorem continuous_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ] :
    Continuous (cdf μ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply (monotone_cdf μ).continuousAt_iff_leftLim_eq_rightLim.mpr
  rw [(cdf μ).rightLim_eq]
  have hz : ENNReal.ofReal (cdf μ x - leftLim (cdf μ) x) = 0 := by
    rw [← StieltjesFunction.measure_singleton, measure_cdf, measure_singleton]
  have hle := ENNReal.ofReal_eq_zero.mp hz
  apply le_antisymm ((monotone_cdf μ).leftLim_le le_rfl)
  linarith

lemma exists_cdf_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ]
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : ∃ x : ℝ, cdf μ x = t := by
  obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot μ).eventually_lt_const ht0).exists
  obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop μ).eventually_const_lt ht1).exists
  exact mem_range_of_exists_le_of_exists_ge (continuous_cdf μ)
    ⟨a, ha.le⟩ ⟨b, hb.le⟩

/-- The CDF of its own value has the uniform CDF on the unit interval. -/
theorem cdf_map_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ]
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    cdf (μ.map (cdf μ)) t = t := by
  let ν := μ.map (cdf μ)
  have hm : Measurable (cdf μ) := (continuous_cdf μ).measurable
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_map hm.aemeasurable
  have hlo : t ≤ cdf ν t := by
    rcases eq_or_lt_of_le ht0 with hzero | hpos
    · subst t
      exact cdf_nonneg ν 0
    · obtain ⟨a, ha⟩ := exists_cdf_eq μ hpos ht1
      have hsub : Iic a ⊆ (cdf μ) ⁻¹' Iic t := by
        intro x hx
        exact (monotone_cdf μ hx).trans ha.le
      calc
        t = μ.real (Iic a) := by rw [← cdf_eq_real μ, ha]
        _ ≤ μ.real ((cdf μ) ⁻¹' Iic t) := measureReal_mono hsub
        _ = cdf ν t := by rw [cdf_eq_real, map_measureReal_apply hm measurableSet_Iic]
  have hhi : cdf ν t ≤ t := by
    by_contra h
    have hp : t < cdf ν t := lt_of_not_ge h
    let s := (t + cdf ν t) / 2
    have hts : t < s := by dsimp [s]; linarith
    have hsp : s < cdf ν t := by dsimp [s]; linarith
    have hs0 : 0 < s := lt_of_le_of_lt ht0 hts
    have hs1 : s < 1 := hsp.trans_le (cdf_le_one ν t)
    obtain ⟨a, ha⟩ := exists_cdf_eq μ hs0 hs1
    have hsub : (cdf μ) ⁻¹' Iic t ⊆ Iic a := by
      intro x hx
      by_contra hxa
      have hax : a ≤ x := le_of_not_ge hxa
      have hfx : cdf μ a ≤ cdf μ x := monotone_cdf μ hax
      have hxt : cdf μ x ≤ t := hx
      rw [ha] at hfx
      linarith
    have hbound : cdf ν t ≤ s := by
      calc
        cdf ν t = μ.real ((cdf μ) ⁻¹' Iic t) := by
          rw [cdf_eq_real, map_measureReal_apply hm measurableSet_Iic]
        _ ≤ μ.real (Iic a) := measureReal_mono hsub
        _ = s := by rw [← cdf_eq_real μ, ha]
    linarith
  exact le_antisymm hhi hlo

/-- Probability integral transform for atomless real laws. -/
theorem map_cdf_eq_unitInterval (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ] :
    μ.map (cdf μ) = volume.restrict (Icc (0 : ℝ) 1) := by
  have hm : Measurable (cdf μ) := (continuous_cdf μ).measurable
  letI : IsProbabilityMeasure (μ.map (cdf μ)) := isProbabilityMeasure_map hm.aemeasurable
  apply Measure.ext_of_Iic
  intro t
  have hset : Iic t ∩ Icc (0 : ℝ) 1 = Icc 0 (min t 1) := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Icc, le_min_iff]
    tauto
  rw [Measure.restrict_apply measurableSet_Iic, hset, Real.volume_Icc, sub_zero]
  by_cases ht0 : t < 0
  · have he : (cdf μ) ⁻¹' Iic t = ∅ := by
      ext x
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
      exact not_le.mpr (ht0.trans_le (cdf_nonneg μ x))
    rw [Measure.map_apply hm measurableSet_Iic, he, measure_empty]
    simp [min_eq_left (ht0.le.trans zero_le_one), ENNReal.ofReal_eq_zero.mpr ht0.le]
  · have ht0 : 0 ≤ t := le_of_not_gt ht0
    by_cases ht1 : t < 1
    · rw [← ofReal_cdf, cdf_map_cdf μ ht0 ht1, min_eq_left ht1.le]
    · have ht1 : 1 ≤ t := le_of_not_gt ht1
      have he : (cdf μ) ⁻¹' Iic t = univ := by
        ext x
        simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
        exact (cdf_le_one μ x).trans ht1
      rw [Measure.map_apply hm measurableSet_Iic, he, measure_univ, min_eq_right ht1,
        ENNReal.ofReal_one]

/-- The CDF power has the exact `1/(n+1)` expectation under every
atomless real probability law. -/
theorem integral_cdf_pow (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ] (n : ℕ) :
    (∫ y : ℝ, cdf μ y ^ n ∂μ) = 1 / (n + 1 : ℝ) := by
  have hm : Measurable (cdf μ) := (continuous_cdf μ).measurable
  calc
    (∫ y : ℝ, cdf μ y ^ n ∂μ) = ∫ t : ℝ, t ^ n ∂μ.map (cdf μ) :=
      (integral_map hm.aemeasurable
        ((measurable_id.pow_const n).aestronglyMeasurable)).symm
    _ = ∫ t in Icc (0 : ℝ) 1, t ^ n := by rw [map_cdf_eq_unitInterval]
    _ = ∫ t in (0 : ℝ)..1, t ^ n := by
      rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le zero_le_one]
    _ = 1 / (n + 1 : ℝ) := by simp

/-- Equation (4.6) for a genuine arbitrary Lebesgue probability density.
The density need only be integrable and nonnegative; no continuity or
pointwise derivative hypothesis is imposed. -/
theorem integral_cdf_pow_mul_density {h : ℝ → ℝ}
    (hhi : Integrable h volume) (hh0 : ∀ y, 0 ≤ h y)
    (hh1 : ∫ y, h y = 1) (n : ℕ) :
    let μ := volume.withDensity (fun y => ENNReal.ofReal (h y))
    (∫ y : ℝ, cdf μ y ^ n * h y) = 1 / (n + 1 : ℝ) := by
  let μ := volume.withDensity (fun y => ENNReal.ofReal (h y))
  have hμ : IsProbabilityMeasure μ := by
    constructor
    change (volume.withDensity (fun y => ENNReal.ofReal (h y))) univ = 1
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hhi (Eventually.of_forall hh0), hh1,
      ENNReal.ofReal_one]
  letI := hμ
  have hnorm := integral_cdf_pow μ n
  change (∫ y : ℝ, cdf μ y ^ n * h y) = _
  change (∫ y : ℝ, cdf μ y ^ n ∂volume.withDensity (fun y => ENNReal.ofReal (h y))) = _ at hnorm
  rw [integral_withDensity_eq_integral_toReal_smul₀
    hhi.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at hnorm
  simpa only [ENNReal.toReal_ofReal (hh0 _), smul_eq_mul, mul_comm] using hnorm

/-- The same normalization as an extended nonnegative integral of actual
CDF masses, suitable for the kernel expression in (4.1). -/
theorem lintegral_cdf_pow (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ] (n : ℕ) :
    (∫⁻ y : ℝ, μ (Iic y) ^ n ∂μ) = (n + 1 : ℝ≥0∞)⁻¹ := by
  have hi : Integrable (fun y : ℝ => cdf μ y ^ n) μ := by
    apply (integrable_const (1 : ℝ)).mono'
      (((monotone_cdf μ).measurable.pow_const n).aestronglyMeasurable)
    exact Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (cdf_nonneg μ y) n)]
      exact pow_le_one₀ (cdf_nonneg μ y) (cdf_le_one μ y)
  calc
    (∫⁻ y : ℝ, μ (Iic y) ^ n ∂μ) = ∫⁻ y : ℝ, ENNReal.ofReal (cdf μ y ^ n) ∂μ := by
      apply lintegral_congr
      intro y
      rw [ENNReal.ofReal_pow (cdf_nonneg μ y), ofReal_cdf]
    _ = ENNReal.ofReal (∫ y : ℝ, cdf μ y ^ n ∂μ) :=
      (ofReal_integral_eq_lintegral_ofReal hi
        (Eventually.of_forall fun y => pow_nonneg (cdf_nonneg μ y) n)).symm
    _ = (n + 1 : ℝ≥0∞)⁻¹ := by
      rw [integral_cdf_pow, ENNReal.ofReal_div_of_pos (by positivity)]
      rw [ENNReal.ofReal_add (Nat.cast_nonneg n) zero_le_one]
      simp

lemma densityLaw_isProbability {h : ℝ → ℝ}
    (hhi : Integrable h volume) (hh0 : ∀ y, 0 ≤ h y)
    (hh1 : ∫ y, h y = 1) :
    IsProbabilityMeasure (volume.withDensity (fun y => ENNReal.ofReal (h y))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hhi (Eventually.of_forall hh0), hh1,
    ENNReal.ofReal_one]

/-- A probability density's CDF is exactly its lower-half-line integral. -/
theorem cdf_densityLaw_eq_setIntegral {h : ℝ → ℝ}
    (hhi : Integrable h volume) (hh0 : ∀ y, 0 ≤ h y)
    (hh1 : ∫ y, h y = 1) (y : ℝ) :
    cdf (volume.withDensity (fun t => ENNReal.ofReal (h t))) y =
      ∫ t in Iic y, h t := by
  letI := densityLaw_isProbability hhi hh0 hh1
  rw [cdf_eq_real, ← setIntegral_one_eq_measureReal]
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    hhi.aestronglyMeasurable.aemeasurable.ennreal_ofReal.restrict
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
    (fun _ => (1 : ℝ)) measurableSet_Iic]
  simp_rw [ENNReal.toReal_ofReal (hh0 _), smul_eq_mul, mul_one]

/-- Equation (4.6), with the CDF written directly as the integral of the
density over `(-∞,y]`. -/
theorem integral_lowerIntegral_pow_mul_density {h : ℝ → ℝ}
    (hhi : Integrable h volume) (hh0 : ∀ y, 0 ≤ h y)
    (hh1 : ∫ y, h y = 1) (n : ℕ) :
    (∫ y : ℝ, (∫ t in Iic y, h t) ^ n * h y) = 1 / (n + 1 : ℝ) := by
  have heq (y : ℝ) := cdf_densityLaw_eq_setIntegral hhi hh0 hh1 y
  simpa only [heq] using integral_cdf_pow_mul_density hhi hh0 hh1 n

/-- The density-weighted version of (4.6) in `ℝ≥0∞`. -/
theorem lintegral_cdf_pow_mul_density {h : ℝ → ℝ}
    (hhi : Integrable h volume) (hh0 : ∀ y, 0 ≤ h y)
    (hh1 : ∫ y, h y = 1) (n : ℕ) :
    let μ := volume.withDensity (fun y => ENNReal.ofReal (h y))
    (∫⁻ y : ℝ, μ (Iic y) ^ n * ENNReal.ofReal (h y)) = (n + 1 : ℝ≥0∞)⁻¹ := by
  let μ := volume.withDensity (fun y => ENNReal.ofReal (h y))
  letI := densityLaw_isProbability hhi hh0 hh1
  have heq : Measurable (fun y : ℝ => μ (Iic y) ^ n) := by
    have hm := (((monotone_cdf μ).measurable.ennreal_ofReal).pow_const n)
    simpa only [ofReal_cdf] using hm
  have hnorm := lintegral_cdf_pow μ n
  change (∫⁻ y : ℝ, μ (Iic y) ^ n * ENNReal.ofReal (h y)) = _
  change (∫⁻ y : ℝ, μ (Iic y) ^ n ∂volume.withDensity (fun y => ENNReal.ofReal (h y))) = _ at hnorm
  rw [lintegral_withDensity_eq_lintegral_mul₀
    hhi.aestronglyMeasurable.aemeasurable.ennreal_ofReal heq.aemeasurable] at hnorm
  simpa only [Pi.mul_apply, mul_comm] using hnorm

/-- The full CDF power normalization for any nonnegative Lebesgue density
of mass one, in the extended nonnegative formulation of the source model.
Only almost-everywhere measurability is required. -/
theorem lintegral_cdf_mass_pow_mul_density {h : ℝ → ℝ≥0∞}
    (hhm : AEMeasurable h volume) (hh1 : ∫⁻ y, h y = 1) (n : ℕ) :
    let μ := volume.withDensity h
    (∫⁻ y : ℝ, μ (Iic y) ^ n * h y) = (n + 1 : ℝ≥0∞)⁻¹ := by
  let μ := volume.withDensity h
  letI : IsProbabilityMeasure μ := by
    constructor
    change (volume.withDensity h) univ = 1
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hh1]
  have heq : Measurable (fun y : ℝ => μ (Iic y) ^ n) := by
    have hm := (((monotone_cdf μ).measurable.ennreal_ofReal).pow_const n)
    simpa only [ofReal_cdf] using hm
  have hnorm := lintegral_cdf_pow μ n
  change (∫⁻ y : ℝ, μ (Iic y) ^ n * h y) = _
  change (∫⁻ y : ℝ, μ (Iic y) ^ n ∂volume.withDensity h) = _ at hnorm
  rw [lintegral_withDensity_eq_lintegral_mul₀ hhm heq.aemeasurable] at hnorm
  simpa only [Pi.mul_apply, mul_comm] using hnorm

end Paper35.CDFPower
