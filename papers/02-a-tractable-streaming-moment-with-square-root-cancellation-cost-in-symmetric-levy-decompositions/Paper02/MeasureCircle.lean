import Paper02.MeasureDual
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.MeasureTheory.Group.AddCircle

noncomputable section
open MeasureTheory Real
namespace Paper02.LSym

instance angleMeasurableSpace : MeasurableSpace Real.Angle := borel Real.Angle
instance angleBorelSpace : BorelSpace Real.Angle := ⟨rfl⟩

/-- The paper's second-difference measure on `ℝ/(2πℤ)`. -/
def circleMeasure {g : ℝ → ℝ} (c : LSymCert g) : Measure Real.Angle :=
  (certMeasure c).map ((↑) : ℝ → Real.Angle)

instance circleMeasure_finite {g : ℝ → ℝ} (c : LSymCert g) : IsFiniteMeasure (circleMeasure c) := by
  unfold circleMeasure
  infer_instance

lemma circleMeasure_mass {g : ℝ → ℝ} (c : LSymCert g) :
    circleMeasure c Set.univ = ENNReal.ofReal (g 1) := by
  rw [circleMeasure, Measure.map_apply Real.Angle.continuous_coe.measurable MeasurableSet.univ,
    Set.preimage_univ, certMeasure_mass]

lemma circleMeasure_secondDiff {g : ℝ → ℝ} (c : LSymCert g) (k : ℤ) :
    secondDiff (RestrictInt g) k =
      ∫ t : Real.Angle, Real.Angle.cos (k • t) ∂circleMeasure c := by
  rw [circleMeasure, integral_map_of_stronglyMeasurable Real.Angle.continuous_coe.measurable
    (show StronglyMeasurable (fun t : Real.Angle => Real.Angle.cos (k • t)) from
      (Real.Angle.continuous_cos.comp (continuous_id.zsmul k)).stronglyMeasurable)]
  simp only [← Real.Angle.coe_zsmul, Real.Angle.cos_coe, zsmul_eq_mul]
  exact certMeasure_secondDiff c k

/-- Lemma 2.1 with the exact original circle, arbitrary jump measures, and total mass. -/
theorem positive_second_difference_measure {g : ℝ → ℝ} (hg : IsLSym g) :
    ∃ μ : Measure Real.Angle, IsFiniteMeasure μ ∧ μ Set.univ = ENNReal.ofReal (g 1) ∧
      ∀ k : ℤ, secondDiff (RestrictInt g) k =
        ∫ t : Real.Angle, Real.Angle.cos (k • t) ∂μ := by
  rcases hg with ⟨c⟩
  exact ⟨circleMeasure c, inferInstance, circleMeasure_mass c, circleMeasure_secondDiff c⟩

/-- The normalized generators of Remark 2.3. -/
def normalizedGenerator (k : ℤ) (t : Real.Angle) : ℝ := by
  classical
  exact if t = 0 then (k : ℝ) ^ 2 else
    (1 - Real.Angle.cos (k • t)) / (1 - Real.Angle.cos t)

lemma angle_cos_eq_one_iff (t : Real.Angle) : Real.Angle.cos t = 1 ↔ t = 0 := by
  rw [← Real.Angle.cos_zero, Real.Angle.cos_eq_iff_eq_or_eq_neg]
  simp

lemma normalizedGenerator_measurable (k : ℤ) : Measurable (normalizedGenerator k) := by
  unfold normalizedGenerator
  apply Measurable.ite (measurableSet_singleton 0) measurable_const
  exact (measurable_const.sub (Real.Angle.continuous_cos.comp
    (continuous_id.zsmul k)).measurable).div
      (measurable_const.sub Real.Angle.continuous_cos.measurable)

lemma normalizedGenerator_weight (k : ℤ) (s : ℝ) :
    (1 - Real.cos s) * normalizedGenerator k (s : Real.Angle) =
      1 - Real.cos ((k : ℝ) * s) := by
  have hk : Real.cos ((k : ℝ) * s) = Real.Angle.cos (k • (s : Real.Angle)) := by
    rw [← Real.Angle.coe_zsmul, Real.Angle.cos_coe, zsmul_eq_mul]
  rw [hk, ← Real.Angle.cos_coe s]
  by_cases hs : (s : Real.Angle) = 0
  · simp [normalizedGenerator, hs]
  · have hc : 1 - Real.Angle.cos (s : Real.Angle) ≠ 0 := by
      intro h
      exact hs ((angle_cos_eq_one_iff _).mp (by linarith))
    simp only [normalizedGenerator, if_neg hs]
    exact mul_div_cancel₀ _ hc

lemma normalizedGenerator_representation {g : ℝ → ℝ} (c : LSymCert g) (k : ℤ) :
    g (k : ℝ) = ∫ t : Real.Angle, normalizedGenerator k t ∂circleMeasure c := by
  have hw : Integrable (fun s : ℝ => 1 - Real.cos s) (c.ν.restrict (Set.Ioi (0 : ℝ))) := by
    simpa using (integrable_levy_kernel c.ν_integrable 1).restrict
  haveI := isFiniteMeasure_withDensity_ofReal hw.hasFiniteIntegral
  have hi : Integrable (fun s : ℝ => normalizedGenerator k (s : Real.Angle))
      ((c.ν.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun s => ENNReal.ofReal (1 - Real.cos s))) := by
    rw [integrable_withDensity_iff_integrable_smul' (by fun_prop)
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simp_rw [ENNReal.toReal_ofReal (one_sub_cos_nonneg _), smul_eq_mul, normalizedGenerator_weight]
    exact (integrable_levy_kernel c.ν_integrable _).restrict
  rw [circleMeasure, integral_map_of_stronglyMeasurable Real.Angle.continuous_coe.measurable
    (normalizedGenerator_measurable k).stronglyMeasurable,
    certMeasure, integral_add_measure
      ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top) hi,
    integral_smul_measure, integral_dirac,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (one_sub_cos_nonneg _), smul_eq_mul, normalizedGenerator_weight]
  simpa [normalizedGenerator, c.A_nonneg] using c.apply_eq (k : ℝ)

lemma circleMeasure_eq_zero_of_one_eq_zero {g : ℝ → ℝ} (c : LSymCert g) (h : g 1 = 0) :
    circleMeasure c = 0 := by
  apply Measure.measure_univ_eq_zero.mp
  simp [circleMeasure_mass, h]

/-- The degenerate assertion of Remark 2.3 holds at every integer. -/
lemma integer_zero_of_one_zero {g : ℝ → ℝ} (hg : IsLSym g) (h : g 1 = 0) (k : ℤ) :
    g (k : ℝ) = 0 := by
  rcases hg with ⟨c⟩
  rw [normalizedGenerator_representation c k, circleMeasure_eq_zero_of_one_eq_zero c h]
  simp

/-- The normalized representing measure is a probability measure. -/
lemma normalized_probability {g : ℝ → ℝ} (c : LSymCert g) (h : 0 < g 1) :
    IsProbabilityMeasure ((ENNReal.ofReal (g 1))⁻¹ • circleMeasure c) := by
  constructor
  rw [Measure.smul_apply, smul_eq_mul, circleMeasure_mass]
  exact ENNReal.inv_mul_cancel (by simpa using h) ENNReal.ofReal_ne_top

/-- The probability-mixture conclusion of Remark 2.3. -/
theorem normalized_probability_mixture {g : ℝ → ℝ} (hg : IsLSym g) (h : 0 < g 1) :
    ∃ μ : Measure Real.Angle, IsProbabilityMeasure μ ∧
      ∀ k : ℤ, g (k : ℝ) / g 1 = ∫ t, normalizedGenerator k t ∂μ := by
  rcases hg with ⟨c⟩
  refine ⟨(ENNReal.ofReal (g 1))⁻¹ • circleMeasure c, normalized_probability c h, ?_⟩
  intro k
  rw [integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_ofReal h.le,
    smul_eq_mul, ← normalizedGenerator_representation c k]
  ring

lemma cert_support_positive {g : ℝ → ℝ} (c : LSymCert g) :
    c.ν.restrict (Set.Ioi (0 : ℝ)) = c.ν := by
  have h := Measure.restrict_add_restrict_compl (μ := c.ν) (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi
  simpa only [Set.compl_Ioi, c.ν_support, add_zero] using h

/-- In the zero-mass case the Gaussian coefficient vanishes and the whole
jump measure is concentrated on positive multiples of `2π`. -/
lemma cert_zero_mass_concentration {g : ℝ → ℝ} (c : LSymCert g) (h : g 1 = 0) :
    c.A = 0 ∧ ∀ᵐ s ∂c.ν, ∃ n : ℤ, 0 < n ∧ (n : ℝ) * (2 * Real.pi) = s := by
  have hw := integrable_levy_kernel c.ν_integrable 1
  simp only [one_mul] at hw
  have he := cert_one c
  rw [h, cert_support_positive] at he
  have hI : 0 ≤ ∫ s, (1 - Real.cos s) ∂c.ν := integral_nonneg one_sub_cos_nonneg
  have hA : c.A = 0 := by linarith [c.A_nonneg]
  refine ⟨hA, ?_⟩
  have hzero : (fun s : ℝ => 1 - Real.cos s) =ᵐ[c.ν] 0 :=
    (integral_eq_zero_iff_of_nonneg one_sub_cos_nonneg hw).mp (by linarith)
  have hpos : ∀ᵐ s ∂c.ν, 0 < s := by
    have hh := ae_restrict_mem (μ := c.ν) (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi
    rwa [cert_support_positive] at hh
  filter_upwards [hzero, hpos] with s hs hsp
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff s).mp (by simpa using sub_eq_zero.mp hs |>.symm)
  refine ⟨n, ?_, hn⟩
  have hnpos : 0 < (n : ℝ) := (mul_pos_iff_of_pos_right (by positivity : 0 < 2 * Real.pi)).mp (hn ▸ hsp)
  exact_mod_cast hnpos

lemma normalizedGenerator_zero (t : Real.Angle) : normalizedGenerator 0 t = 0 := by
  classical
  simp [normalizedGenerator]

lemma normalizedGenerator_one (t : Real.Angle) : normalizedGenerator 1 t = 1 := by
  classical
  by_cases ht : t = 0
  · simp [normalizedGenerator, ht]
  · have hc : 1 - Real.Angle.cos t ≠ 0 := by
      intro h
      exact ht ((angle_cos_eq_one_iff _).mp (by linarith))
    simp [normalizedGenerator, ht, hc]

lemma normalizedGenerator_neg (k : ℤ) (t : Real.Angle) :
    normalizedGenerator (-k) t = normalizedGenerator k t := by
  classical
  simp [normalizedGenerator]

lemma normalizedGenerator_recurrence (n : ℕ) (t : Real.Angle) :
    normalizedGenerator (n + 2 : ℤ) t =
      2 * Real.Angle.cos ((n + 1 : ℤ) • t) +
        2 * normalizedGenerator (n + 1 : ℤ) t - normalizedGenerator n t := by
  classical
  induction t using Real.Angle.induction_on with | h s =>
    by_cases hs : (s : Real.Angle) = 0
    · simp only [hs, normalizedGenerator, if_true, Int.cast_add, Int.cast_natCast,
        Int.cast_ofNat, zsmul_zero, Real.Angle.cos_zero]
      ring
    · have hw : 1 - Real.cos s ≠ 0 := by
        intro h
        exact hs ((angle_cos_eq_one_iff _).mp (by
          rw [Real.Angle.cos_coe]
          linarith))
      have hD := Paper02.secondDiff_cos s (n + 1 : ℤ)
      rw [Paper02.secondDiff_eq] at hD
      have h0 := normalizedGenerator_weight (n : ℤ) s
      have h1 := normalizedGenerator_weight (n + 1 : ℤ) s
      have h2 := normalizedGenerator_weight (n + 2 : ℤ) s
      have hc : Real.Angle.cos ((n + 1 : ℤ) • (s : Real.Angle)) =
          Real.cos (((n + 1 : ℤ) : ℝ) * s) := by
        rw [← Real.Angle.coe_zsmul, Real.Angle.cos_coe, zsmul_eq_mul]
      rw [hc]
      apply (mul_left_cancel₀ hw)
      have hi : (n + 1 : ℤ) - 1 = n := by omega
      rw [hi] at hD
      change (1 - Real.cos ((((n + 2 : ℤ) : ℝ)) * s) -
        2 * (1 - Real.cos ((((n + 1 : ℤ) : ℝ)) * s)) +
        (1 - Real.cos ((n : ℝ) * s))) / 2 = _ at hD
      norm_num only [Int.cast_add, Int.cast_natCast, Int.cast_one, Int.cast_ofNat] at hD h0 h1 h2 ⊢
      nlinarith

lemma normalizedGenerator_continuous_nat (n : ℕ) :
    Continuous (normalizedGenerator (n : ℤ)) := by
  induction n using Nat.twoStepInduction with
  | zero =>
    have he : normalizedGenerator 0 = (fun _ : Real.Angle => (0 : ℝ)) :=
      funext normalizedGenerator_zero
    simpa only [Int.natCast_zero, he] using
      (continuous_const : Continuous (fun _ : Real.Angle => (0 : ℝ)))
  | one =>
    have he : normalizedGenerator 1 = (fun _ : Real.Angle => (1 : ℝ)) :=
      funext normalizedGenerator_one
    simpa only [Int.natCast_one, he] using
      (continuous_const : Continuous (fun _ : Real.Angle => (1 : ℝ)))
  | more n h0 h1 =>
    have he : normalizedGenerator (n + 2 : ℤ) = fun t : Real.Angle =>
        2 * Real.Angle.cos ((n + 1 : ℤ) • t) +
          2 * normalizedGenerator (n + 1 : ℤ) t - normalizedGenerator n t := by
      funext t
      exact normalizedGenerator_recurrence n t
    push_cast
    rw [he]
    exact ((continuous_const.mul (Real.Angle.continuous_cos.comp (continuous_id.zsmul _))).add
      (continuous_const.mul (by simpa using h1))).sub h0

/-- In particular the exceptional value `K₀(k)=k²` is the continuous limit. -/
lemma normalizedGenerator_continuous (k : ℤ) : Continuous (normalizedGenerator k) := by
  cases k with
  | ofNat n => exact normalizedGenerator_continuous_nat n
  | negSucc n =>
    have he : normalizedGenerator (Int.negSucc n) = normalizedGenerator (n + 1 : ℤ) := by
      funext t
      exact normalizedGenerator_neg (n + 1 : ℤ) t
    rw [he]
    simpa using normalizedGenerator_continuous_nat (n + 1)

end Paper02.LSym
