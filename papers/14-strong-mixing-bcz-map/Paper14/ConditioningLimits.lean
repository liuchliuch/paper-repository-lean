import Paper14.BoundedProductLimits
import Paper14.KacExcess

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal BoundedContinuousFunction
namespace Paper14
noncomputable section

/-- Conditioning on a set of probability close to one changes any bounded
test integral by at most twice its bound times the omitted probability. -/
theorem normalizedRestriction_integral_error {E : Type*} [MeasurableSpace E]
    {μ : Measure E} [IsProbabilityMeasure μ] {Y : Set E}
    (hY : MeasurableSet Y) (hp : 0 < μ Y) {f : E → ℝ} (hf : Measurable f)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ x, ‖f x‖ ≤ K) :
    |(∫ x, f x ∂normalizedRestriction μ Y) - ∫ x, f x ∂μ| ≤ 2*K*μ.real Yᶜ := by
  letI := normalizedRestriction_probability hp.ne'
  have hiY := integrable_of_measurable_bound (μ := normalizedRestriction μ Y) hf K hb
  have hiC := integrable_of_measurable_bound (μ := μ.restrict Yᶜ) hf K hb
  have hmix : μ = μ Y • normalizedRestriction μ Y + μ.restrict Yᶜ := by
    rw [normalizedRestriction,smul_smul,ENNReal.mul_inv_cancel hp.ne' (measure_ne_top μ Y),one_smul]
    exact (Measure.restrict_add_restrict_compl hY).symm
  have hI : (∫ x, f x ∂μ) = (μ Y).toReal * (∫ x, f x ∂normalizedRestriction μ Y) +
      ∫ x, f x ∂μ.restrict Yᶜ := by
    conv_lhs => rw [hmix]
    rw [integral_add_measure (hiY.smul_measure (measure_ne_top μ Y)) hiC,
      integral_smul_measure,smul_eq_mul]
  have hρ : 1-(μ Y).toReal = μ.real Yᶜ := by
    rw [measureReal_compl hY,measureReal_univ_eq_one]
    rfl
  have hYbound : |∫ x, f x ∂normalizedRestriction μ Y| ≤ K := by
    simpa only [Real.norm_eq_abs,measureReal_univ_eq_one,mul_one] using
      norm_integral_le_of_norm_le_const (μ := normalizedRestriction μ Y) (Eventually.of_forall hb)
  have hCbound : |∫ x, f x ∂μ.restrict Yᶜ| ≤ K*μ.real Yᶜ := by
    simpa only [Real.norm_eq_abs,Measure.real,Measure.restrict_apply_univ] using
      norm_integral_le_of_norm_le_const (μ := μ.restrict Yᶜ) (Eventually.of_forall hb)
  rw [hI]
  have heq : (∫ x, f x ∂normalizedRestriction μ Y) -
      ((μ Y).toReal*(∫ x, f x ∂normalizedRestriction μ Y)+(∫ x, f x ∂μ.restrict Yᶜ)) =
      μ.real Yᶜ*(∫ x, f x ∂normalizedRestriction μ Y) - (∫ x, f x ∂μ.restrict Yᶜ) := by
    rw [← hρ]; ring
  rw [heq]
  calc _ ≤ |μ.real Yᶜ*(∫ x, f x ∂normalizedRestriction μ Y)| + |∫ x, f x ∂μ.restrict Yᶜ| := abs_sub _ _
       _ = μ.real Yᶜ*|∫ x, f x ∂normalizedRestriction μ Y| + |∫ x, f x ∂μ.restrict Yᶜ| := by
         rw [abs_mul,abs_of_nonneg measureReal_nonneg]
       _ ≤ μ.real Yᶜ*K + K*μ.real Yᶜ := add_le_add (mul_le_mul_of_nonneg_left hYbound measureReal_nonneg) hCbound
       _ = _ := by ring

/-- The conditioning error tends to zero uniformly over a sequence of
bounded measurable tests. -/
theorem normalizedRestriction_integral_error_tendsto {E : Type*} [MeasurableSpace E]
    {μ : Measure E} [IsProbabilityMeasure μ] (Y : ℕ → Set E)
    (hY : ∀ n, MeasurableSet (Y n)) (hp : ∀ n, 0 < μ (Y n))
    (hρ : Tendsto (fun n => μ.real (Y n)) atTop (𝓝 1))
    (f : ℕ → E → ℝ) (hf : ∀ n, Measurable (f n)) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ n x, ‖f n x‖ ≤ K) :
    Tendsto (fun n => (∫ x, f n x ∂normalizedRestriction μ (Y n)) - ∫ x, f n x ∂μ)
      atTop (𝓝 0) := by
  have hc : Tendsto (fun n => μ.real (Y n)ᶜ) atTop (𝓝 0) := by
    simpa only [measureReal_compl (hY _),measureReal_univ_eq_one,sub_self] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hρ
  have hnorm : Tendsto (fun n => |(∫ x, f n x ∂normalizedRestriction μ (Y n)) - ∫ x, f n x ∂μ|)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => abs_nonneg _) (fun n => normalizedRestriction_integral_error (hY n) (hp n) (hf n) hK (hb n))
    simpa using hc.const_mul (2*K)
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using hnorm)

end
end Paper14
