import Paper14.ReturnTime
import Mathlib.MeasureTheory.Integral.Prod

/-! The actual roof integral in (1), including its integrability. -/
open MeasureTheory Measure Filter Set Real
namespace Paper14
noncomputable section

lemma integrable_log_kernel :
    IntegrableOn (fun a : ℝ => -Real.log (1 - a) / a) (Ioo 0 1) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_neg_log_one_sub_div_eq]
  positivity

lemma tauSlice_nonneg (a b : ℝ) : 0 ≤ tauSlice a b := by
  classical
  by_cases h : (a, b) ∈ Omega
  · rw [tauSlice_apply_if, if_pos h]
    exact le_of_lt (tau_pos_on_Omega h)
  · rw [tauSlice_apply_if, if_neg h]

lemma tauSlice_eq_zero_of_not_mem {a : ℝ} (h : a ∉ Ioc (0 : ℝ) 1) :
    tauSlice a = 0 := by
  funext b
  apply indicator_of_notMem
  intro hx
  exact h ⟨hx.1, hx.2.1⟩

lemma integrable_tauSlice {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    Integrable (tauSlice a) := by
  classical
  have heq : tauSlice a = (Ioc (1 - a) 1).indicator (fun b : ℝ => 1 / (a * b)) := by
    funext b
    simp only [tauSlice_apply_if, mem_Omega_iff_of_a a b ha0 ha1, indicator_apply, mem_Ioc]
  rw [heq, integrable_indicator_iff measurableSet_Ioc]
  have hc : ContinuousOn (fun b : ℝ => 1 / (a * b)) (Icc (1 - a) 1) :=
    continuousOn_const.div (continuousOn_const.mul continuousOn_id)
      (fun b hb => mul_ne_zero ha0.ne' (ne_of_gt (by linarith [hb.1])))
  exact hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self

lemma outer_tauSlice :
    (fun a : ℝ => ∫ b, tauSlice a b) =ᵐ[volume]
      (Ioo (0 : ℝ) 1).indicator (fun a => -Real.log (1 - a) / a) := by
  have hne : ∀ᵐ a : ℝ ∂volume, a ≠ 1 :=
    (countable_singleton (1 : ℝ)).ae_notMem volume
  filter_upwards [hne] with a ha
  by_cases h0 : 0 < a
  · by_cases h1 : a < 1
    · rw [indicator_of_mem (show a ∈ Ioo (0 : ℝ) 1 from ⟨h0, h1⟩), integral_tauSlice a h0 h1]
    · have hgt : 1 < a := lt_of_le_of_ne (le_of_not_gt h1) (Ne.symm ha)
      rw [indicator_of_notMem (by simp [not_lt.mpr hgt.le]), integral_tauSlice_of_one_lt a hgt]
  · rw [indicator_of_notMem (by simp [h0]), integral_tauSlice_of_le_zero a (le_of_not_gt h0)]

/-- Integrability of the roof on the actual normalized section measure. -/
theorem integrable_tau : Integrable tau m := by
  have hmeas : Measurable (Omega.indicator tau) := by
    apply Measurable.indicator _ measurableSet_Omega
    unfold tau
    fun_prop
  have hint : Integrable (Omega.indicator tau) (volume : Measure (ℝ × ℝ)) := by
    apply (integrable_prod_iff hmeas.aestronglyMeasurable).mpr
    constructor
    · have hne : ∀ᵐ a : ℝ ∂volume, a ≠ 1 :=
        (countable_singleton (1 : ℝ)).ae_notMem volume
      filter_upwards [hne] with a ha
      by_cases h0 : 0 < a
      · by_cases h1 : a < 1
        · exact integrable_tauSlice h0 h1
        · have heq := tauSlice_eq_zero_of_not_mem (a := a) (by intro hh; exact ha (le_antisymm hh.2 (le_of_not_gt h1)))
          change Integrable (tauSlice a)
          rw [heq]
          exact integrable_zero _ _ _
      · change Integrable (tauSlice a)
        rw [tauSlice_eq_zero_of_not_mem (by simp [h0])]
        exact integrable_zero _ _ _
    · have heq : (fun a : ℝ => ∫ b, ‖Omega.indicator tau (a, b)‖) =
          (fun a => ∫ b, tauSlice a b) := by
        funext a
        apply integral_congr_ae
        exact Eventually.of_forall (fun b => Real.norm_of_nonneg (tauSlice_nonneg a b))
      rw [heq]
      exact (integrable_log_kernel.integrable_indicator measurableSet_Ioo).congr outer_tauSlice.symm
  have hon : IntegrableOn tau Omega := (integrable_indicator_iff measurableSet_Omega).mp hint
  exact hon.smul_measure (by norm_num : (2 : ENNReal) ≠ ⊤)

/-- The mean return time is `π²/3`, with respect to `m`, as in paper (1). -/
theorem integral_tau : (∫ x, tau x ∂m) = π^2 / 3 := by
  have hon : IntegrableOn tau Omega :=
    (integrable_smul_measure (by norm_num : (2 : ENNReal) ≠ 0)
      (by norm_num : (2 : ENNReal) ≠ ⊤)).mp integrable_tau
  have hint := (integrable_indicator_iff measurableSet_Omega).mpr hon
  rw [m, integral_smul_measure, ENNReal.toReal_ofNat, smul_eq_mul,
    ← integral_indicator measurableSet_Omega]
  change 2 * (∫ p : ℝ × ℝ, Omega.indicator tau p ∂(volume.prod volume)) = _
  rw [integral_prod _ hint]
  change 2 * (∫ a, ∫ b, tauSlice a b) = _
  rw [integral_congr_ae outer_tauSlice, integral_indicator measurableSet_Ioo,
    integral_neg_log_one_sub_div_eq]
  ring

end
end Paper14
