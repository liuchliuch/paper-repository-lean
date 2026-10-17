import Paper14.CoordinateBounds
import Paper14.SievePeriodTransfer

open MeasureTheory Set Function Filter
open scoped ENNReal
namespace Paper14
noncomputable section

lemma lintegral_sieveAux_swap (M : ℕ) (F : ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F (z.2,z.1) ∂sieveAuxMeasure M) =
      (ENNReal.ofReal (M : ℝ))⁻¹ *
        ∫⁻ c in Ioc (0 : ℝ) (M : ℝ), ∫⁻ θ in Ioc (0 : ℝ) 1, F (c,θ) := by
  rw [sieveAuxMeasure,Measure.prod_smul_right,lintegral_smul_measure]
  change (ENNReal.ofReal (M : ℝ))⁻¹*(∫⁻ z : ℝ × ℝ, F z.swap
    ∂(volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) (M : ℝ)))) = _
  rw [lintegral_prod_swap,lintegral_prod F hF.aemeasurable]

/-- The source density domination behind (18): on c <= K <= M the actual
BCZ coordinate law is at most 2M times the real auxiliary probability. -/
theorem farey_coordinate_truncation_bound (M : ℕ) [hM : Fact (0 < (M : ℝ))]
    {K : ℝ} (hKM : K ≤ M) (F : ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, if cOf x ≤ K then F (cOf x,thetaOf x) else 0 ∂m) ≤
      2*ENNReal.ofReal (M : ℝ)*(∫⁻ z, F (z.2,z.1) ∂sieveAuxMeasure M) := by
  let Fk : ℝ × ℝ → ℝ≥0∞ := fun z => if z.1 ≤ K then F z else 0
  have hFk : Measurable Fk := Measurable.ite (measurableSet_le measurable_fst measurable_const) hF measurable_const
  change (∫⁻ x, Fk (cOf x,thetaOf x) ∂m) ≤ _
  rw [lintegral_farey_coordinates Fk hFk,lintegral_sieveAux_swap M F hF]
  have hcancel (I : ℝ≥0∞) :
      2*ENNReal.ofReal (M : ℝ)*((ENNReal.ofReal (M : ℝ))⁻¹*I) = 2*I := by
    rw [← mul_assoc,mul_assoc 2,ENNReal.mul_inv_cancel
      (ne_of_gt (ENNReal.ofReal_pos.mpr hM.out)) ENNReal.ofReal_ne_top,mul_one]
  rw [hcancel]
  calc
    _ ≤ ∫⁻ c in Ici (1 : ℝ), (Ioc (0 : ℝ) (M : ℝ)).indicator
        (fun c => 2*∫⁻ θ in Ioc (0 : ℝ) 1, F (c,θ)) c := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ici] with c hc
      by_cases hk : c ≤ K
      · have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
        have hcm : c ∈ Ioc (0 : ℝ) (M : ℝ) := ⟨hc0,hk.trans hKM⟩
        rw [indicator_of_mem hcm]
        dsimp only [Fk]
        simp only [if_pos hk]
        have hi : c⁻¹ ≤ 1 := (inv_le_one₀ hc0).mpr hc
        have hp : c⁻¹^3 ≤ 1 := pow_le_one₀ (inv_nonneg.mpr hc0.le) hi
        have hd : ENNReal.ofReal (2*c⁻¹^3) ≤ 2 := by
          simpa using ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2))
        exact mul_le_mul_right' hd _
      · dsimp only [Fk]
        simp only [if_neg hk,lintegral_zero,mul_zero]
        exact zero_le _
    _ ≤ ∫⁻ c : ℝ, (Ioc (0 : ℝ) (M : ℝ)).indicator
        (fun c => 2*∫⁻ θ in Ioc (0 : ℝ) 1, F (c,θ)) c :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _ = _ := by
      rw [lintegral_indicator measurableSet_Ioc,lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]

end
end Paper14
