import Paper14.PhiRFunctionApproximation

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal
namespace Paper14
noncomputable section

/-- The actual f_r-f section error in (60), before taking its square root. -/
theorem bounded_phiRInv_L2_sq_error {f : ℝ × ℝ → ℂ} (hf : Measurable f) (hb : ∀ x,‖f x‖≤1)
    {α : ℝ} (hα : 0<α) :
    Tendsto (fun n : ℕ => ∫ y,‖f (phiRInv (bczScale n α) y)-f y‖^2 ∂mr (bczScale n α)) atTop (𝓝 0) := by
  apply (tendsto_congr' ?_).mpr (bounded_phiR_L2_sq_error hf hb hα)
  filter_upwards [bczScale_eventually hα] with n hr
  have hr0 : 0<bczScale n α := by linarith [hr.1]
  have hm : Measurable (fun y => ‖f (phiRInv (bczScale n α) y)-f y‖^2) :=
    (((hf.comp (measurable_phiRInv _)).sub hf).norm).pow_const 2
  have hmap := integral_map (μ := m) (measurable_phiR (bczScale n α)).aemeasurable hm.aestronglyMeasurable
  rw [(measurePreserving_phiR _ hr0 hr.2).map_eq] at hmap
  rw [hmap]
  apply integral_congr_ae
  filter_upwards [ae_mem_Omega] with x hx
  rw [phiRInv_phiR hr0 hr.2 hx,norm_sub_rev]

/-- Original normalized-eigenfunction L2 approximation in (60), with actual moving mr. -/
theorem bounded_phiRInv_L2_error {f : ℝ × ℝ → ℂ} (hf : Measurable f) (hb : ∀ x,‖f x‖≤1)
    {α : ℝ} (hα : 0<α) :
    Tendsto (fun n : ℕ => eLpNorm (fun y => f (phiRInv (bczScale n α) y)-f y) 2 (mr (bczScale n α))) atTop (𝓝 0) := by
  have ht := ENNReal.tendsto_ofReal ((bounded_phiRInv_L2_sq_error hf hb hα).rpow_const
    (Or.inr (by norm_num : (0 : ℝ) ≤ 1/2)))
  have ht0 : ENNReal.ofReal ((0 : ℝ)^(1/2 : ℝ))=0 := by norm_num
  rw [ht0] at ht
  apply (tendsto_congr' ?_).mpr ht
  filter_upwards [bczScale_eventually hα] with n hr
  let r := bczScale n α
  have hd : mr r ≤ (4 : ℝ≥0∞) • m := mr_le_four hr.1 hr.2
  letI : IsFiniteMeasure (mr r) := ⟨(hd univ).trans_lt (by simp [Measure.smul_apply,smul_eq_mul])⟩
  have hfn : MemLp (fun y => f (phiRInv r y)-f y) 2 (mr r) := by
    apply MemLp.of_bound ((hf.comp (measurable_phiRInv _)).sub hf).aestronglyMeasurable 2
    filter_upwards [] with y
    change ‖f (phiRInv r y)-f y‖≤2
    exact (norm_sub_le _ _).trans (by nlinarith [hb (phiRInv r y),hb y])
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) hfn]
  norm_num [r]

end
end Paper14
