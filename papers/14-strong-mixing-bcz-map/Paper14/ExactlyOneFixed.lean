import Paper14.ExactlyOneProbability

open MeasureTheory Set Function Filter Topology
open scoped ENNReal
namespace Paper14
noncomputable section

theorem exactly_one_extra_fixed_of_ergodic (hB : Ergodic B m) :
    ∀ᶠ n : ℕ in atTop, ((1 : ℝ)/51200)/320 ≤
      (m {y ∈ Yr (bczScale n (1/51200)) | Rn B (Yr (bczScale n (1/51200))) n y=n+1}).toReal := by
  let α : ℝ := 1/51200
  let η : ℝ := α/320
  have hα : 0<α := by norm_num [α]
  have hη : 0<η := by positivity
  have hsmall : ∀ᶠ n : ℕ in atTop,mr (bczScale n α)
      {y | Hr (bczScale n α) n y ≤ 3*(n : ℝ) ∨ 4*(n : ℝ) ≤ Hr (bczScale n α) n y} ≤ ENNReal.ofReal η :=
    ((bcz_roof_window_bad_tendsto_zero hB hα).eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hη))).mono (fun _ h => h.le)
  filter_upwards [appendix_oneEvent_positive,hsmall,bczScale_eventually hα,eventually_gt_atTop (0 : ℕ)] with n hvec hbad hr hn
  let r := bczScale n α
  let E := appendixOneEvent n α
  let G := {y ∈ Yr r | Rn B (Yr r) n y=n+1}
  let Bad := {y | Hr r n y ≤ 3*(n : ℝ) ∨ 4*(n : ℝ) ≤ Hr r n y}
  have hr0 : 0<r := by dsimp [r]; linarith [hr.1]
  have hBad : MeasurableSet Bad :=
    (measurableSet_le (measurable_Hr r n) measurable_const).union
      (measurableSet_le measurable_const (measurable_Hr r n))
  have hdom : m (Yr r ∩ Bad) ≤ mr r Bad := by
    rw [mr_eq_normalizedRestriction hr0 hr.2,normalizedRestriction,Measure.smul_apply,smul_eq_mul,
      Measure.restrict_apply hBad,inter_comm]
    have hc : (1 : ℝ≥0∞) ≤ (m (Yr r))⁻¹ := ENNReal.one_le_inv.mpr MeasureTheory.prob_le_one
    exact le_mul_of_one_le_left' hc
  have hbadR : (m (Yr r ∩ Bad)).toReal ≤ η := by
    have hh := hdom.trans hbad
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hh).trans_eq (ENNReal.toReal_ofReal hη.le)
  have hsub : E ⊆ G ∪ (Yr r ∩ Bad) := by
    intro x hx
    have hxY : x ∈ Yr r := ⟨hx.1.1,hx.1.2.2⟩
    by_cases hxBad : x ∈ Bad
    · exact Or.inr ⟨hxY,hxBad⟩
    · left
      have hg : 3*(n : ℝ)<Hr r n x ∧ Hr r n x<4*(n : ℝ) := by
        simpa only [Bad,mem_setOf_eq,not_or,not_le] using hxBad
      exact exactly_one_extra_of_counts_roof hn hr.1 hr.2 hx hg.1 hg.2
  have hsplit : m.real E ≤ m.real G+m.real (Yr r ∩ Bad) :=
    (measureReal_mono hsub).trans (measureReal_union_le _ _)
  change η ≤ (m G).toReal
  change α/160 ≤ (m E).toReal at hvec
  change (m E).toReal ≤ (m G).toReal+(m (Yr r ∩ Bad)).toReal at hsplit
  dsimp [η] at *
  linarith

end
end Paper14
