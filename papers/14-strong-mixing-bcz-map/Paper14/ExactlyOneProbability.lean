import Paper14.ExactlyOneGeometry
import Paper14.BCZExcessHypotheses

open MeasureTheory Set Function Filter Topology
open scoped ENNReal
namespace Paper14
noncomputable section

lemma bcz_roof_window_bad_tendsto_zero (hB : Ergodic B m) {α : ℝ} (hα : 0<α) :
    Tendsto (fun n : ℕ => mr (bczScale n α)
      {y | Hr (bczScale n α) n y ≤ 3*(n : ℝ) ∨ 4*(n : ℝ) ≤ Hr (bczScale n α) n y}) atTop (𝓝 0) := by
  let δ : ℝ := min (Real.pi^2/3-3) (4-Real.pi^2/3)
  have hpi : Real.pi^2/3<4 := by nlinarith [Real.pi_lt_d2,Real.pi_pos]
  have hδ : 0<δ := lt_min (sub_pos.mpr pi_sq_div_three_gt_three) (sub_pos.mpr hpi)
  have ht := changing_roof_probability hB (fun n => bczScale n α)
    ((bczScale_eventually hα).mono (fun n hn => ⟨by linarith [hn.1],hn.2⟩)) (bczScale_tendsto α) δ hδ
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    (Eventually.of_forall (fun _ => zero_le _))
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  apply measure_mono
  intro y hy
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  have hlo : δ ≤ Real.pi^2/3-3 := min_le_left _ _
  have hup : δ ≤ 4-Real.pi^2/3 := min_le_right _ _
  rcases hy with hy | hy
  · have hq := (div_le_iff₀ hnR).mpr hy
    have habs := neg_le_abs (Hr (bczScale n α) n y/(n : ℝ)-Real.pi^2/3)
    change δ ≤ |Hr (bczScale n α) n y/(n : ℝ)-Real.pi^2/3|
    linarith
  · have hq := (le_div_iff₀ hnR).mpr hy
    have habs := le_abs_self (Hr (bczScale n α) n y/(n : ℝ)-Real.pi^2/3)
    change δ ≤ |Hr (bczScale n α) n y/(n : ℝ)-Real.pi^2/3|
    linarith

/-- Complete original return-count event (22), with its sole remaining background ergodicity input explicit. -/
theorem exactly_one_extra_of_ergodic (hB : Ergodic B m) : ExactlyOneExtraStatement := by
  let α : ℝ := 1/51200
  let η : ℝ := α/320
  have hα : 0<α := by norm_num [α]
  have hη : 0<η := by positivity
  refine ⟨α,η,hα,hη,?_⟩
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
