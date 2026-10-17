import Paper14.AppendixStripIntersection
import Paper14.AppendixSecondGeometry

open MeasureTheory Set
open scoped ENNReal
namespace Paper14
noncomputable section

/-- The actual normalized intersection-area estimate in (25). -/
theorem appendix_strip_intersection_bound {n p q p' q' : ℕ} (hn : 0 < n)
    {α : ℝ} (hα : 0 < α) (hαs : α < 1/32)
    (hq : 0 < q) (hqq : q < q') (hq'n : q' ≤ 4*n) :
    (m (appendixStrip (1-α/(n : ℝ)) p q ∩
      appendixStrip (1-α/(n : ℝ)) p' q')).toReal ≤
      5*(α/(n : ℝ))^2/(2*((q' : ℝ)-q)) := by
  let S := appendixStrip (1-α/(n : ℝ)) p q ∩ appendixStrip (1-α/(n : ℝ)) p' q'
  have hΔ : 0 < (q' : ℝ)-q := sub_pos.mpr (by exact_mod_cast hqq)
  by_cases hne : S.Nonempty
  · obtain ⟨hDlo,hDup⟩ := appendix_intersection_determinant hn hα hαs hq hqq hq'n hne
    have hD : 0 < (p' : ℝ)*q-(p : ℝ)*q' := lt_of_lt_of_le (mul_pos (by norm_num) hΔ) hDlo
    have hε0 : 0 ≤ α/(n : ℝ) := by positivity
    have hsub : S ⊆ {x : ℝ × ℝ | 1-α/(n : ℝ) < (q : ℝ)*x.2-(p : ℝ)*x.1 ∧
        (q : ℝ)*x.2-(p : ℝ)*x.1 ≤ 1 ∧ 1-α/(n : ℝ) < (q' : ℝ)*x.2-(p' : ℝ)*x.1 ∧
        (q' : ℝ)*x.2-(p' : ℝ)*x.1 ≤ 1} := by
      intro x hx
      exact ⟨hx.1.2.1,hx.1.2.2,hx.2.2.1,hx.2.2.2⟩
    have hm : m S ≤ ENNReal.ofReal (2*((α/(n : ℝ))^2/((p' : ℝ)*q-(p : ℝ)*q'))) := by
      change (2 : ℝ≥0∞)*(volume.restrict Omega) S ≤ _
      calc
        _ ≤ 2*volume {x : ℝ × ℝ | 1-α/(n : ℝ) < (q : ℝ)*x.2-(p : ℝ)*x.1 ∧
            (q : ℝ)*x.2-(p : ℝ)*x.1 ≤ 1 ∧ 1-α/(n : ℝ) < (q' : ℝ)*x.2-(p' : ℝ)*x.1 ∧
            (q' : ℝ)*x.2-(p' : ℝ)*x.1 ≤ 1} :=
          mul_le_mul_left' ((Measure.restrict_le_self S).trans (measure_mono hsub)) _
        _ = _ := by
          rw [volume_two_strips _ _ _ _ _ hε0 hD.ne',abs_of_pos hD,ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
    have hmR := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
    rw [ENNReal.toReal_ofReal (by positivity)] at hmR
    apply hmR.trans
    rw [show 2*((α/(n : ℝ))^2/((p' : ℝ)*q-(p : ℝ)*q')) =
      (2*(α/(n : ℝ))^2)/((p' : ℝ)*q-(p : ℝ)*q') by ring]
    apply (div_le_div_iff₀ hD (mul_pos (by norm_num) hΔ)).mpr
    have hh := mul_le_mul_of_nonneg_right hDlo (sq_nonneg (α/(n : ℝ)))
    nlinarith
  · have hS : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    change (m S).toReal ≤ _
    rw [hS,measure_empty,ENNReal.toReal_zero]
    positivity

end
end Paper14
