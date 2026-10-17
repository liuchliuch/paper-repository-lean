import Paper14.AppendixDeterminantCount
import Paper14.AppendixIntersectionBound

open MeasureTheory Set Finset
open scoped ENNReal
namespace Paper14
noncomputable section

lemma appendix_intersection_mem_determinantPairs {n p q p' q' : ℕ} (hn : 0 < n)
    {α : ℝ} (hα : 0 < α) (hαs : α < 1/32)
    (hq : 0 < q) (hqq : q < q') (hq'n : q' ≤ 4*n) (hp : p < 2*q) (hp' : p' < 2*q')
    (hne : (appendixStrip (1-α/(n : ℝ)) p q ∩
      appendixStrip (1-α/(n : ℝ)) p' q').Nonempty) : (p,p') ∈ determinantPairs q q' := by
  obtain ⟨hlo,hup⟩ := appendix_intersection_determinant hn hα hαs hq hqq hq'n hne
  have hΔ : 0 < (q' : ℝ)-q := sub_pos.mpr (by exact_mod_cast hqq)
  have hD : 0 < (p' : ℝ)*q-(p : ℝ)*q' := lt_of_lt_of_le (mul_pos (by norm_num) hΔ) hlo
  have hpos : 0 < pairDet q q' (p,p') := by
    have hh : (0 : ℝ) < ((pairDet q q' (p,p') : ℤ) : ℝ) := by simpa [pairDet] using hD
    exact_mod_cast hh
  have hu : pairDet q q' (p,p') ≤ 4*(q'-q : ℕ) := by
    have hh : ((pairDet q q' (p,p') : ℤ) : ℝ) ≤ ((4*(q'-q : ℕ) : ℕ) : ℝ) := by
      simpa [pairDet,Nat.cast_sub hqq.le] using hup
    exact_mod_cast hh
  exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hp,Finset.mem_range.mpr hp'⟩,hpos,hu⟩

/-- The actual fixed-q,q' sum of intersection measures is bounded by 20ε². -/
theorem appendix_crossMoment {n q q' : ℕ} (hn : 0 < n)
    {α : ℝ} (hα : 0 < α) (hαs : α < 1/32)
    (hq : 0 < q) (hqq : q < q') (hq'n : q' ≤ 4*n) :
    (∑ p ∈ Finset.range (2*q), ∑ p' ∈ Finset.range (2*q'),
      (m (appendixStrip (1-α/(n : ℝ)) p q ∩
        appendixStrip (1-α/(n : ℝ)) p' q')).toReal) ≤ 20*(α/(n : ℝ))^2 := by
  classical
  let f : ℕ × ℕ → ℝ := fun pp => (m (appendixStrip (1-α/(n : ℝ)) pp.1 q ∩
    appendixStrip (1-α/(n : ℝ)) pp.2 q')).toReal
  have heq : (∑ p ∈ Finset.range (2*q), ∑ p' ∈ Finset.range (2*q'),f (p,p')) =
      ∑ pp ∈ determinantPairs q q',f pp := by
    rw [← Finset.sum_product]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro pp hpp hnmem
    have hemp : appendixStrip (1-α/(n : ℝ)) pp.1 q ∩
        appendixStrip (1-α/(n : ℝ)) pp.2 q' = ∅ := by
      apply Set.not_nonempty_iff_eq_empty.mp
      intro hne
      exact hnmem (appendix_intersection_mem_determinantPairs hn hα hαs hq hqq hq'n
        (Finset.mem_range.mp (Finset.mem_product.mp hpp).1)
        (Finset.mem_range.mp (Finset.mem_product.mp hpp).2) hne)
    simp [f,hemp]
  change (∑ p ∈ Finset.range (2*q), ∑ p' ∈ Finset.range (2*q'),f (p,p')) ≤ _
  rw [heq]
  have hΔ : 0 < (q' : ℝ)-q := sub_pos.mpr (by exact_mod_cast hqq)
  calc
    _ ≤ ∑ pp ∈ determinantPairs q q',5*(α/(n : ℝ))^2/(2*((q' : ℝ)-q)) :=
      Finset.sum_le_sum (fun pp _ => appendix_strip_intersection_bound hn hα hαs hq hqq hq'n)
    _ = ((determinantPairs q q').card : ℝ)*(5*(α/(n : ℝ))^2/(2*((q' : ℝ)-q))) := by
      rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ (8*((q' : ℝ)-q))*(5*(α/(n : ℝ))^2/(2*((q' : ℝ)-q))) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hh : ((determinantPairs q q').card : ℝ) ≤ (8*(q'-q : ℕ) : ℕ) := by
        exact_mod_cast determinantPairs_card_le hq
      simpa [Nat.cast_sub hqq.le] using hh
    _ = _ := by field_simp; ring

end
end Paper14
