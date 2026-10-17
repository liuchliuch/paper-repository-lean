import Paper20.GeometricSeries
import Paper20.PartitionShift

namespace Paper20.HilbertSeriesProof
open Paper20.FastHilbert
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

/-- The actual formal-series summand in equation (13). -/
def partitionSummand (r k : ℕ) (ps : List ℕ) : PowerSeries ℚ :=
  PowerSeries.C (dimOf r ps:ℚ)*
    (PowerSeries.X^(shiftE ps k (deg r k)).toNat*(hooksOf ps |>.map hookInverse).prod)

def partitionHilbertSeries (r k : ℕ) : PowerSeries ℚ :=
  ((partitionsOf r).map (partitionSummand r k)).sum

theorem summand_coeff {r : ℕ} {ps : List ℕ} (hp : ps ∈ partitionsOf r)
    (k i : ℕ) (hi : i ≤ deg r k) :
    ((summand r k (deg r k) ps).getD i 0:ℚ) =
      PowerSeries.coeff i (partitionSummand r k ps) := by
  have hpos := shiftE_nonnegative_of_mem_partitionsOf hp k
  let E := (shiftE ps k (deg r k)).toNat
  have hhooks : ∀ a ∈ hooksOf ps, 0 < a := by
    intro a ha
    exact hooksOf_positive_of_mem_partitionsOf hp a ha
  unfold partitionSummand summand
  dsimp only
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  by_cases hd : deg r k < E
  · rw [if_pos (Or.inr hd), getD_replicate_zero, Nat.cast_zero,
      if_neg (by dsimp only [E] at hd; omega)]
    ring
  · rw [if_neg (by dsimp only [E] at hd; omega), getD_append_if, List.length_replicate]
    by_cases hei : i < E
    · rw [if_pos hei, getD_replicate_zero, Nat.cast_zero, if_neg (by omega)]
      ring
    · rw [if_neg hei, getD_map_mul, Nat.cast_mul, if_pos (by omega)]
      rw [series_coeff _ hhooks _ _ (by dsimp only [E] at hd hei; omega)]

lemma addPart_coeff (r k d : ℕ) (H ps : List ℕ) (hH : H.length=d+1)
    (i : ℕ) (hi : i ≤ d) :
    (addPart r k d H ps).getD i 0 = H.getD i 0+(summand r k d ps).getD i 0 := by
  unfold addPart summand
  dsimp only
  split_ifs with h
  · rw [getD_replicate_zero, Nat.add_zero]
  · apply getD_zipAdd
    · omega
    · simp only [List.length_append, List.length_replicate, List.length_map, series_length]
      omega

lemma fold_addPart_coeff (r k d : ℕ) (pss : List (List ℕ)) (H : List ℕ)
    (hH : H.length=d+1) (i : ℕ) (hi : i ≤ d) :
    (pss.foldl (addPart r k d) H).getD i 0 = H.getD i 0+
      (pss.map (fun ps => (summand r k d ps).getD i 0)).sum := by
  induction pss generalizing H with
  | nil => simp
  | cons ps pss ih =>
    rw [List.foldl_cons, ih _ (addPart_length _ _ _ _ _ hH), addPart_coeff _ _ _ _ _ hH i hi]
    simp only [List.map_cons, List.sum_cons]
    omega

/-- The original array program computes the genuine partition sum (13)
through every coefficient required for its BPS extraction. -/
theorem hilbertArray_coeff (r k i : ℕ) (hi : i ≤ deg r k) :
    ((hilbertArray r k).getD i 0:ℚ) = PowerSeries.coeff i (partitionHilbertSeries r k) := by
  rw [← getD_toList, total_correct, total,
    fold_addPart_coeff _ _ _ _ _ (by simp) i hi, getD_replicate_zero, Nat.zero_add]
  unfold partitionHilbertSeries
  rw [map_list_sum, List.map_map]
  rw [Nat.cast_list_sum]
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ps hp
  exact summand_coeff hp k i hi

end
end Paper20.HilbertSeriesProof
