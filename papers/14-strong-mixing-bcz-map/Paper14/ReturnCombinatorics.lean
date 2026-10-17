import Paper14.InducedReturn
import Mathlib.Data.Set.SymmDiff

/-! Paper Ex10, Ex20, and the pointwise input to (8). -/
open MeasureTheory Filter Set Function
open scoped symmDiff ENNReal
namespace Paper14

lemma firstReturnTime_eq_one {α : Type*} {T : α → α} {Y : Set α} {x : α}
    (hx : T x ∈ Y) : firstReturnTime T Y x = 1 := by
  classical
  letI : DecidablePred (fun k : ℕ => 0 < k ∧ T^[k] x ∈ Y) := Classical.decPred _
  have he : ∃ k, 0 < k ∧ T^[k] x ∈ Y := ⟨1, by simp [hx]⟩
  rw [firstReturnTime_eq_find he]
  apply le_antisymm
  · exact Nat.find_min' he (m := 1) ⟨by omega, by simpa using hx⟩
  · exact Nat.succ_le_iff.mpr (Nat.find_spec he).1

lemma inducedMap_eq_of_next_mem {α : Type*} {T : α → α} {Y : Set α} {x : α}
    (hx : T x ∈ Y) : inducedMap T Y x = T x := by
  simp [inducedMap, firstReturnTime_eq_one hx]

/-- The ordinary time accumulated by the induced orbit gives the same point. -/
theorem induced_iterate_eq {α : Type*} (T : α → α) (Y : Set α) (n : ℕ) (x : α) :
    (inducedMap T Y)^[n] x = T^[Rn T Y n x] x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply', inducedMap, Rn_succ, Nat.add_comm, iterate_add_apply, ← ih]

lemma Rn_succ_left {α : Type*} (T : α → α) (Y : Set α) (n : ℕ) (x : α) :
    Rn T Y (n + 1) x = firstReturnTime T Y x + Rn T Y n (inducedMap T Y x) := by
  induction n with
  | zero => simp [Rn_succ, Rn_zero]
  | succ n ih =>
    rw [Rn_succ T Y (n + 1), ih, Rn_succ]
    simp only [iterate_succ_apply, add_assoc]

/-- If the first and the next return each take one iterate, shifting the
starting point by `T` does not change the time of `n` induced returns. -/
theorem Rn_shift_of_next_mem {α : Type*} {T : α → α} {Y : Set α} {x : α}
    {n : ℕ} (hx : T x ∈ Y) (hn : T ((inducedMap T Y)^[n] x) ∈ Y) :
    Rn T Y n (T x) = Rn T Y n x := by
  have hleft := Rn_succ_left T Y n x
  have hright := Rn_succ T Y n x
  rw [firstReturnTime_eq_one hx, inducedMap_eq_of_next_mem hx] at hleft
  rw [firstReturnTime_eq_one hn] at hright
  omega

/-- The exceptional set used in (8), with the last condition restricted to `Y`. -/
theorem excessLevel_symmDiff_subset {α : Type*} (T : α → α) (Y : Set α) (n j : ℕ) :
    excessLevel T Y n j ∆ (T ⁻¹' excessLevel T Y n j) ⊆
      Yᶜ ∪ T ⁻¹' Yᶜ ∪ (Y ∩ ((inducedMap T Y)^[n]) ⁻¹' (T ⁻¹' Yᶜ)) := by
  intro x hx
  by_contra hbad
  have hgood : x ∈ Y ∧ T x ∈ Y ∧ T ((inducedMap T Y)^[n] x) ∈ Y := by
    simp only [mem_union, mem_inter_iff, mem_compl_iff, mem_preimage,
      not_or, not_and, not_not] at hbad
    exact ⟨hbad.1.1, hbad.1.2, hbad.2 hbad.1.1⟩
  have hR := Rn_shift_of_next_mem hgood.2.1 hgood.2.2
  have hD : excessDn T Y n (T x) = excessDn T Y n x := by
    simp only [excessDn, hR]
  simp only [mem_symmDiff, mem_preimage, mem_excessLevel, hgood.1,
    hgood.2.1, true_and, hD] at hx
  tauto

end Paper14
