import Paper20.PartitionContent
import Paper20.ConjugateHooks

namespace Paper20
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem sum_flatMap_nat {α : Type*} (xs : List α) (f : α → List ℕ) :
    (xs.flatMap f).sum = (xs.map (fun x => (f x).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih, List.sum_append]

theorem sum_map_range_nat (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

theorem nuOf_eq_boxes_sum (ps : List ℕ) :
    nuOf ps = ((boxesOf ps).map Prod.fst).sum := by
  unfold nuOf boxesOf
  rw [foldl_acc_sum, zero_add, List.map_flatMap, sum_flatMap_nat]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  rcases p with ⟨a,i⟩
  dsimp only
  rw [List.map_map]
  simp only [Function.comp_def]
  rw [sum_map_range_nat]
  simp [Nat.mul_comm]

namespace Part
variable {n : ℕ}

/-- Conjugating the actual partition changes the sign of its actual content. -/
@[simp] theorem contentOf_transpose (p : Part n) :
    contentOf p.transpose.parts = -contentOf p.parts := by
  rw [contentOf_eq_boxes_sum, contentOf_eq_boxes_sum]
  have hp := (p.boxes_transpose_perm.map (fun c => (c.2:ℤ)-(c.1:ℤ))).sum_eq
  rw [List.map_map] at hp
  calc
    _ = ((boxesOf p.parts).map (fun c => (c.1:ℤ)-(c.2:ℤ))).sum := hp
    _ = ((boxesOf p.parts).map (fun c => -((c.2:ℤ)-(c.1:ℤ)))).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro c hc
      ring
    _ = _ := sum_neg_map _ _

theorem nuOf_transpose_boxes (p : Part n) :
    nuOf p.transpose.parts = ((boxesOf p.parts).map Prod.snd).sum := by
  rw [nuOf_eq_boxes_sum]
  have hp := (p.boxes_transpose_perm.map Prod.fst).sum_eq
  simpa only [List.map_map, Function.comp_def, Prod.fst_swap] using hp

/-- The content identity used in (14) and (21), for the same executable
nu and content functions as the Hilbert partition sum. -/
theorem contentOf_eq_nu_difference (p : Part n) :
    contentOf p.parts = (nuOf p.transpose.parts:ℤ)-(nuOf p.parts:ℤ) := by
  rw [contentOf_eq_boxes_sum, nuOf_transpose_boxes, nuOf_eq_boxes_sum]
  have hs : ∀ xs : List (ℕ × ℕ),
      (xs.map (fun c => (c.2:ℤ)-(c.1:ℤ))).sum =
        ((xs.map Prod.snd).sum:ℤ)-((xs.map Prod.fst).sum:ℤ) := by
    intro xs
    induction xs with
    | nil => simp
    | cons c xs ih => simp only [List.map_cons, List.sum_cons, Nat.cast_add, ih]; ring
  exact hs _

end Part
end Paper20
