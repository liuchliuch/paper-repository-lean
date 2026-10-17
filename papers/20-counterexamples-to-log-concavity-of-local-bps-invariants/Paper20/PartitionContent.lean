import Paper20.Boxes

namespace Paper20
open Finset
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem foldl_acc_sum {α M : Type*} [AddMonoid M] (f : α → M)
    (xs : List α) (z : M) :
    xs.foldl (fun acc x => acc+f x) z = z+(xs.map f).sum := by
  induction xs generalizing z with
  | nil => simp
  | cons x xs ih => simp [ih, add_assoc]

theorem contentOf_eq_rows (ps : List ℕ) : contentOf ps =
    (ps.zipIdx.map (fun (a,i) => ((a*(a-1)/2:ℕ):ℤ)-((i*a:ℕ):ℤ))).sum := by
  unfold contentOf
  simp only [sub_eq_add_neg, add_assoc]
  rw [foldl_acc_sum, zero_add]

theorem sum_map_range_int (f : ℕ → ℤ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

theorem sum_flatMap_int {α : Type*} (xs : List α) (f : α → List ℤ) :
    (xs.flatMap f).sum = (xs.map (fun x => (f x).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih, List.sum_append]

theorem content_row_sum (a i : ℕ) :
    ((List.range a).map (fun j : ℕ => (j:ℤ)-(i:ℤ))).sum =
      ((a*(a-1)/2:ℕ):ℤ)-((i*a:ℕ):ℤ) := by
  rw [sum_map_range_int, Finset.sum_sub_distrib]
  have hs : (∑ j ∈ range a, (j:ℤ)) = ((a*(a-1)/2:ℕ):ℤ) := by
    rw [← Nat.cast_sum, Finset.sum_range_id]
  rw [hs]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

/-- The content in the actual partition algorithm is the sum of column
minus row over precisely the mathematical Young-diagram boxes. -/
theorem contentOf_eq_boxes_sum (ps : List ℕ) : contentOf ps =
    ((boxesOf ps).map (fun c => (c.2:ℤ)-(c.1:ℤ))).sum := by
  rw [contentOf_eq_rows]
  unfold boxesOf
  rw [List.map_flatMap, sum_flatMap_int]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  rcases p with ⟨a,i⟩
  dsimp only
  rw [List.map_map]
  exact (content_row_sum a i).symm

theorem sum_neg_map {α : Type*} (f : α → ℤ) (xs : List α) :
    (xs.map (fun x => -f x)).sum = -(xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, add_comm]

end Paper20
