import Paper20.ConjugateContent

namespace Paper20
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem nuOf_eq_rows (ps : List ℕ) :
    nuOf ps = (ps.zipIdx.map (fun (a,i) => i*a)).sum := by
  unfold nuOf
  rw [foldl_acc_sum, zero_add]

theorem nuOf_cons (a : ℕ) (ps : List ℕ) : nuOf (a::ps) = nuOf ps+ps.sum := by
  rw [nuOf_eq_rows, nuOf_eq_rows, List.zipIdx_cons']
  simp only [List.map_cons, List.sum_cons, zero_mul, zero_add, List.map_map]
  have hs : ∀ xs : List (ℕ × ℕ),
      (xs.map (fun (a,i) => (i+1)*a)).sum =
        (xs.map (fun (a,i) => i*a)).sum+(xs.map Prod.fst).sum := by
    intro xs
    induction xs with
    | nil => simp
    | cons p xs ih => rcases p with ⟨a,i⟩; simp only [List.map_cons, List.sum_cons, ih]; ring
  simpa only [Function.comp_def, Prod.map_apply, id_eq, List.zipIdx_map_fst] using hs ps.zipIdx

/-- The maximum of nu at fixed positive row sum is attained by the column
partition; no symmetric-group dimension formula is used here. -/
theorem nuOf_le_choose_sum (ps : List ℕ) (hp : ∀ a ∈ ps, 0 < a) :
    nuOf ps ≤ Nat.choose ps.sum 2 := by
  induction ps with
  | nil => decide
  | cons a ps ih =>
    have ha : 0 < a := hp a (by simp)
    have hi := ih (fun b hb => hp b (by simp [hb]))
    rw [nuOf_cons, List.sum_cons]
    have hc : Nat.choose (ps.sum+1) 2 = Nat.choose ps.sum 2+ps.sum := by
      have hc := Nat.choose_succ_succ ps.sum 1
      change Nat.choose (ps.sum+1) 2 = Nat.choose ps.sum 1+Nat.choose ps.sum 2 at hc
      rw [Nat.choose_one_right] at hc
      omega
    calc
      _ ≤ Nat.choose ps.sum 2+ps.sum := Nat.add_le_add_right hi _
      _ = Nat.choose (ps.sum+1) 2 := hc.symm
      _ ≤ Nat.choose (a+ps.sum) 2 := Nat.choose_le_choose 2 (by omega)

theorem Part.nuOf_le (p : Part n) : nuOf p.parts ≤ Nat.choose n 2 := by
  simpa only [p.sum_eq] using nuOf_le_choose_sum p.parts p.pos

/-- The second, manifestly nonnegative expression in equation (14), for
the exact shift used by the executable Hilbert partition sum. -/
theorem Part.shiftE_eq (p : Part r) (k : ℕ) :
    shiftE p.parts k (deg r k) =
      ((k*(Nat.choose r 2-nuOf p.parts)+(k+1)*nuOf p.transpose.parts:ℕ):ℤ) := by
  unfold shiftE deg
  rw [p.contentOf_eq_nu_difference]
  push_cast
  rw [Nat.cast_sub p.nuOf_le]
  ring

theorem Part.shiftE_nonnegative (p : Part r) (k : ℕ) :
    0 ≤ shiftE p.parts k (deg r k) := by
  rw [p.shiftE_eq]
  exact Nat.cast_nonneg _

theorem shiftE_nonnegative_of_mem_partitionsOf {r : ℕ} {ps : List ℕ}
    (hp : ps ∈ partitionsOf r) (k : ℕ) : 0 ≤ shiftE ps k (deg r k) := by
  let p : Part r :=
    ⟨ps,((mem_partitionsOf r ps).mp hp).2.1,
      fun a ha => (((mem_partitionsOf r ps).mp hp).2.2 a ha).1,
      ((mem_partitionsOf r ps).mp hp).1⟩
  exact p.shiftE_nonnegative k

end Paper20
