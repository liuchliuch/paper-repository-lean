import Paper08.RationalProgram

/-! # Concrete expression trees for the rational recurrence and exponentiation -/

open scoped BigOperators
namespace Paper08.RationalRecurrenceProgram
open RationalProgram

/-- A computable finite sum, in list order. -/
def sumList : List Expr → Expr
  | [] => .atom 0
  | x :: xs => .node .add x (sumList xs)

lemma eval_sumList (xs : List Expr) : (sumList xs).eval = (xs.map Expr.eval).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [sumList, Expr.eval, Op.eval, List.map_cons, List.sum_cons, ih]

lemma operations_sumList (xs : List Expr) :
    (sumList xs).operations = (xs.map (fun x => x.operations + 1)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [sumList, Expr.operations, List.map_cons, List.sum_cons, ih]; omega

lemma inputHeight_sumList_le (xs : List Expr) (B : ℕ) (hB : 1 ≤ B)
    (h : ∀ x ∈ xs, x.inputHeight ≤ B) : (sumList xs).inputHeight ≤ B := by
  induction xs with
  | nil => simpa [sumList, Expr.inputHeight, height] using hB
  | cons x xs ih =>
    exact max_le (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

/-- `Fin n` enumeration avoids noncomputable choice of a finite-set list. -/
def finSum {n : ℕ} (f : Fin n → Expr) : Expr := sumList (List.ofFn f)

lemma eval_finSum {n : ℕ} (f : Fin n → Expr) :
    (finSum f).eval = ∑ i, (f i).eval := by
  rw [finSum, eval_sumList, List.map_ofFn, List.sum_ofFn]
  rfl

lemma operations_finSum {n : ℕ} (f : Fin n → Expr) :
    (finSum f).operations = ∑ i, ((f i).operations + 1) := by
  rw [finSum, operations_sumList, List.map_ofFn, List.sum_ofFn]
  rfl

lemma inputHeight_finSum_le {n : ℕ} (f : Fin n → Expr) (B : ℕ) (hB : 1 ≤ B)
    (h : ∀ i, (f i).inputHeight ≤ B) : (finSum f).inputHeight ≤ B := by
  apply inputHeight_sumList_le _ _ hB
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact h i

lemma height_natCast_le {j s : ℕ} (hj : j ≤ s) : height (j : ℚ) ≤ s + 1 := by
  unfold height
  simp only [Rat.num_natCast, Int.natAbs_natCast, Rat.den_natCast]
  apply max_le
  · apply Nat.size_le.mpr
    exact lt_of_le_of_lt (Nat.le_succ_of_le hj) (s + 1).lt_two_pow_self
  · simp

/-- The complete uncached recurrence as an arithmetic expression. The input
moments are arbitrary expression trees, so callers substitute the actual
quadrature/multinomial programs, rather than merely their answers. -/
def recurrenceExpr (M : ℕ → Expr) (j : ℕ) : Expr :=
  if h : j = 0 then .atom 0 else
    .node .sub (M j)
      (.node .mul (.node .div (.atom 1) (.atom (j : ℚ)))
        (finSum (fun i : Fin j =>
          .node .mul (.node .mul (.atom (i.val : ℚ)) (recurrenceExpr M i.val)) (M (j - i.val)))))
termination_by j
decreasing_by exact i.isLt

/-- Value equality with the original executable recurrence. -/
theorem eval_recurrenceExpr (M : ℕ → Expr) (j : ℕ) :
    (recurrenceExpr M j).eval = Moments.rationalLogCoeff (fun i => (M i).eval) j := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    rw [recurrenceExpr, Moments.rationalLogCoeff]
    split_ifs with hj
    · rfl
    · simp only [Expr.eval, Op.eval, eval_finSum, ih _ (Fin.isLt _)]

/-- Actual expression size, including every repeated occurrence of each
moment subprogram, is exponentially bounded in the recurrence order. -/
theorem operations_recurrenceExpr_le (M : ℕ → Expr) (s j N : ℕ) (hj : j ≤ s)
    (hM : ∀ k, 1 ≤ k → k ≤ s → (M k).operations ≤ N) :
    (recurrenceExpr M j).operations ≤ (N + 1) * BitComplexity.recurrenceOperationCount j := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    by_cases hj0 : j = 0
    · subst j
      rw [recurrenceExpr, BitComplexity.recurrenceOperationCount]
      simp [Expr.operations]
    have hjp : 1 ≤ j := by omega
    have ht : ∀ i : Fin j,
        (recurrenceExpr M i.val).operations + (M (j - i.val)).operations + 3 ≤
          (N + 1) * (BitComplexity.recurrenceOperationCount i.val + 4) := by
      intro i
      have hh := ih i.val i.isLt (by omega)
      have hm := hM (j - i.val) (by have := i.isLt; omega) (by omega)
      nlinarith
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin j))) => ht i)
    have hm := hM j hjp hj
    rw [recurrenceExpr, dif_neg hj0]
    simp only [Expr.operations, operations_finSum]
    rw [BitComplexity.recurrenceOperationCount, dif_neg hj0, Nat.mul_add, Finset.mul_sum]
    simp only [Nat.zero_add]
    have he : (∑ i : Fin j, ((recurrenceExpr M i.val).operations + 1 + (M (j - i.val)).operations + 1 + 1)) =
        ∑ i : Fin j, ((recurrenceExpr M i.val).operations + (M (j - i.val)).operations + 3) := by
      apply Finset.sum_congr rfl
      intro i _
      omega
    rw [he]
    nlinarith

/-- Leaf encoding lengths are controlled by the actual moment subprograms
and by the small integer indices introduced by the recurrence. -/
theorem inputHeight_recurrenceExpr_le (M : ℕ → Expr) (s j B : ℕ) (hj : j ≤ s)
    (hB : s + 2 ≤ B) (hM : ∀ k, 1 ≤ k → k ≤ s → (M k).inputHeight ≤ B) :
    (recurrenceExpr M j).inputHeight ≤ B := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    by_cases hj0 : j = 0
    · subst j
      rw [recurrenceExpr]
      simp [Expr.inputHeight, height]
      omega
    rw [recurrenceExpr, dif_neg hj0]
    simp only [Expr.inputHeight]
    apply max_le (hM j (by omega) hj)
    apply max_le
    · apply max_le
      · simpa [height] using (show 1 ≤ B by omega)
      · exact (height_natCast_le hj).trans (by omega)
    · apply inputHeight_finSum_le _ B (by omega)
      intro i
      apply max_le
      · apply max_le
        · exact (height_natCast_le (show i.val ≤ s by have := i.isLt; omega)).trans (by omega)
        · exact ih i.val i.isLt (by omega)
      · exact hM (j - i.val) (by have := i.isLt; omega) (by omega)

/-- Polynomial-in-expression-size arithmetic work for the fully substituted
uncached recurrence, with no assumed cost certificate. -/
theorem work_recurrenceExpr_le (M : ℕ → Expr) (s j N B : ℕ) (hj : j ≤ s)
    (hB : s + 2 ≤ B) (hMops : ∀ k, 1 ≤ k → k ≤ s → (M k).operations ≤ N)
    (hMbits : ∀ k, 1 ≤ k → k ≤ s → (M k).inputHeight ≤ B) :
    (recurrenceExpr M j).work ≤
      ((N + 1) * 2 ^ (j + 4)) *
        (4 * ((B + 2) * ((N + 1) * 2 ^ (j + 4) + 1)) + 3) ^ 3 := by
  let K := (N + 1) * 2 ^ (j + 4)
  have ho : (recurrenceExpr M j).operations ≤ K := by
    apply (operations_recurrenceExpr_le M s j N hj hMops).trans
    exact Nat.mul_le_mul_left (N + 1) (by have := BitComplexity.recurrenceOperationCount_le j; omega)
  have hi := inputHeight_recurrenceExpr_le M s j B hj hB hMbits
  apply (Expr.work_le _).trans
  apply Nat.mul_le_mul ho
  apply Nat.pow_le_pow_left _ 3
  gcongr

/-- A literal repeated multiplication expression, suitable even for the
final power `2^h = O(n)`. -/
def power (x : Expr) : ℕ → Expr
  | 0 => .atom 1
  | n + 1 => .node .mul x (power x n)

lemma eval_power (x : Expr) (n : ℕ) : (power x n).eval = x.eval ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [power, Expr.eval, Op.eval, ih, pow_succ]; ring

lemma operations_power (x : Expr) (n : ℕ) : (power x n).operations = n * (x.operations + 1) := by
  induction n with
  | zero => simp [power, Expr.operations]
  | succ n ih => simp only [power, Expr.operations, ih]; ring

lemma inputHeight_power_le (x : Expr) (n B : ℕ) (hB : 1 ≤ B) (hx : x.inputHeight ≤ B) :
    (power x n).inputHeight ≤ B := by
  induction n with
  | zero => simpa [power, Expr.inputHeight, height] using hB
  | succ n ih => exact max_le hx ih

/-- Factorials are represented by actual integer multiplications as well. -/
def factorial : ℕ → Expr
  | 0 => .atom 1
  | n + 1 => .node .mul (.atom ((n + 1 : ℕ) : ℚ)) (factorial n)

lemma eval_factorial (n : ℕ) : (factorial n).eval = (Nat.factorial n : ℚ) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [factorial, Expr.eval, Op.eval, ih, Nat.factorial_succ, Nat.cast_mul]

lemma operations_factorial (n : ℕ) : (factorial n).operations = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [factorial, Expr.operations, ih]; omega

lemma inputHeight_factorial_le (n : ℕ) : (factorial n).inputHeight ≤ n + 2 := by
  induction n with
  | zero => simp [factorial, Expr.inputHeight, height]
  | succ n ih =>
    apply max_le
    · exact (height_natCast_le (show n + 1 ≤ n + 1 by omega)).trans (by omega)
    · omega

/-- Finite Taylor exponentiation with a substituted argument expression. -/
def expPolynomialExpr (t : Expr) (N : ℕ) : Expr :=
  finSum (fun j : Fin (N + 1) => .node .div (power t j.val) (factorial j.val))

lemma eval_expPolynomialExpr (t : Expr) (N : ℕ) :
    (expPolynomialExpr t N).eval = Algorithm.expPolynomial t.eval N := by
  simp only [expPolynomialExpr, eval_finSum, Expr.eval, Op.eval, eval_power, eval_factorial]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => t.eval ^ j / (Nat.factorial j : ℚ))]
  rfl

lemma operations_expPolynomialExpr_le (t : Expr) (N : ℕ) :
    (expPolynomialExpr t N).operations ≤ (N + 1) * ((N + 1) * (t.operations + 2) + 2) := by
  rw [expPolynomialExpr, operations_finSum]
  calc
    _ ≤ ∑ _j : Fin (N + 1), ((N + 1) * (t.operations + 2) + 2) := by
      apply Finset.sum_le_sum
      intro j _
      simp only [Expr.operations, operations_power, operations_factorial]
      have hj : j.val ≤ N + 1 := by have := j.isLt; omega
      nlinarith
    _ = _ := by simp [Nat.mul_comm]

lemma inputHeight_expPolynomialExpr_le (t : Expr) (N B : ℕ)
    (ht : t.inputHeight ≤ B) (hB : N + 3 ≤ B) :
    (expPolynomialExpr t N).inputHeight ≤ B := by
  apply inputHeight_finSum_le _ B (by omega)
  intro j
  apply max_le
  · exact inputHeight_power_le t j.val B (by omega) ht
  · exact (inputHeight_factorial_le j.val).trans (by have := j.isLt; omega)

/-- The complete final exponentiation AST computes its degree and scaling
from the value of the substituted argument, exactly as the original program. -/
def rationalExpExpr (L : Expr) (ε : ℚ) : Expr :=
  let h := Algorithm.exponentialScale L.eval
  let a := ε / (12 * (2 : ℚ) ^ h)
  let t := Expr.node .div L (power (.atom 2) h)
  power (expPolynomialExpr t (Algorithm.exponentialDegree a)) (2 ^ h)

/-- Value equality with the actual output construction, including all
computed parameter choices. -/
lemma eval_rationalExpExpr (L : Expr) (ε : ℚ) :
    (rationalExpExpr L ε).eval = Algorithm.rationalExp L.eval ε := by
  simp only [rationalExpExpr, eval_power, eval_expPolynomialExpr, Expr.eval, Op.eval,
    Algorithm.rationalExp]

/-- Complete AST node bound for final exponentiation, including all factorial
and power arithmetic. -/
lemma operations_rationalExpExpr_le (L : Expr) (ε : ℚ) :
    let h := Algorithm.exponentialScale L.eval
    let N := Algorithm.exponentialDegree (ε / (12 * (2 : ℚ) ^ h))
    (rationalExpExpr L ε).operations ≤
      (2 ^ h) * ((N + 1) * ((N + 1) * (L.operations + h + 3) + 2) + 1) := by
  dsimp only [rationalExpExpr]
  rw [operations_power]
  apply Nat.mul_le_mul_left
  have h := operations_expPolynomialExpr_le
    (.node .div L (power (.atom 2) (Algorithm.exponentialScale L.eval)))
    (Algorithm.exponentialDegree (ε / (12 * (2 : ℚ) ^ Algorithm.exponentialScale L.eval)))
  simpa only [Expr.operations, operations_power, Nat.zero_add, Nat.mul_one, Nat.add_assoc] using
    Nat.add_le_add_right h 1

lemma inputHeight_rationalExpExpr_le (L : Expr) (ε : ℚ) (B : ℕ)
    (hL : L.inputHeight ≤ B)
    (hB : Algorithm.exponentialDegree (ε / (12 * (2 : ℚ) ^ Algorithm.exponentialScale L.eval)) + 3 ≤ B) :
    (rationalExpExpr L ε).inputHeight ≤ B := by
  apply inputHeight_power_le _ _ B (by omega)
  apply inputHeight_expPolynomialExpr_le _ _ B _ hB
  apply max_le hL
  apply inputHeight_power_le _ _ B (by omega)
  simp [Expr.inputHeight, height]
  constructor
  · apply Nat.size_le.mpr
    exact lt_of_lt_of_le (by decide : 2 < (2 : ℕ) ^ 2)
      (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ B))
  · omega

end Paper08.RationalRecurrenceProgram
