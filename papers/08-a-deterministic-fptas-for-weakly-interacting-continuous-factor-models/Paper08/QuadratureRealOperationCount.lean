import Paper08.QuadratureOperationCount

/-! # Arithmetic operations for the real-valued rule of Lemma 3.1

The local functions here have arbitrary real values. The evaluator samples
their actual lower corners and traverses the finite increment, product, cell,
and level loops. Its operation count equals the existing rational evaluator's
count on a zero table, since that count depends only on the loop indices.
-/
noncomputable section
open scoped BigOperators
namespace Paper08.QuadratureRealOperationCount
open CellGrid

def add (x y : ℝ × ℕ) : ℝ × ℕ := (x.1 + y.1, x.2 + y.2 + 1)
def mul (x y : ℝ × ℕ) : ℝ × ℕ := (x.1 * y.1, x.2 + y.2 + 1)

def sumList : List (ℝ × ℕ) → ℝ × ℕ
  | [] => (0, 0)
  | x :: xs => add x (sumList xs)

def productList : List (ℝ × ℕ) → ℝ × ℕ
  | [] => (1, 0)
  | x :: xs => mul x (productList xs)

@[simp] theorem sumList_value (xs : List (ℝ × ℕ)) :
    (sumList xs).1 = (xs.map Prod.fst).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [sumList, add, ih]

@[simp] theorem productList_value (xs : List (ℝ × ℕ)) :
    (productList xs).1 = (xs.map Prod.fst).prod := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [productList, mul, ih]

@[simp] theorem sumList_cost (xs : List (ℝ × ℕ)) :
    (sumList xs).2 = (xs.map Prod.snd).sum + xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [sumList, add, ih]; omega

@[simp] theorem productList_cost (xs : List (ℝ × ℕ)) :
    (productList xs).2 = (xs.map Prod.snd).sum + xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [productList, mul, ih]; omega

def sumSet {α : Type*} [LinearOrder α] (S : Finset α) (f : α → ℝ × ℕ) : ℝ × ℕ :=
  sumList ((PrimitiveProgram.canonicalList S).map f)

def productSet {α : Type*} [LinearOrder α] (S : Finset α) (f : α → ℝ × ℕ) : ℝ × ℕ :=
  productList ((PrimitiveProgram.canonicalList S).map f)

@[simp] theorem sumSet_value {α : Type*} [LinearOrder α] (S : Finset α) (f : α → ℝ × ℕ) :
    (sumSet S f).1 = ∑ i ∈ S, (f i).1 := by
  rw [sumSet, sumList_value, List.map_map]
  exact (List.sum_toFinset (fun i => (f i).1) (Finset.sort_nodup _ S)).symm.trans (by simp)

@[simp] theorem productSet_value {α : Type*} [LinearOrder α] (S : Finset α) (f : α → ℝ × ℕ) :
    (productSet S f).1 = ∏ i ∈ S, (f i).1 := by
  rw [productSet, productList_value, List.map_map]
  exact (List.prod_toFinset (fun i => (f i).1) (Finset.sort_nodup _ S)).symm.trans (by simp)

@[simp] theorem sumSet_cost {α : Type*} [LinearOrder α] (S : Finset α) (f : α → ℝ × ℕ) :
    (sumSet S f).2 = (∑ i ∈ S, (f i).2) + S.card := by
  rw [sumSet, sumList_cost, List.map_map, List.length_map, PrimitiveProgram.canonicalList_length]
  congr 1
  exact (List.sum_toFinset (fun i => (f i).2) (Finset.sort_nodup _ S)).symm.trans (by simp)

@[simp] theorem productSet_cost {α : Type*} [LinearOrder α] (S : Finset α) (f : α → ℝ × ℕ) :
    (productSet S f).2 = (∑ i ∈ S, (f i).2) + S.card := by
  rw [productSet, productList_cost, List.map_map, List.length_map, PrimitiveProgram.canonicalList_length]
  congr 1
  exact (List.sum_toFinset (fun i => (f i).2) (Finset.sort_nodup _ S)).symm.trans (by simp)

/-- One inverse of an integer dyadic denominator, once per level vector. -/
def prepareWeight {n : ℕ} (levels : Fin n → ℕ) : ℝ × ℕ :=
  let denominator : ℕ := 2 ^ (∑ v, levels v)
  ((denominator : ℝ)⁻¹, 1)

@[simp] theorem prepareWeight_value {n : ℕ} (levels : Fin n → ℕ) :
    (prepareWeight levels).1 = (weightQ levels : ℝ) := by simp [prepareWeight, weightQ]

/-- Evaluate the given real function at its actual lower-corner sample. -/
def sampledStep {n t : ℕ} (scopes : Fin t → Finset (Fin n))
    (f : (i : Fin t) → LocalFunc (scopes i).card) (ν : Fin t → ℕ)
    (z : Grid (commonLevels scopes ν)) (i : Fin t) (l : ℕ) : ℝ :=
  (f i).toFun (Dyadic.corner l (Integral.restrictTo (scopes i) (corner z)))

def countedIncrement {n t : ℕ} (scopes : Fin t → Finset (Fin n))
    (f : (i : Fin t) → LocalFunc (scopes i).card) (ν : Fin t → ℕ)
    (z : Grid (commonLevels scopes ν)) (i : Fin t) : ℝ × ℕ :=
  match ν i with
  | 0 => (sampledStep scopes f ν z i 0, 0)
  | l + 1 => (sampledStep scopes f ν z i (l + 1) - sampledStep scopes f ν z i l, 1)

@[simp] theorem countedIncrement_value {n t : ℕ} (scopes : Fin t → Finset (Fin n))
    (f : (i : Fin t) → LocalFunc (scopes i).card) (ν : Fin t → ℕ)
    (z : Grid (commonLevels scopes ν)) (i : Fin t) :
    (countedIncrement scopes f ν z i).1 = Quadrature.scopedIncrement scopes f i (ν i) (corner z) := by
  unfold countedIncrement Quadrature.scopedIncrement
  generalize h : ν i = l
  cases l <;> rfl

@[simp] theorem countedIncrement_cost {n t : ℕ} (scopes : Fin t → Finset (Fin n))
    (f : (i : Fin t) → LocalFunc (scopes i).card) (ν : Fin t → ℕ)
    (z : Grid (commonLevels scopes ν)) (i : Fin t) :
    (countedIncrement scopes f ν z i).2 = if ν i = 0 then 0 else 1 := by
  unfold countedIncrement
  generalize h : ν i = l
  cases l <;> simp

/-- Prepare one weight and then execute every actual cell product and sum. -/
def countedLevel {n t : ℕ} (scopes : Fin t → Finset (Fin n))
    (f : (i : Fin t) → LocalFunc (scopes i).card) (ν : Fin t → ℕ) : ℝ × ℕ :=
  let w := prepareWeight (commonLevels scopes ν)
  letI := PrimitiveProgram.gridOrder (commonLevels scopes ν)
  let cells := sumSet Finset.univ fun z : Grid (commonLevels scopes ν) =>
    mul (w.1, 0) (productSet Finset.univ (countedIncrement scopes f ν z))
  (cells.1, w.2 + cells.2)

def countedRule {n t : ℕ} (scopes : Fin t → Finset (Fin n))
    (f : (i : Fin t) → LocalFunc (scopes i).card) (J : ℕ) : ℝ × ℕ :=
  letI := PrimitiveProgram.tupleOrder t
  sumSet (TupleCount.boundedTuples t J) (countedLevel scopes f)

@[simp] theorem countedLevel_value {n t : ℕ} (scopes : Fin t → Finset (Fin n))
    (f : (i : Fin t) → LocalFunc (scopes i).card) (ν : Fin t → ℕ) :
    (countedLevel scopes f ν).1 = Integral.cubeIntegral
      (fun x => ∏ i, Quadrature.scopedIncrement scopes f i (ν i) x) := by
  rw [integral_increment_product_eq_cell_sum]
  simp [countedLevel, mul]

/-- The real-sample evaluator computes exactly (3.4), for arbitrary real
local functions, without a rational-valuedness or approximation premise. -/
@[simp] theorem countedRule_value {n t : ℕ} (scopes : Fin t → Finset (Fin n))
    (f : (i : Fin t) → LocalFunc (scopes i).card) (J : ℕ) :
    (countedRule scopes f J).1 = Quadrature.totalLevelRule (Quadrature.scopedIncrement scopes f) J := by
  simp only [countedRule, sumSet_value, countedLevel_value, TupleCount.boundedTuples_eq_totalLevels,
    Quadrature.totalLevelRule]

theorem countedLevel_cost {n t : ℕ} (scopes : Fin t → Finset (Fin n))
    (f : (i : Fin t) → LocalFunc (scopes i).card) (ν : Fin t → ℕ) :
    (countedLevel scopes f ν).2 = 1 + Fintype.card (Grid (commonLevels scopes ν)) *
      ((∑ i : Fin t, if ν i = 0 then 0 else 1) + t + 2) := by
  simp only [countedLevel, sumSet_cost, mul, productSet_cost, countedIncrement_cost,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, prepareWeight, Nat.cast_id]
  ring

/-- Exact numeric independence of the real and rational loop counts. -/
theorem countedRule_cost_eq_zero {n t : ℕ} (scopes : Fin t → Finset (Fin n))
    (f : (i : Fin t) → LocalFunc (scopes i).card) (J : ℕ) :
    (countedRule scopes f J).2 =
      (QuadratureOperationCount.countedRule scopes (fun _ _ _ => 0) J).2 := by
  simp only [countedRule, sumSet_cost, QuadratureOperationCount.countedRule,
    QuadratureOperationCount.sumSet_cost, countedLevel_cost, QuadratureOperationCount.countedLevel_cost]

/-- Lemma 3.1's arithmetic bound with its original arbitrary-real-function
quantifier. The rational count is reused only after proving exact count equality. -/
theorem countedRule_operations {n t r J : ℕ} (scopes : Fin t → Finset (Fin n))
    (hscopes : ∀ i, (scopes i).card ≤ r)
    (f : (i : Fin t) → LocalFunc (scopes i).card) (ht : 1 ≤ t) :
    (countedRule scopes f J).2 ≤ 10 * t * (J + t).choose t * 2 ^ (r * J) := by
  rw [countedRule_cost_eq_zero]
  exact QuadratureOperationCount.countedRule_operations scopes hscopes _ ht

end Paper08.QuadratureRealOperationCount
