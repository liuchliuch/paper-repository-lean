import Paper08.PrimitiveProgram

/-! # Field-operation count of the generic total-level quadrature

This evaluator uses an arbitrary rational sample table. A subtraction is
charged for each nonzero-level increment, and the product and both accumulation
loops charge their actually executed rational operations. Each level prepares
its dyadic weight once, using an integer shift and one rational inverse; the
cell loop reuses that value. Integer indexing and bit costs belong to the
separate discrete implementation model.
-/
open scoped BigOperators
namespace Paper08.QuadratureOperationCount
open CellGrid RationalQuadrature

def add (x y : ℚ × ℕ) : ℚ × ℕ := (x.1 + y.1, x.2 + y.2 + 1)
def mul (x y : ℚ × ℕ) : ℚ × ℕ := (x.1 * y.1, x.2 + y.2 + 1)

/-- An actual list traversal, including addition to the initial zero. -/
def sumList : List (ℚ × ℕ) → ℚ × ℕ
  | [] => (0, 0)
  | x :: xs => add x (sumList xs)

/-- An actual list traversal, including multiplication by the initial one. -/
def productList : List (ℚ × ℕ) → ℚ × ℕ
  | [] => (1, 0)
  | x :: xs => mul x (productList xs)

@[simp] theorem sumList_value (xs : List (ℚ × ℕ)) :
    (sumList xs).1 = (xs.map Prod.fst).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [sumList, add, ih]

@[simp] theorem productList_value (xs : List (ℚ × ℕ)) :
    (productList xs).1 = (xs.map Prod.fst).prod := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [productList, mul, ih]

@[simp] theorem sumList_cost (xs : List (ℚ × ℕ)) :
    (sumList xs).2 = (xs.map Prod.snd).sum + xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [sumList, add, ih]; omega

@[simp] theorem productList_cost (xs : List (ℚ × ℕ)) :
    (productList xs).2 = (xs.map Prod.snd).sum + xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [productList, mul, ih]; omega

def sumSet {α : Type*} [LinearOrder α] (S : Finset α) (f : α → ℚ × ℕ) : ℚ × ℕ :=
  sumList ((PrimitiveProgram.canonicalList S).map f)

def productSet {α : Type*} [LinearOrder α] (S : Finset α) (f : α → ℚ × ℕ) : ℚ × ℕ :=
  productList ((PrimitiveProgram.canonicalList S).map f)

@[simp] theorem sumSet_value {α : Type*} [LinearOrder α] (S : Finset α) (f : α → ℚ × ℕ) :
    (sumSet S f).1 = ∑ i ∈ S, (f i).1 := by
  rw [sumSet, sumList_value, List.map_map]
  exact (List.sum_toFinset (fun i => (f i).1) (Finset.sort_nodup _ S)).symm.trans (by simp)

@[simp] theorem productSet_value {α : Type*} [LinearOrder α] (S : Finset α) (f : α → ℚ × ℕ) :
    (productSet S f).1 = ∏ i ∈ S, (f i).1 := by
  rw [productSet, productList_value, List.map_map]
  exact (List.prod_toFinset (fun i => (f i).1) (Finset.sort_nodup _ S)).symm.trans (by simp)

@[simp] theorem sumSet_cost {α : Type*} [LinearOrder α] (S : Finset α) (f : α → ℚ × ℕ) :
    (sumSet S f).2 = (∑ i ∈ S, (f i).2) + S.card := by
  rw [sumSet, sumList_cost, List.map_map, List.length_map, PrimitiveProgram.canonicalList_length]
  congr 1
  exact (List.sum_toFinset (fun i => (f i).2) (Finset.sort_nodup _ S)).symm.trans (by simp)

@[simp] theorem productSet_cost {α : Type*} [LinearOrder α] (S : Finset α) (f : α → ℚ × ℕ) :
    (productSet S f).2 = (∑ i ∈ S, (f i).2) + S.card := by
  rw [productSet, productList_cost, List.map_map, List.length_map, PrimitiveProgram.canonicalList_length]
  congr 1
  exact (List.sum_toFinset (fun i => (f i).2) (Finset.sort_nodup _ S)).symm.trans (by simp)

/-- Construct the integer power of two by a shift, followed by one inverse. -/
def prepareWeight {n : ℕ} (levels : Fin n → ℕ) : ℚ × ℕ :=
  let denominator : ℕ := 2 ^ (∑ v, levels v)
  ((denominator : ℚ)⁻¹, 1)

@[simp] theorem prepareWeight_value {n : ℕ} (levels : Fin n → ℕ) :
    (prepareWeight levels).1 = weightQ levels := by simp [prepareWeight, weightQ]

def countedIncrement {n t : ℕ} (scopes : Fin t → Finset (Fin n))
    (table : SampleTable scopes) (ν : Fin t → ℕ) (z : Grid (commonLevels scopes ν)) (i : Fin t) : ℚ × ℕ :=
  match ν i with
  | 0 => (stepQ scopes table ν z i 0, 0)
  | l + 1 => (stepQ scopes table ν z i (l + 1) - stepQ scopes table ν z i l, 1)

@[simp] theorem countedIncrement_value {n t : ℕ} (scopes : Fin t → Finset (Fin n))
    (table : SampleTable scopes) (ν : Fin t → ℕ) (z : Grid (commonLevels scopes ν)) (i : Fin t) :
    (countedIncrement scopes table ν z i).1 = incrementQ scopes table ν z i := by
  unfold countedIncrement incrementQ
  generalize h : ν i = l
  cases l <;> rfl

@[simp] theorem countedIncrement_cost {n t : ℕ} (scopes : Fin t → Finset (Fin n))
    (table : SampleTable scopes) (ν : Fin t → ℕ) (z : Grid (commonLevels scopes ν)) (i : Fin t) :
    (countedIncrement scopes table ν z i).2 = if ν i = 0 then 0 else 1 := by
  unfold countedIncrement
  generalize h : ν i = l
  cases l <;> simp

/-- The weight is prepared before the cell loop and charged exactly once. -/
def countedLevel {n t : ℕ} (scopes : Fin t → Finset (Fin n))
    (table : SampleTable scopes) (ν : Fin t → ℕ) : ℚ × ℕ :=
  let w := prepareWeight (commonLevels scopes ν)
  letI := PrimitiveProgram.gridOrder (commonLevels scopes ν)
  let cells := sumSet Finset.univ fun z : Grid (commonLevels scopes ν) =>
    mul (w.1, 0) (productSet Finset.univ (countedIncrement scopes table ν z))
  (cells.1, w.2 + cells.2)

def countedRule {n t : ℕ} (scopes : Fin t → Finset (Fin n))
    (table : SampleTable scopes) (J : ℕ) : ℚ × ℕ :=
  letI := PrimitiveProgram.tupleOrder t
  sumSet (TupleCount.boundedTuples t J) (countedLevel scopes table)

@[simp] theorem countedLevel_value {n t : ℕ} (scopes : Fin t → Finset (Fin n))
    (table : SampleTable scopes) (ν : Fin t → ℕ) :
    (countedLevel scopes table ν).1 =
      ∑ z : Grid (commonLevels scopes ν), weightQ (commonLevels scopes ν) * ∏ i, incrementQ scopes table ν z i := by
  simp [countedLevel, mul]

/-- The costed evaluator computes exactly the existing rational quadrature. -/
@[simp] theorem countedRule_value {n t : ℕ} (scopes : Fin t → Finset (Fin n))
    (table : SampleTable scopes) (J : ℕ) : (countedRule scopes table J).1 = ruleQ scopes table J := by
  simp [countedRule, ruleQ]

/-- Exact count of the inverse, increment subtractions, products, weighted
cell multiplications, and additions in a single retained level. -/
theorem countedLevel_cost {n t : ℕ} (scopes : Fin t → Finset (Fin n))
    (table : SampleTable scopes) (ν : Fin t → ℕ) :
    (countedLevel scopes table ν).2 = 1 + Fintype.card (Grid (commonLevels scopes ν)) *
      ((∑ i : Fin t, if ν i = 0 then 0 else 1) + t + 2) := by
  simp only [countedLevel, sumSet_cost, mul, productSet_cost, countedIncrement_cost,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, prepareWeight, Nat.cast_id]
  ring

/-- Lemma 3.1's arithmetic bound for the actual generic rational rule loops.
The constant includes preparing each level weight once. -/
theorem countedRule_operations {n t r J : ℕ} (scopes : Fin t → Finset (Fin n))
    (hscopes : ∀ i, (scopes i).card ≤ r) (table : SampleTable scopes) (ht : 1 ≤ t) :
    (countedRule scopes table J).2 ≤ 10 * t * (J + t).choose t * 2 ^ (r * J) := by
  letI := PrimitiveProgram.tupleOrder t
  have hlevel : ∀ ν ∈ TupleCount.boundedTuples t J,
      (countedLevel scopes table ν).2 + 1 ≤ 10 * t * 2 ^ (r * J) := by
    intro ν hν
    have hinc : (∑ i : Fin t, if ν i = 0 then 0 else 1) ≤ t := by
      calc
        _ ≤ ∑ _i : Fin t, 1 := Finset.sum_le_sum fun i _ => by split_ifs <;> omega
        _ = _ := by simp
    have hcard := common_grid_card_le scopes hscopes ν (TupleCount.mem_boundedTuples.mp hν)
    have hp : 1 ≤ 2 ^ (r * J) := one_le_pow₀ (by decide)
    rw [countedLevel_cost]
    have hc : (∑ i : Fin t, if ν i = 0 then 0 else 1) + t + 2 ≤ 4 * t := by omega
    have hm := Nat.mul_le_mul hcard hc
    nlinarith
  rw [countedRule, sumSet_cost]
  calc
    _ = ∑ ν ∈ TupleCount.boundedTuples t J, ((countedLevel scopes table ν).2 + 1) := by
      simp [Finset.sum_add_distrib]
    _ ≤ ∑ _ν ∈ TupleCount.boundedTuples t J, 10 * t * 2 ^ (r * J) := Finset.sum_le_sum hlevel
    _ = _ := by simp [TupleCount.card_boundedTuples]; ring

end Paper08.QuadratureOperationCount
