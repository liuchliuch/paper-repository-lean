import Paper08.RationalProgram
import Paper08.EffectiveAccess
import Paper08.PrimitiveMomentsQ
import Mathlib.Data.List.Lex
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Prod.Lex

/-! # Explicit arithmetic expressions for primitive and moment computation

The expression tree exposes every rational operation, including the logarithm
series, powers, projections and dyadic rounding. Finite sums use computable
sorting, with orders whose keys are finite lists of coordinates.
-/
open scoped BigOperators
namespace Paper08.PrimitiveProgram
open RationalProgram

/-- Lexicographic coordinate keys avoid unbounded numeric encodings. -/
def tupleOrder (t : ℕ) : LinearOrder (Fin t → ℕ) :=
  LinearOrder.lift' List.ofFn List.ofFn_injective

def gridOrder {n : ℕ} (m : Fin n → ℕ) : LinearOrder (CellGrid.Grid m) :=
  LinearOrder.lift' (fun z : CellGrid.Grid m => List.ofFn (fun v => (z v).val)) (by
    intro x y h
    have hh := List.ofFn_injective h
    funext v
    exact Fin.ext (congrFun hh v))

def exponentOrder (m : ℕ) : LinearOrder (Fin m →₀ ℕ) :=
  LinearOrder.lift' (fun d : Fin m →₀ ℕ => List.ofFn (fun e => d e)) (by
    intro d e h
    exact Finsupp.ext (congrFun (List.ofFn_injective h)))

def finsetKey {m : ℕ} (S : Finset (Fin m)) : List ℕ :=
  List.ofFn (fun e => if e ∈ S then 1 else 0)

lemma finsetKey_injective (m : ℕ) : Function.Injective (finsetKey (m := m)) := by
  intro S T h
  have hh := List.ofFn_injective h
  ext e
  have he := congrFun hh e
  by_cases hS : e ∈ S <;> by_cases hT : e ∈ T <;> simp_all

def finsetOrder (m : ℕ) : LinearOrder (Finset (Fin m)) :=
  LinearOrder.lift' finsetKey (finsetKey_injective m)

def pairOrder (m : ℕ) : LinearOrder (Finset (Fin m) × Finset (Fin m)) := by
  letI := finsetOrder m
  exact LinearOrder.lift' (fun p : Finset (Fin m) × Finset (Fin m) => toLex p)
    (fun _ _ h => h)

/-- A computable finite traversal from an explicit order. -/
def canonicalList {α : Type*} [LinearOrder α] (S : Finset α) : List α := S.sort (· ≤ ·)

@[simp] theorem canonicalList_length {α : Type*} [LinearOrder α] (S : Finset α) :
    (canonicalList S).length = S.card := Finset.length_sort _
@[simp] theorem canonicalList_mem {α : Type*} [LinearOrder α] (S : Finset α) (a : α) :
    a ∈ canonicalList S ↔ a ∈ S := Finset.mem_sort _

/-- Traverse an actual list, with zero as the initial sum. -/
def sumList : List Expr → Expr
  | [] => .atom 0
  | e :: es => .node .add e (sumList es)

def productList : List Expr → Expr
  | [] => .atom 1
  | e :: es => .node .mul e (productList es)

def natPower (e : Expr) : ℕ → Expr
  | 0 => .atom 1
  | n+1 => .node .mul (natPower e n) e

@[simp] theorem sumList_eval (es : List Expr) : (sumList es).eval = (es.map Expr.eval).sum := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [sumList, Expr.eval, Op.eval, ih]
@[simp] theorem productList_eval (es : List Expr) : (productList es).eval = (es.map Expr.eval).prod := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [productList, Expr.eval, Op.eval, ih]
@[simp] theorem natPower_eval (e : Expr) (n : ℕ) : (natPower e n).eval = e.eval^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [natPower, Expr.eval, Op.eval, ih, pow_succ]

@[simp] theorem sumList_operations (es : List Expr) :
    (sumList es).operations = (es.map Expr.operations).sum + es.length := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [sumList, Expr.operations, ih]; omega
@[simp] theorem productList_operations (es : List Expr) :
    (productList es).operations = (es.map Expr.operations).sum + es.length := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [productList, Expr.operations, ih]; omega
@[simp] theorem natPower_operations (e : Expr) (n : ℕ) :
    (natPower e n).operations = n*(e.operations+1) := by
  induction n with
  | zero => simp [natPower, Expr.operations]
  | succ n ih => simp only [natPower, Expr.operations, ih]; ring

theorem sumList_inputHeight (es : List Expr) {H : ℕ} (hH : 1 ≤ H)
    (he : ∀ e ∈ es, e.inputHeight ≤ H) : (sumList es).inputHeight ≤ H := by
  induction es with
  | nil => simpa [sumList, Expr.inputHeight, height] using hH
  | cons e es ih =>
    exact max_le (he e (by simp)) (ih (fun x hx => he x (by simp [hx])))
theorem productList_inputHeight (es : List Expr) {H : ℕ} (hH : 1 ≤ H)
    (he : ∀ e ∈ es, e.inputHeight ≤ H) : (productList es).inputHeight ≤ H := by
  induction es with
  | nil => simpa [productList, Expr.inputHeight, height] using hH
  | cons e es ih =>
    exact max_le (he e (by simp)) (ih (fun x hx => he x (by simp [hx])))
theorem natPower_inputHeight (e : Expr) (n : ℕ) {H : ℕ} (hH : 1 ≤ H)
    (he : e.inputHeight ≤ H) : (natPower e n).inputHeight ≤ H := by
  induction n with
  | zero => simpa [natPower, Expr.inputHeight, height] using hH
  | succ n ih => exact max_le ih he

/-- Finite sums and products over explicit computable sorted traversals. -/
def sumSet {α : Type*} [LinearOrder α] (S : Finset α) (f : α → Expr) : Expr :=
  sumList ((canonicalList S).map f)
def productSet {α : Type*} [LinearOrder α] (S : Finset α) (f : α → Expr) : Expr :=
  productList ((canonicalList S).map f)

@[simp] theorem sumSet_eval {α : Type*} [LinearOrder α] (S : Finset α) (f : α → Expr) :
    (sumSet S f).eval = ∑ i ∈ S, (f i).eval := by
  rw [sumSet, sumList_eval, List.map_map]
  exact (List.sum_toFinset (fun i => (f i).eval) (Finset.sort_nodup _ S)).symm.trans
    (by simp [canonicalList])
@[simp] theorem productSet_eval {α : Type*} [LinearOrder α] (S : Finset α) (f : α → Expr) :
    (productSet S f).eval = ∏ i ∈ S, (f i).eval := by
  rw [productSet, productList_eval, List.map_map]
  exact (List.prod_toFinset (fun i => (f i).eval) (Finset.sort_nodup _ S)).symm.trans
    (by simp [canonicalList])

@[simp] theorem sumSet_operations {α : Type*} [LinearOrder α] (S : Finset α) (f : α → Expr) :
    (sumSet S f).operations = (∑ i ∈ S, (f i).operations) + S.card := by
  rw [sumSet, sumList_operations, List.map_map, List.length_map, canonicalList_length]
  congr 1
  exact (List.sum_toFinset (fun i => (f i).operations) (Finset.sort_nodup _ S)).symm.trans
    (by simp [canonicalList])
@[simp] theorem productSet_operations {α : Type*} [LinearOrder α] (S : Finset α) (f : α → Expr) :
    (productSet S f).operations = (∑ i ∈ S, (f i).operations) + S.card := by
  rw [productSet, productList_operations, List.map_map, List.length_map, canonicalList_length]
  congr 1
  exact (List.sum_toFinset (fun i => (f i).operations) (Finset.sort_nodup _ S)).symm.trans
    (by simp [canonicalList])

theorem sumSet_operations_le {α : Type*} [LinearOrder α] (S : Finset α) (f : α → Expr)
    {N : ℕ} (hf : ∀ i ∈ S, (f i).operations ≤ N) : (sumSet S f).operations ≤ S.card*(N+1) := by
  rw [sumSet_operations]
  have hh := Finset.sum_le_sum hf
  simp only [Finset.sum_const, nsmul_eq_mul] at hh
  nlinarith

theorem productSet_operations_le {α : Type*} [LinearOrder α] (S : Finset α) (f : α → Expr)
    {N : ℕ} (hf : ∀ i ∈ S, (f i).operations ≤ N) : (productSet S f).operations ≤ S.card*(N+1) := by
  rw [productSet_operations]
  have hh := Finset.sum_le_sum hf
  simp only [Finset.sum_const, nsmul_eq_mul] at hh
  nlinarith

theorem sumSet_inputHeight {α : Type*} [LinearOrder α] (S : Finset α) (f : α → Expr)
    {H : ℕ} (hH : 1 ≤ H) (hf : ∀ i ∈ S, (f i).inputHeight ≤ H) :
    (sumSet S f).inputHeight ≤ H := by
  apply sumList_inputHeight _ hH
  intro e he
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
  exact hf i ((canonicalList_mem S i).mp hi)
theorem productSet_inputHeight {α : Type*} [LinearOrder α] (S : Finset α) (f : α → Expr)
    {H : ℕ} (hH : 1 ≤ H) (hf : ∀ i ∈ S, (f i).inputHeight ≤ H) :
    (productSet S f).inputHeight ≤ H := by
  apply productList_inputHeight _ hH
  intro e he
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
  exact hf i ((canonicalList_mem S i).mp hi)

end Paper08.PrimitiveProgram
