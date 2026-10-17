import Paper34.LinearPrograms
import Paper34.SampleMedian
import Paper34.ArbitraryRepresentatives
import Paper34.SourceComplexity
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Finset.Card

/-!
# Actual coefficient matrices and finite description bounds (Proposition 6.2)

The matrices below encode the existing `initializerConstraint` and
`refinementConstraint`. Labels occur only in right-hand sides. Each initializer
row uses only its own sample's slack. Nonzero counts inspect the actual real
matrix coefficients; they are not arbitrary cost surrogates.
-/

open scoped BigOperators

namespace Paper34

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The source's actual dense monomial feature. -/
def monomialFeature {n d : ℕ} (x : Point n) (a : Exponent n d) : ℝ :=
  ∏ k, x k ^ (a k : ℕ)

/-- The two residual signs, in the same Bool convention as LinearPrograms. -/
def residualRowSign (b : Bool) : ℝ := if b then 1 else -1

/-- Actual initializer coefficient matrix. The monomial block is signed, and
only the slack belonging to this row's sample has coefficient -1. -/
def initializerMatrix {n d M : ℕ} (X : Fin M → Point n) :
    Matrix (InitializerRow M) (InitializerVariable n d M) ℝ :=
  fun row col => match col with
    | Sum.inl a => residualRowSign row.2 * monomialFeature (X row.1) a
    | Sum.inr i => if i = row.1 then -1 else 0

/-- Labels are data on the RHS, and are not variable-column coefficients. -/
def initializerRHS {M : ℕ} (Y : Fin M → ℝ) (row : InitializerRow M) : ℝ :=
  residualRowSign row.2 * Y row.1

/-- Actual minimax refinement coefficient matrix, with one shared lambda column. -/
def refinementMatrix {n d m : ℕ} (a : CellIndex n m → Point n) :
    Matrix (RefinementRow n m) (RefinementVariable n d) ℝ :=
  fun row col => match col with
    | some e => residualRowSign row.2 * monomialFeature (a row.1) e
    | none => -1

def refinementRHS {n m : ℕ} (y : CellIndex n m → ℝ) (row : RefinementRow n m) : ℝ :=
  residualRowSign row.2 * y row.1

/-- Finite row action of the actual coefficient matrix. -/
def lpRowAction {R C : Type*} [Fintype C] (A : Matrix R C ℝ)
    (v : C → ℝ) (r : R) : ℝ := ∑ c, A r c * v c

/-- The actual initializer matrix inequality is precisely the existing source
residual row, including its own slack and signed label RHS. -/
theorem initializerMatrix_row_iff {n d M : ℕ} (X : Fin M → Point n)
    (Y : Fin M → ℝ) (v : InitializerVariable n d M → ℝ) (row : InitializerRow M) :
    lpRowAction (initializerMatrix X) v row ≤ initializerRHS Y row ↔
      initializerConstraint X Y v row := by
  classical
  rcases row with ⟨i, b⟩
  cases b <;>
    simp [lpRowAction, initializerMatrix, initializerRHS, residualRowSign,
      initializerConstraint, monomialFeature, denseEval, initCoefficients, initSlacks,
      Finset.sum_neg_distrib, mul_comm] <;>
    constructor <;> intro h <;> linarith

/-- The actual refinement matrix inequality is precisely the existing source
minimax residual row. -/
theorem refinementMatrix_row_iff {n d m : ℕ} (a : CellIndex n m → Point n)
    (y : CellIndex n m → ℝ) (v : RefinementVariable n d → ℝ) (row : RefinementRow n m) :
    lpRowAction (refinementMatrix a) v row ≤ refinementRHS y row ↔
      refinementConstraint a y v row := by
  classical
  rcases row with ⟨j, b⟩
  cases b <;>
    simp [lpRowAction, refinementMatrix, refinementRHS, residualRowSign,
      refinementConstraint, monomialFeature, denseEval, Finset.sum_neg_distrib, mul_comm]

/-- Support of a real matrix row: exactly those columns whose coefficients
are nonzero for the actual supplied locations. -/
def matrixRowSupport {R C : Type*} [Fintype C] (A : Matrix R C ℝ) (r : R) : Finset C := by
  classical
  exact Finset.univ.filter (fun c => A r c ≠ 0)

/-- Total actual nonzero coefficients, counted once by their row and column. -/
def matrixNonzeroCount {R C : Type*} [Fintype R] [Fintype C]
    (A : Matrix R C ℝ) : ℕ := ∑ r, (matrixRowSupport A r).card

/-- At most D monomial coefficients and one sample-specific slack coefficient
can be nonzero in any actual initializer row. -/
theorem initializerMatrix_row_nonzeros_le {n d M : ℕ} (X : Fin M → Point n)
    (row : InitializerRow M) :
    (matrixRowSupport (initializerMatrix (d := d) X) row).card ≤ (d+1)^n + 1 := by
  classical
  let potential : Finset (InitializerVariable n d M) :=
    (Finset.univ.image Sum.inl) ∪ {Sum.inr row.1}
  have hsub : matrixRowSupport (initializerMatrix (d := d) X) row ⊆ potential := by
    intro c hc
    cases c with
    | inl a =>
        apply Finset.mem_union_left
        exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩
    | inr i =>
        have hn := (Finset.mem_filter.mp hc).2
        have hi : i = row.1 := by
          by_contra hi
          exact hn (by simp [initializerMatrix, hi])
        apply Finset.mem_union_right
        simp only [Finset.mem_singleton]
        exact congrArg Sum.inr hi
  calc
    (matrixRowSupport (initializerMatrix (d := d) X) row).card ≤ potential.card :=
      Finset.card_le_card hsub
    _ ≤ (Finset.univ.image (Sum.inl : Exponent n d → InitializerVariable n d M)).card + 1 := by
      exact (Finset.card_union_le _ _).trans_eq (by simp)
    _ ≤ Fintype.card (Exponent n d) + 1 := Nat.add_le_add_right
      (Finset.card_image_le.trans_eq (Finset.card_univ)) 1
    _ = (d+1)^n + 1 := by rw [card_exponent]

/-- A refinement row has only D monomial columns and its single lambda column. -/
theorem refinementMatrix_row_nonzeros_le {n d m : ℕ} (a : CellIndex n m → Point n)
    (row : RefinementRow n m) :
    (matrixRowSupport (refinementMatrix (d := d) a) row).card ≤ (d+1)^n + 1 := by
  classical
  calc
    (matrixRowSupport (refinementMatrix (d := d) a) row).card ≤
        Fintype.card (RefinementVariable n d) := Finset.card_le_univ _
    _ = (d+1)^n + 1 := by simp [RefinementVariable]

/-- The exact finite dense dimension D is always positive. -/
lemma dense_dimension_pos (n d : ℕ) : 0 < (d+1)^n := pow_pos (by omega) n

/-- The actual initializer has at most 2M(D+1), hence at most 4MD nonzeros. -/
theorem initializerMatrix_nonzeros_le {n d M : ℕ} (X : Fin M → Point n) :
    matrixNonzeroCount (initializerMatrix (d := d) X) ≤ 2*M*((d+1)^n+1) ∧
      matrixNonzeroCount (initializerMatrix (d := d) X) ≤ 4*M*(d+1)^n := by
  have h : matrixNonzeroCount (initializerMatrix (d := d) X) ≤ 2*M*((d+1)^n+1) := by
    calc
      matrixNonzeroCount (initializerMatrix (d := d) X) ≤
          ∑ _row : InitializerRow M, ((d+1)^n+1) :=
        Finset.sum_le_sum (fun row _ => initializerMatrix_row_nonzeros_le X row)
      _ = 2*M*((d+1)^n+1) := by simp [InitializerRow, Nat.mul_comm]
  refine ⟨h, h.trans ?_⟩
  have hD : 1 ≤ (d+1)^n := dense_dimension_pos n d
  have hmD := Nat.mul_le_mul_left M hD
  nlinarith

/-- The actual refinement has at most 2m^n(D+1), hence at most 4m^nD nonzeros. -/
theorem refinementMatrix_nonzeros_le {n d m : ℕ} (a : CellIndex n m → Point n) :
    matrixNonzeroCount (refinementMatrix (d := d) a) ≤ 2*m^n*((d+1)^n+1) ∧
      matrixNonzeroCount (refinementMatrix (d := d) a) ≤ 4*m^n*(d+1)^n := by
  have h : matrixNonzeroCount (refinementMatrix (d := d) a) ≤ 2*m^n*((d+1)^n+1) := by
    calc
      matrixNonzeroCount (refinementMatrix (d := d) a) ≤
          ∑ _row : RefinementRow n m, ((d+1)^n+1) :=
        Finset.sum_le_sum (fun row _ => refinementMatrix_row_nonzeros_le a row)
      _ = 2*m^n*((d+1)^n+1) := by simp [RefinementRow, CellIndex, Nat.mul_comm]
  refine ⟨h, h.trans ?_⟩
  have hD : 1 ≤ (d+1)^n := dense_dimension_pos n d
  have hmD := Nat.mul_le_mul_left (m^n) hD
  nlinarith

/-- The source's dense dimension is bounded by a constant depending only on n
 times the number of cells, and hence by the sample count on a nonempty grid. -/
theorem dense_dimension_le_cells_and_samples {n d m M : ℕ}
    (hm : 0 < m) (hdm : d ≤ m) (hgrid : m^n ≤ M) :
    (d+1)^n ≤ 2^n*m^n ∧ (d+1)^n ≤ 2^n*M := by
  have hb : d+1 ≤ 2*m := by omega
  have hpow := Nat.pow_le_pow_left hb n
  rw [Nat.mul_pow] at hpow
  exact ⟨hpow, hpow.trans (Nat.mul_le_mul_left (2^n) hgrid)⟩


/-! ## A concrete exact-real arithmetic implementation of dense evaluation -/

/-- A materialized prefix of powers, its last entry, and the number of real
multiplications executed by the recursive table-building loop. -/
structure PowerTableBuild where
  entries : List ℝ
  current : ℝ
  multiplications : ℕ

/-- Start with x^0=1, then append one new power by one multiplication per step.
The current power is shared; powers are not independently recomputed. -/
def buildPowerTable (x : ℝ) : ℕ → PowerTableBuild
  | 0 => ⟨[1], 1, 0⟩
  | d+1 => let t := buildPowerTable x d
    let next := t.current * x
    ⟨t.entries ++ [next], next, t.multiplications+1⟩

lemma buildPowerTable_spec (x : ℝ) (d : ℕ) :
    (buildPowerTable x d).entries = (List.range (d+1)).map (fun e => x^e) ∧
    (buildPowerTable x d).current = x^d ∧
    (buildPowerTable x d).multiplications = d := by
  induction d with
  | zero => simp [buildPowerTable]
  | succ d ih =>
    rcases ih with ⟨he, hp, hc⟩
    simp [buildPowerTable, he, hp, hc, List.range_succ, pow_succ]

/-- A lookup in the actual materialized power table. -/
def powerTableLookup (x : ℝ) (d : ℕ) (e : Fin (d+1)) : ℝ :=
  (buildPowerTable x d).entries[e.val]'(by
    rw [(buildPowerTable_spec x d).1, List.length_map, List.length_range]
    exact e.isLt)

lemma powerTableLookup_eq (x : ℝ) (d : ℕ) (e : Fin (d+1)) :
    powerTableLookup x d e = x^(e : ℕ) := by
  simp [powerTableLookup, (buildPowerTable_spec x d).1]

/-- A straight-line exact-real arithmetic expression. Literal nodes include
input coefficients and already materialized table lookups; add/mul nodes are
the primitive real operations being counted. -/
inductive RealArithmeticExpr where
  | literal (x : ℝ)
  | add (a b : RealArithmeticExpr)
  | mul (a b : RealArithmeticExpr)

def RealArithmeticExpr.eval : RealArithmeticExpr → ℝ
  | .literal x => x
  | .add a b => a.eval+b.eval
  | .mul a b => a.eval*b.eval

def RealArithmeticExpr.operations : RealArithmeticExpr → ℕ
  | .literal _ => 0
  | .add a b => a.operations+b.operations+1
  | .mul a b => a.operations+b.operations+1

def productExpression : List RealArithmeticExpr → RealArithmeticExpr
  | [] => .literal 1
  | a::l => .mul a (productExpression l)

def sumExpression : List RealArithmeticExpr → RealArithmeticExpr
  | [] => .literal 0
  | a::l => .add a (sumExpression l)

lemma eval_productExpression (l : List RealArithmeticExpr) :
    (productExpression l).eval = (l.map RealArithmeticExpr.eval).prod := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [productExpression, RealArithmeticExpr.eval, ih]

lemma eval_sumExpression (l : List RealArithmeticExpr) :
    (sumExpression l).eval = (l.map RealArithmeticExpr.eval).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [sumExpression, RealArithmeticExpr.eval, ih]

lemma productExpression_operations_le (l : List RealArithmeticExpr) (B : ℕ)
    (h : ∀ a ∈ l, a.operations ≤ B) :
    (productExpression l).operations ≤ l.length*(B+1) := by
  induction l with
  | nil => simp [productExpression, RealArithmeticExpr.operations]
  | cons a l ih =>
    have ha := h a (by simp)
    have ht := ih (fun a ha => h a (by simp [ha]))
    simp only [productExpression, RealArithmeticExpr.operations, List.length_cons]
    nlinarith

lemma sumExpression_operations_le (l : List RealArithmeticExpr) (B : ℕ)
    (h : ∀ a ∈ l, a.operations ≤ B) :
    (sumExpression l).operations ≤ l.length*(B+1) := by
  induction l with
  | nil => simp [sumExpression, RealArithmeticExpr.operations]
  | cons a l ih =>
    have ha := h a (by simp)
    have ht := ih (fun a ha => h a (by simp [ha]))
    simp only [sumExpression, RealArithmeticExpr.operations, List.length_cons]
    nlinarith

/-- The actual dense monomial evaluation circuit, using shared coordinate
power tables and then n multiplications per monomial plus coefficient multiply
and accumulation. -/
def denseEvaluationExpression {n d : ℕ} (c : Exponent n d → ℝ) (x : Point n) : RealArithmeticExpr :=
  sumExpression ((Finset.univ : Finset (Exponent n d)).toList.map (fun a =>
    .mul (.literal (c a)) (productExpression ((Finset.univ : Finset (Fin n)).toList.map
      (fun k => .literal (powerTableLookup (x k) d (a k)))))))

/-- Circuit correctness is for the genuine dense polynomial evaluation. -/
theorem denseEvaluationExpression_eval {n d : ℕ} (c : Exponent n d → ℝ) (x : Point n) :
    (denseEvaluationExpression c x).eval = denseEval c x := by
  simp [denseEvaluationExpression, eval_sumExpression, eval_productExpression,
    List.map_map, RealArithmeticExpr.eval, powerTableLookup_eq, denseEval]

lemma denseEvaluationExpression_operations_le {n d : ℕ} (c : Exponent n d → ℝ) (x : Point n) :
    (denseEvaluationExpression c x).operations ≤ (d+1)^n*(n+2) := by
  let terms := ((Finset.univ : Finset (Exponent n d)).toList.map (fun a =>
    RealArithmeticExpr.mul (.literal (c a))
      (productExpression ((Finset.univ : Finset (Fin n)).toList.map
        (fun k => .literal (powerTableLookup (x k) d (a k)))))))
  have hterms : ∀ a ∈ terms, a.operations ≤ n+1 := by
    intro a ha
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp ha
    have hprod := productExpression_operations_le
      ((Finset.univ : Finset (Fin n)).toList.map
        (fun k => RealArithmeticExpr.literal (powerTableLookup (x k) d (e k)))) 0 (by
          intro a ha
          obtain ⟨k, _, rfl⟩ := List.mem_map.mp ha
          exact le_rfl)
    simp only [List.length_map, Finset.length_toList, Finset.card_univ, Fintype.card_fin,
      zero_add, Nat.mul_one] at hprod
    change 0 + _ + 1 ≤ n+1
    omega
  have h := sumExpression_operations_le terms (n+1) hterms
  simpa [terms, denseEvaluationExpression, card_exponent] using h

/-- The table loops need exactly nd multiplications for one location. -/
lemma coordinate_power_table_operations {n : ℕ} (d : ℕ) (x : Point n) :
    (∑ k : Fin n, (buildPowerTable (x k) d).multiplications) = n*d := by
  simp only [(buildPowerTable_spec _ _).2.2]
  simp

lemma degree_times_dimension_bound (n d : ℕ) : n*d ≤ n*(d+1)^n := by
  cases n with
  | zero => simp
  | succ n =>
    have hp : 1 ≤ (d+1)^n := dense_dimension_pos n d
    have hd : d ≤ (d+1)^(n+1) := by rw [pow_succ]; nlinarith
    exact Nat.mul_le_mul_left _ hd

/-- Count the real operations of the actual table-plus-circuit residual
routine: all power-table multiplies, all circuit add/mul nodes, and one label
subtraction for every observation. -/
def batchResidualOperations {n d M : ℕ} (c : Exponent n d → ℝ)
    (X : Fin M → Point n) : ℕ :=
  ∑ i : Fin M, ((∑ k : Fin n, (buildPowerTable (X i k) d).multiplications) +
    (denseEvaluationExpression c (X i)).operations + 1)

/-- The explicit dense residual routine has O_n(MD) primitive real operations,
with a proved concrete constant, independently of coefficient magnitudes. -/
theorem batchResidualOperations_le {n d M : ℕ} (c : Exponent n d → ℝ)
    (X : Fin M → Point n) :
    batchResidualOperations c X ≤ (2*n+3)*M*(d+1)^n := by
  have hp (i : Fin M) :
      (∑ k : Fin n, (buildPowerTable (X i k) d).multiplications) +
        (denseEvaluationExpression c (X i)).operations + 1 ≤ (2*n+3)*(d+1)^n := by
    rw [coordinate_power_table_operations]
    have he := denseEvaluationExpression_operations_le c (X i)
    have hn := degree_times_dimension_bound n d
    have hD := dense_dimension_pos n d
    nlinarith
  calc
    batchResidualOperations c X ≤ ∑ _i : Fin M, (2*n+3)*(d+1)^n :=
      Finset.sum_le_sum (fun i _ => hp i)
    _ = (2*n+3)*M*(d+1)^n := by simp; ring


/-! ## Concrete comparison tables for assignment and median enumeration -/

/-- Each grid-scan site performs its lower-bound and upper-bound comparisons.
The final interval includes its lower exterior endpoint, exactly as halfOpenCell. -/
def gridCoordinateChecks {n m M : ℕ} (X : Fin M → Point n)
    (site : Fin M × CellIndex n m × Fin n) : Bool × Bool := by
  classical
  let i := site.1
  let j := site.2.1
  let k := site.2.2
  exact (if (j k : ℕ)+1 = m then decide (cellLower j k ≤ X i k)
    else decide (cellLower j k < X i k), decide (X i k ≤ cellUpper j k))

lemma gridCoordinateChecks_correct {n m M : ℕ} (X : Fin M → Point n)
    (i : Fin M) (j : CellIndex n m) :
    X i ∈ halfOpenCell j ↔ ∀ k : Fin n,
      (gridCoordinateChecks X (i,j,k)).1 = true ∧
        (gridCoordinateChecks X (i,j,k)).2 = true := by
  classical
  have hc (k : Fin n) :
      ((gridCoordinateChecks X (i,j,k)).1 = true ∧
        (gridCoordinateChecks X (i,j,k)).2 = true) ↔
      cellLower j k ≤ X i k ∧ X i k ≤ cellUpper j k ∧
        (cellLower j k < X i k ∨ (j k : ℕ)+1 = m) := by
    by_cases h : (j k : ℕ)+1 = m
    · simp [gridCoordinateChecks, h]
    · simp only [gridCoordinateChecks, h, if_false, decide_eq_true_eq, or_false]
      constructor
      · rintro ⟨hl, hu⟩; exact ⟨hl.le, hu, hl⟩
      · rintro ⟨_, hu, hl⟩; exact ⟨hl, hu⟩
  constructor
  · intro h k
    exact (hc k).mpr ⟨h.1.1 k, h.1.2 k, h.2 k⟩
  · intro h
    have hh := fun k => (hc k).mp (h k)
    exact ⟨⟨fun k => (hh k).1, fun k => (hh k).2.1⟩, fun k => (hh k).2.2⟩

/-- The actual finite naive grid comparison table, with one entry per sample,
cell and coordinate. Each entry contains two primitive real comparisons. -/
def gridComparisonTrace {n m M : ℕ} (X : Fin M → Point n) : List (Bool × Bool) :=
  ((Finset.univ : Finset (Fin M × CellIndex n m × Fin n)).toList.map
    (gridCoordinateChecks X))

def gridScanOperations {n m M : ℕ} (X : Fin M → Point n) : ℕ :=
  2 * (gridComparisonTrace (m := m) X).length

theorem gridScanOperations_eq {n m M : ℕ} (X : Fin M → Point n) :
    gridScanOperations (m := m) X = 2*n*M*m^n := by
  simp [gridScanOperations, gridComparisonTrace, CellIndex]
  ring

/-- Pairwise real comparisons actually used to test both median-side counts.
Indices are the original sample indices, so equal labels are still repeated. -/
def medianComparisonTrace {ι : Type*} (I : Finset ι) (Z : ι → ℝ) : List (Bool × Bool) := by
  classical
  exact (Finset.univ : Finset (I × I)).toList.map
    (fun ij => (decide (Z ij.1 ≤ Z ij.2), decide (Z ij.2 ≤ Z ij.1)))

def medianComparisonOperations {ι : Type*} (I : Finset ι) (Z : ι → ℝ) : ℕ :=
  2 * (medianComparisonTrace I Z).length

theorem medianComparisonOperations_eq {ι : Type*} (I : Finset ι) (Z : ι → ℝ) :
    medianComparisonOperations I Z = 2 * I.card^2 := by
  simp [medianComparisonOperations, medianComparisonTrace, pow_two]

/-- A concrete finite candidate-index filter. The predicate is evaluated using
exactly the two pairwise comparison tables and two finite integer tallies. -/
def enumeratedMedianCandidates {M : ℕ} (I : Finset (Fin M)) (Z : Fin M → ℝ) : Finset (Fin M) := by
  classical
  exact I.filter (fun i => IsSampleMedian I Z (Z i))

lemma enumeratedMedianCandidates_nonempty {M : ℕ} (I : Finset (Fin M)) (Z : Fin M → ℝ)
    (hI : I.Nonempty) : (enumeratedMedianCandidates I Z).Nonempty := by
  classical
  obtain ⟨y, hy, hmed⟩ := exists_sampleMedian_mem_image I Z hI
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
  exact ⟨i, Finset.mem_filter.mpr ⟨hi, hmed⟩⟩

/-- Select the smallest sample index among accepted candidates. This is a
concrete finite enumeration implementation of the permitted median step; it is
not a runtime assertion about Classical.choose in the abstract medianFor. -/
def enumeratedMedian {M : ℕ} (I : Finset (Fin M)) (Z : Fin M → ℝ) (hI : I.Nonempty) : ℝ :=
  Z ((enumeratedMedianCandidates I Z).min' (enumeratedMedianCandidates_nonempty I Z hI))

theorem enumeratedMedian_spec {M : ℕ} (I : Finset (Fin M)) (Z : Fin M → ℝ) (hI : I.Nonempty) :
    IsSampleMedian I Z (enumeratedMedian I Z hI) := by
  classical
  exact (Finset.mem_filter.mp ((enumeratedMedianCandidates I Z).min'_mem
    (enumeratedMedianCandidates_nonempty I Z hI))).2

/-- Explicit visits of the finite enumeration: for each index pair, two real
comparisons and two tally updates; for each candidate, a flag test and an
index-selection visit. This is a specified finite loop cost model. -/
abbrev MedianEnumerationVisit {ι : Type*} (I : Finset ι) :=
  Sum (Fin 4 × (I × I)) (Fin 2 × I)

def medianEnumerationWork {ι : Type*} (I : Finset ι) : ℕ := Fintype.card (MedianEnumerationVisit I)

lemma medianEnumerationWork_eq {ι : Type*} (I : Finset ι) :
    medianEnumerationWork I = 4*I.card^2 + 2*I.card := by
  simp [medianEnumerationWork, MedianEnumerationVisit, pow_two]

/-- The concrete enumeration work is polynomial in the ambient sample count. -/
lemma medianEnumerationWork_le {M : ℕ} (I : Finset (Fin M)) :
    medianEnumerationWork I ≤ 6*M^2 := by
  have hcard : I.card ≤ M := by simpa using Finset.card_le_univ I
  rw [medianEnumerationWork_eq]
  have hs : I.card^2 ≤ M^2 := Nat.pow_le_pow_left hcard 2
  have hself : I.card ≤ I.card^2 := by nlinarith
  nlinarith


/-! ## Completeness of the dense coefficient representation -/

/-- The actual monomial exponent encoded by a dense tensor index. -/
def denseExponent {n d : ℕ} (a : Exponent n d) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun k => (a k : ℕ))

lemma denseExponent_injective (n d : ℕ) :
    Function.Injective (denseExponent : Exponent n d → Fin n →₀ ℕ) := by
  intro a b hab
  funext k
  apply Fin.ext
  exact congrArg (fun s : Fin n →₀ ℕ => s k) hab

/-- Extract every native polynomial coefficient in the tensor-degree box. -/
def nativeDenseCoefficients {n d : ℕ} (q : PolynomialSpace n d) (a : Exponent n d) : ℝ :=
  q.1.coeff (denseExponent a)

/-- Dense encoding is complete for the actual native polynomial space, not
only sound. Every coefficient outside the degree box is zero by q's membership
proof, and all bounded exponents appear exactly once. -/
theorem densePolynomial_nativeDenseCoefficients {n d : ℕ} (q : PolynomialSpace n d) :
    densePolynomial (nativeDenseCoefficients q) = q.1 := by
  classical
  apply MvPolynomial.ext
  intro s
  by_cases hs : ∀ k, s k ≤ d
  · let a : Exponent n d := fun k => ⟨s k, Nat.lt_succ_iff.mpr (hs k)⟩
    have ha : denseExponent a = s := by ext k; rfl
    have heq (b : Exponent n d) : denseExponent b = s ↔ b = a := by
      rw [← ha]
      exact (denseExponent_injective n d).eq_iff
    change (∑ b : Exponent n d,
      MvPolynomial.monomial (denseExponent b) (nativeDenseCoefficients q b)).coeff s = _
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial, heq, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, nativeDenseCoefficients, ha]
  · have hq0 : q.1.coeff s = 0 := by
      apply MvPolynomial.notMem_support_iff.mp
      intro hmem
      exact hs ((MvPolynomial.mem_restrictDegree (Fin n) q.1 d).mp q.2 s hmem)
    have hne (b : Exponent n d) : denseExponent b ≠ s := by
      intro h
      apply hs
      intro k
      rw [← h]
      exact Nat.le_of_lt_succ (b k).isLt
    change (∑ b : Exponent n d,
      MvPolynomial.monomial (denseExponent b) (nativeDenseCoefficients q b)).coeff s = _
    rw [MvPolynomial.coeff_sum]
    simp [hne, hq0]

/-- Every native source polynomial is represented by an actual dense vector. -/
theorem densePolynomial_encoding_complete {n d : ℕ} (q : PolynomialSpace n d) :
    ∃ c : Exponent n d → ℝ, densePolynomial c = q.1 :=
  ⟨nativeDenseCoefficients q, densePolynomial_nativeDenseCoefficients q⟩

/-- Evaluation of the extracted dense vector is the source's native polyEval. -/
theorem denseEval_nativeDenseCoefficients {n d : ℕ} (q : PolynomialSpace n d) (x : Point n) :
    denseEval (nativeDenseCoefficients q) x = polyEval q x := by
  rw [← eval_densePolynomial, densePolynomial_nativeDenseCoefficients]
  rfl


/-! ## Actual LP objectives and a polynomial bound for the specified finite loops -/

/-- Coefficient of a sample slack in the true cell-normalized LAD objective. -/
def initializerSlackWeight {κ : Type*} [Fintype κ] {M : ℕ}
    (samples : κ → Finset (Fin M)) (i : Fin M) : ℝ := by
  classical
  exact (Fintype.card κ : ℝ)⁻¹ * ∑ j,
    if i ∈ samples j then ((samples j).card : ℝ)⁻¹ else 0

/-- Expanding the actual linear slack objective gives exactly the source's
cell-normalized weighted average, even before using partition disjointness. -/
theorem initializer_slack_objective_eq {κ : Type*} [Fintype κ] {M : ℕ}
    (samples : κ → Finset (Fin M)) (v : Fin M → ℝ) :
    (∑ i, initializerSlackWeight samples i * v i) =
      (Fintype.card κ : ℝ)⁻¹ * ∑ j, ((samples j).card : ℝ)⁻¹ * ∑ i ∈ samples j, v i := by
  classical
  simp only [initializerSlackWeight, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp [mul_ite, ite_mul]

/-- The linear initializer objective is zero on polynomial columns and has the
actual averaging weights on sample slack columns. -/
def initializerObjective {n d m M : ℕ} (samples : CellIndex n m → Finset (Fin M)) :
    InitializerVariable n d M → ℝ
  | .inl _ => 0
  | .inr i => initializerSlackWeight samples i

theorem initializerObjective_eval {n d m M : ℕ}
    (samples : CellIndex n m → Finset (Fin M)) (v : InitializerVariable n d M → ℝ) :
    (∑ col, initializerObjective samples col * v col) =
      ((m^n : ℕ) : ℝ)⁻¹ * ∑ j, ((samples j).card : ℝ)⁻¹ *
        ∑ i ∈ samples j, initSlacks v i := by
  simpa [initializerObjective, initSlacks, CellIndex] using
    initializer_slack_objective_eq samples (initSlacks v)

/-- The minimax LP objective is exactly its lambda variable. -/
def refinementObjective {n d : ℕ} : RefinementVariable n d → ℝ
  | none => 1
  | some _ => 0

lemma refinementObjective_eval {n d : ℕ} (v : RefinementVariable n d → ℝ) :
    (∑ col, refinementObjective col * v col) = v none := by
  simp [refinementObjective]

/-- Primitive real work of one materialized-table dense residual evaluation. -/
def pointResidualOperations {n d : ℕ} (c : Exponent n d → ℝ) (x : Point n) : ℕ :=
  (∑ k : Fin n, (buildPowerTable (x k) d).multiplications) +
    (denseEvaluationExpression c x).operations + 1

lemma pointResidualOperations_le {n d : ℕ} (c : Exponent n d → ℝ) (x : Point n) :
    pointResidualOperations c x ≤ (2*n+3)*(d+1)^n := by
  unfold pointResidualOperations
  rw [coordinate_power_table_operations]
  have he := denseEvaluationExpression_operations_le c x
  have hn := degree_times_dimension_bound n d
  have hD := dense_dimension_pos n d
  nlinarith

/-- This precise finite-loop schedule comprises: the proved grid comparison
table; one common cell-mass inverse, two operations per cell weight and the
sample-by-cell objective-weight accumulation; initializer feature circuits;
then T copies of sample residual circuits, representative feature circuits,
proved finite median enumeration loops, and dense coefficient addition.
The LP oracle's own work is excluded. For the feature circuits, coefficient -1
retains both each positive monomial product and its negative as intermediate
nodes, supplying the two actual matrix row signs.

This is a mathematical exact-real cost model for an admissible finite-loop
realization, not a claim about the runtime of Classical.choose. -/
def outsideFiniteLoopWork {n d m M T : ℕ}
    (X : Fin M → Point n) (samples : CellIndex n m → Finset (Fin M))
    (representatives : CellIndex n m → Point n)
    (coefficients : Fin T → Exponent n d → ℝ) : ℕ :=
  gridScanOperations (m := m) X + (1 + 2*m^n + M*m^n) +
    batchResidualOperations (fun _ : Exponent n d => -1) X +
    ∑ t : Fin T, (batchResidualOperations (coefficients t) X +
      (∑ j : CellIndex n m, pointResidualOperations (fun _ : Exponent n d => -1) (representatives j)) +
      (∑ j : CellIndex n m, medianEnumerationWork (samples j)) + (d+1)^n)

/-- An explicit polynomial witness for all of the specified outside-oracle
finite loops. The only budget premise is T ≤ B(M+1); the source's logarithmic
choice of T is supplied independently by SourceComplexity. -/
theorem outsideFiniteLoopWork_le_polynomial {n d m M T B : ℕ}
    (X : Fin M → Point n) (samples : CellIndex n m → Finset (Fin M))
    (representatives : CellIndex n m → Point n)
    (coefficients : Fin T → Exponent n d → ℝ)
    (hm : 0 < m) (hdm : d ≤ m) (hgrid : m^n ≤ M) (hT : T ≤ B*(M+1)) :
    outsideFiniteLoopWork X samples representatives coefficients ≤
      (2*n + (2*n+3)*2^n + 4 +
        2*B*(2*(2*n+3)*2^n + 6 + 2^n)) * M^4 := by
  let C := 2^n
  let A := 2*n+3
  let F := 2*A*C+6+C
  let I := 2*n+A*C+4
  have hM1 : 1 ≤ M := (pow_pos hm n).trans_le hgrid
  have hM2 : M ≤ M^2 := by nlinarith
  have h23 : M^2 ≤ M^3 := by
    have h := Nat.mul_le_mul_left M hM2
    simpa [pow_succ, pow_two, Nat.mul_assoc] using h
  have h34 : M^3 ≤ M^4 := by
    have h := Nat.mul_le_mul_left M h23
    simpa [pow_succ, pow_two, Nat.mul_assoc] using h
  have hD : (d+1)^n ≤ C*M := (dense_dimension_le_cells_and_samples hm hdm hgrid).2
  have hbatch (c : Exponent n d → ℝ) : batchResidualOperations c X ≤ A*C*M^2 := by
    calc
      batchResidualOperations c X ≤ A*M*(d+1)^n := batchResidualOperations_le c X
      _ ≤ A*M*(C*M) := Nat.mul_le_mul_left (A*M) hD
      _ = A*C*M^2 := by ring
  have hrep : (∑ j : CellIndex n m,
      pointResidualOperations (fun _ : Exponent n d => -1) (representatives j)) ≤ A*C*M^2 := by
    calc
      _ ≤ ∑ _j : CellIndex n m, A*(d+1)^n :=
        Finset.sum_le_sum (fun j _ => pointResidualOperations_le _ _)
      _ = m^n*(A*(d+1)^n) := by simp [CellIndex]
      _ ≤ M*(A*(d+1)^n) := Nat.mul_le_mul_right _ hgrid
      _ ≤ M*(A*(C*M)) := Nat.mul_le_mul_left M (Nat.mul_le_mul_left A hD)
      _ = A*C*M^2 := by ring
  have hmedian : (∑ j : CellIndex n m, medianEnumerationWork (samples j)) ≤ 6*M^3 := by
    calc
      _ ≤ ∑ _j : CellIndex n m, 6*M^2 :=
        Finset.sum_le_sum (fun j _ => medianEnumerationWork_le (samples j))
      _ = m^n*(6*M^2) := by simp [CellIndex]
      _ ≤ M*(6*M^2) := Nat.mul_le_mul_right _ hgrid
      _ = 6*M^3 := by ring
  have hphase (t : Fin T) : batchResidualOperations (coefficients t) X +
      (∑ j : CellIndex n m, pointResidualOperations (fun _ : Exponent n d => -1) (representatives j)) +
      (∑ j : CellIndex n m, medianEnumerationWork (samples j)) + (d+1)^n ≤ F*M^3 := by
    have hR := hbatch (coefficients t)
    have hscale := Nat.mul_le_mul_left (A*C) h23
    have hCscale := Nat.mul_le_mul_left C (hM2.trans h23)
    dsimp [F]
    nlinarith
  have hsum : (∑ t : Fin T, (batchResidualOperations (coefficients t) X +
      (∑ j : CellIndex n m, pointResidualOperations (fun _ : Exponent n d => -1) (representatives j)) +
      (∑ j : CellIndex n m, medianEnumerationWork (samples j)) + (d+1)^n)) ≤ T*(F*M^3) := by
    exact (Finset.sum_le_sum (fun t _ => hphase t)).trans_eq (by simp)
  have hT' : T ≤ 2*B*M := by
    have h := Nat.mul_le_mul_left B (by omega : M+1 ≤ 2*M)
    exact hT.trans (by nlinarith)
  have hsum' : T*(F*M^3) ≤ (2*B*F)*M^4 := by
    convert Nat.mul_le_mul_right (F*M^3) hT' using 1
    ring
  have hgridWork : gridScanOperations (m := m) X ≤ 2*n*M^2 := by
    rw [gridScanOperations_eq]
    have h := Nat.mul_le_mul_left (2*n*M) hgrid
    nlinarith
  have hweights : 1 + 2*m^n + M*m^n ≤ 4*M^2 := by
    have h := Nat.mul_le_mul_left M hgrid
    nlinarith
  have hinit : gridScanOperations (m := m) X + (1+2*m^n+M*m^n) +
      batchResidualOperations (fun _ : Exponent n d => -1) X ≤ I*M^2 := by
    have hB := hbatch (fun _ => -1)
    dsimp [I]
    nlinarith
  have hinit' := hinit.trans (Nat.mul_le_mul_left I (h23.trans h34))
  unfold outsideFiniteLoopWork
  calc
    _ ≤ I*M^4 + (2*B*F)*M^4 := Nat.add_le_add hinit' (hsum.trans hsum')
    _ = _ := by dsimp [I, F, A, C]; ring


/-- On the actual source half-open assignment, no empty cell implies m^n≤M:
pick one sample in each cell and use the proved disjoint partition to obtain
an injection into Fin M. This premise is derived from observations, not added
to the source complexity theorem. -/
theorem nonempty_halfOpen_grid_card_le_samples {n m M : ℕ}
    (X : Fin M → Point n) (hm : 0 < m)
    (hN : ∀ j : CellIndex n m,
      (Finset.univ.filter (fun i => X i ∈ halfOpenCell j)).Nonempty) : m^n ≤ M := by
  classical
  let pick : CellIndex n m → Fin M := fun j =>
    (Finset.univ.filter (fun i => X i ∈ halfOpenCell j)).min' (hN j)
  have hinside (j : CellIndex n m) : X (pick j) ∈ halfOpenCell j :=
    (Finset.mem_filter.mp ((Finset.univ.filter (fun i => X i ∈ halfOpenCell j)).min'_mem (hN j))).2
  have hinj : Function.Injective pick := by
    intro i j hij
    by_contra hne
    have hji : X (pick i) ∈ halfOpenCell j := by rw [hij]; exact hinside j
    exact Set.disjoint_left.mp (halfOpenCell_pairwiseDisjoint hm hne) (hinside i) hji
  have hcard := Fintype.card_le_of_injective pick hinj
  simpa [CellIndex] using hcard

/-- Source dimension bound after deriving occupancy from the actual no-empty
half-open branch. -/
theorem dense_dimension_le_samples_of_nonempty_halfOpen {n d m M : ℕ}
    (X : Fin M → Point n) (hm : 0 < m) (hdm : d ≤ m)
    (hN : ∀ j : CellIndex n m,
      (Finset.univ.filter (fun i => X i ∈ halfOpenCell j)).Nonempty) :
    (d+1)^n ≤ 2^n*M :=
  (dense_dimension_le_cells_and_samples hm hdm
    (nonempty_halfOpen_grid_card_le_samples X hm hN)).2

/-- The source's actual logarithmic refinement budget is at most a fixed
linear function of M on the observed nonempty branch. The integer constant is
chosen before A, degree, accuracy, observations and signal/noise values. -/
theorem source_refinementBudget_le_samples_linear (n : ℕ) (rho : ℝ)
    (hn : 1 ≤ n) (hrho0 : 0 ≤ rho) (hrho : rho < 1/2) :
    ∃ B : ℕ, ∀ (A : ℝ) (d : ℕ) (eps : ℝ) (_hd : 1 ≤ d)
      (he0 : 0 < eps) (he : eps ≤ 1/2) (M : ℕ)
      (X : Fin M → Point n),
      (∀ j : CellIndex n (SourceComplexity.gridSize A n d rho eps),
        (Finset.univ.filter (fun i => X i ∈ halfOpenCell j)).Nonempty) →
      refinementBudget n d rho eps he0 he ≤ B*(M+1) := by
  obtain ⟨C, hC, hBudget⟩ := SourceComplexity.source_budget_uniform_bound n rho hrho0 hrho
  refine ⟨Nat.ceil C, ?_⟩
  intro A d eps hd he0 he M X hN
  let m := SourceComplexity.gridSize A n d rho eps
  have hm : 0 < m := SourceComplexity.gridSize_pos A n d rho eps
  have hgrid : m^n ≤ M := nonempty_halfOpen_grid_card_le_samples X hm hN
  have hmM : m ≤ M := by
    have hmpow : m ≤ m^n := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      rw [hk, pow_succ]
      have hp : 1 ≤ m^k := pow_pos hm k
      nlinarith
    exact hmpow.trans hgrid
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hscale0 : (0 : ℝ) ≤ d/eps := div_nonneg (Nat.cast_nonneg d) he0.le
  have hfactor : (1 : ℝ) ≤ 72*Real.pi*n := by
    have hp := mul_le_mul_of_nonneg_left hn' Real.pi_pos.le
    nlinarith [Real.two_le_pi]
  have hscale : (d : ℝ)/eps ≤ m := by
    have h := mul_le_mul_of_nonneg_right hfactor hscale0
    have hs : (d : ℝ)/eps ≤ (72*Real.pi*n)*((d : ℝ)/eps) := by
      simpa only [one_mul] using h
    exact hs.trans (SourceComplexity.gridSize_lower A rho n d he0)
  have hmM' : (m : ℝ) ≤ M := by exact_mod_cast hmM
  have hlog : 1 + Real.log ((d : ℝ)/eps) ≤ (M : ℝ)+1 := by
    linarith [Real.log_le_self hscale0]
  have hT := (hBudget d eps hd he0 he).trans (mul_le_mul_of_nonneg_left hlog hC.le)
  have hceil := mul_le_mul_of_nonneg_right (Nat.le_ceil C) (by positivity : (0 : ℝ) ≤ (M : ℝ)+1)
  exact_mod_cast hT.trans hceil

/-- Full source specialization of the finite-loop polynomial witness. Grid
size and refinement count are the paper's actual prescribed choices, and the
m^n≤M bound is proved from actual half-open sample assignment. The constant is
fixed before all varying input parameters and all observed data. -/
theorem source_outside_finite_loop_polynomial (n : ℕ) (rho : ℝ)
    (hn : 1 ≤ n) (hrho0 : 0 ≤ rho) (hrho : rho < 1/2) :
    ∃ K : ℕ, 0 < K ∧ ∀ (A : ℝ) (d : ℕ) (eps : ℝ) (_hd : 1 ≤ d)
      (he0 : 0 < eps) (he : eps ≤ 1/2), 1 ≤ A →
      ∀ (M : ℕ) (X : Fin M → Point n)
        (representatives : CellIndex n (SourceComplexity.gridSize A n d rho eps) → Point n)
        (coefficients : Fin (refinementBudget n d rho eps he0 he) → Exponent n d → ℝ),
        (∀ j : CellIndex n (SourceComplexity.gridSize A n d rho eps),
          (Finset.univ.filter (fun i => X i ∈ halfOpenCell j)).Nonempty) →
        outsideFiniteLoopWork X (fun j => Finset.univ.filter (fun i => X i ∈ halfOpenCell j))
          representatives coefficients ≤ K*M^4 := by
  obtain ⟨B, hB⟩ := source_refinementBudget_le_samples_linear n rho hn hrho0 hrho
  let K := 2*n + (2*n+3)*2^n + 4 + 2*B*(2*(2*n+3)*2^n+6+2^n)
  refine ⟨K, by dsimp [K]; omega, ?_⟩
  intro A d eps hd he0 he hA M X reps coeff hN
  have hm := SourceComplexity.gridSize_pos A n d rho eps
  have hdm := SourceComplexity.degree_le_gridSize (n := n) (d := d) hA hrho0 hrho he0 he
  have hgrid := nonempty_halfOpen_grid_card_le_samples X hm hN
  have hT := hB A d eps hd he0 he M X hN
  exact outsideFiniteLoopWork_le_polynomial X _ reps coeff hm hdm hgrid hT

end
end Paper34
