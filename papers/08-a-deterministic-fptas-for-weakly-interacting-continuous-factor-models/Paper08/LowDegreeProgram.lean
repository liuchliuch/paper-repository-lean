import Paper08.LowDegreeComplexity
import Paper08.EffectiveAccess
import Paper08.PrimitiveProgram

/-! # Operand-sensitive execution of the degree-one algorithm

The oracle times here are the actual calls at the algorithm's actual rational
corners. The value-access running-time promise is Assumption 1.1, not a bound
assumed on the result of the component algorithm.
-/
open scoped BigOperators
namespace Paper08.LowDegreeAlgorithm
open Integral Oracle

lemma lowDegree_query_bits {n r m L : ℕ} (E : FactorFamily n r m)
    (C : Finset (Fin n)) (z : CellGrid.Grid (levels C L)) (e : Fin m) :
    (∑ j, BitComplexity.rationalBits (localPointQ E C z e j)) ≤ r * (2 * L + 3) := by
  calc
    _ ≤ ∑ _j : Fin (E e).scope.card, (2 * L + 3) :=
      Finset.sum_le_sum fun j _ => localPointQ_bits_le E C z e j
    _ = (E e).scope.card * (2 * L + 3) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (E e).card_le

theorem lowDegree_scope_card_le {n r m : ℕ} (E : FactorFamily n r m)
    (hdeg : FamilyPrimalDegreeLe E 1) (e : Fin m) : (E e).scope.card ≤ 2 :=
  (Finset.card_le_card (scope_subset_owner E e)).trans
    (block_card_le_two E hdeg (owner_mem_blocks E e))

lemma lowDegree_query_bits_two {n r m L : ℕ} (E : FactorFamily n r m)
    (hdeg : FamilyPrimalDegreeLe E 1)
    (C : Finset (Fin n)) (z : CellGrid.Grid (levels C L)) (e : Fin m) :
    (∑ j, BitComplexity.rationalBits (localPointQ E C z e j)) ≤ 2 * (2 * L + 3) := by
  calc
    _ ≤ ∑ _j : Fin (E e).scope.card, (2 * L + 3) :=
      Finset.sum_le_sum fun j _ => localPointQ_bits_le E C z e j
    _ = (E e).scope.card * (2 * L + 3) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (lowDegree_scope_card_le E hdeg e)

lemma lowDegree_query_time {n r m A degree H L b : ℕ} (E : FactorFamily n r m)
    (labelBits : Fin m → ℕ)
    (O : (e : Fin m) → EffectiveAccess.Oracle (E e).scope.card (E e).psi.toFun A degree (labelBits e))
    (hlabels : ∀ e, labelBits e ≤ H) (hb : 1 ≤ b)
    (hdeg : FamilyPrimalDegreeLe E 1)
    (C : Finset (Fin n)) (z : CellGrid.Grid (levels C L)) (e : Fin m) :
    (O e).timeCost (localPointQ E C z e) b ≤ A * (1 + H + b + 2 * (2 * L + 3)) ^ degree := by
  have hh := (O e).time_bound _ b (localPointQ_mem E C z e) hb
  apply hh.trans
  apply Nat.mul_le_mul_left A
  apply Nat.pow_le_pow_left
  have hcoord := lowDegree_query_bits_two E hdeg C z e
  have hlabel := hlabels e
  omega

lemma lowDegree_answer_bits {n r m A degree H L b : ℕ} (E : FactorFamily n r m)
    (labelBits : Fin m → ℕ)
    (O : (e : Fin m) → EffectiveAccess.Oracle (E e).scope.card (E e).psi.toFun A degree (labelBits e))
    (hlabels : ∀ e, labelBits e ≤ H) (hb : 1 ≤ b)
    (hdeg : FamilyPrimalDegreeLe E 1)
    (C : Finset (Fin n)) (z : CellGrid.Grid (levels C L)) (e : Fin m) :
    BitComplexity.rationalBits ((O e).valueOracle.query (localPointQ E C z e) b) ≤
      A * (1 + H + b + 2 * (2 * L + 3)) ^ degree :=
  ((O e).answer_bits_le_time _ b (localPointQ_mem E C z e) hb).trans
    (lowDegree_query_time E labelBits O hlabels hb hdeg C z e)

/-- Instrument every call in the uncached grid/factor loops, with its actual
oracle running time rather than an upper-bound counter. -/
def oracleTime {n r m A degree : ℕ} (E : FactorFamily n r m)
    (labelBits : Fin m → ℕ)
    (O : (e : Fin m) → EffectiveAccess.Oracle (E e).scope.card (E e).psi.toFun A degree (labelBits e))
    (b L : ℕ) : ℕ :=
  ∑ C ∈ blocks E, ∑ z : CellGrid.Grid (levels C L),
    ∑ e ∈ blockFactors E C, (O e).timeCost (localPointQ E C z e) b

theorem oracleTime_le {n r m Δ A degree H b L : ℕ} (E : FactorFamily n r m)
    (labelBits : Fin m → ℕ)
    (O : (e : Fin m) → EffectiveAccess.Oracle (E e).scope.card (E e).psi.toFun A degree (labelBits e))
    (hlabels : ∀ e, labelBits e ≤ H) (hb : 1 ≤ b)
    (hdeg : FamilyPrimalDegreeLe E 1) (hocc : FamilyBoundedOccurrence E Δ) :
    oracleTime E labelBits O b L ≤
      (n * (2 * Δ) * 2 ^ (2 * L)) * (A * (1 + H + b + 2 * (2 * L + 3)) ^ degree) := by
  calc
    _ ≤ ∑ C ∈ blocks E, ∑ _z : CellGrid.Grid (levels C L),
        ∑ _e ∈ blockFactors E C, A * (1 + H + b + 2 * (2 * L + 3)) ^ degree := by
      apply Finset.sum_le_sum
      intro C hC
      apply Finset.sum_le_sum
      intro z _
      exact Finset.sum_le_sum fun e _ => lowDegree_query_time E labelBits O hlabels hb hdeg C z e
    _ = queryCalls E L * (A * (1 + H + b + 2 * (2 * L + 3)) ^ degree) := by
      simp_rw [← Finset.sum_mul]
      simp [queryCalls, Finset.mul_sum, Finset.sum_mul, Nat.mul_assoc]
    _ ≤ _ := Nat.mul_le_mul_right _ (queryCalls_le E hdeg hocc L)

open RationalProgram PrimitiveProgram

/-- The actual arithmetic for one answer: scale, floor, divide and clip.
Powers are built by multiplication nodes rather than provided as result leaves. -/
def sampleProgram (U b : ℕ) (answer : ℚ) : Expr :=
  .node .min (.atom U) (.node .max (.atom 1)
    (.node .div (.floor (.node .mul (.atom answer) (natPower (.atom 2) b)))
      (natPower (.atom 2) b)))

@[simp] theorem sampleProgram_eval (U b : ℕ) (answer : ℚ) :
    (sampleProgram U b answer).eval = projectQ U (Oracle.dyadQ b answer) := by
  simp [sampleProgram, Expr.eval, Op.eval, projectQ, Oracle.dyadQ]

@[simp] theorem sampleProgram_operations (U b : ℕ) (answer : ℚ) :
    (sampleProgram U b answer).operations = 2 * b + 5 := by
  simp [sampleProgram, Expr.operations, natPower_operations]
  omega

/-- The cell weight is also computed by rational operations. -/
def weightProgram {n : ℕ} (C : Finset (Fin n)) (L : ℕ) : Expr :=
  .node .div (.atom 1) (natPower (.atom 2) (L * C.card))

@[simp] theorem weightProgram_eval {n : ℕ} (C : Finset (Fin n)) (L : ℕ) :
    (weightProgram C L).eval = CellGrid.weightQ (levels C L) := by
  simp [weightProgram, Expr.eval, Op.eval, CellGrid.weightQ, sum_levels, Nat.mul_comm]

@[simp] theorem weightProgram_operations {n : ℕ} (C : Finset (Fin n)) (L : ℕ) :
    (weightProgram C L).operations = L * C.card + 1 := by
  simp [weightProgram, Expr.operations]

/-- A concrete sorted traversal of the component's actual grid and factors. -/
def componentProgram {n r m : ℕ} (E : FactorFamily n r m)
    (query : (e : Fin m) → (Fin (E e).scope.card → ℚ) → ℕ → ℚ)
    (U b L : ℕ) (C : Finset (Fin n)) : Expr :=
  letI := gridOrder (levels C L)
  sumSet Finset.univ (fun z : CellGrid.Grid (levels C L) =>
    .node .mul (weightProgram C L)
      (productSet (blockFactors E C) (fun e =>
        sampleProgram U b (query e (localPointQ E C z e) b))))

@[simp] theorem componentProgram_eval {n r m : ℕ} (E : FactorFamily n r m)
    (query : (e : Fin m) → (Fin (E e).scope.card → ℚ) → ℕ → ℚ)
    (U b L : ℕ) (C : Finset (Fin n)) :
    (componentProgram E query U b L C).eval = componentEstimateQ E query U b L C := by
  simp [componentProgram, componentEstimateQ, Expr.eval, Op.eval, sampleQ]

/-- The arithmetic expression produces the actual algorithm's returned rational. -/
def outputProgram {n r m : ℕ} (E : FactorFamily n r m)
    (query : (e : Fin m) → (Fin (E e).scope.card → ℚ) → ℕ → ℚ)
    (U b L : ℕ) : Expr :=
  letI := finsetOrder n
  productSet (blocks E) (componentProgram E query U b L)

@[simp] theorem outputProgram_eval {n r m : ℕ} (E : FactorFamily n r m)
    (query : (e : Fin m) → (Fin (E e).scope.card → ℚ) → ℕ → ℚ)
    (U b L : ℕ) : (outputProgram E query U b L).eval = outputQ E query U b L := by
  simp [outputProgram, outputQ]

@[simp] theorem componentProgram_operations {n r m : ℕ} (E : FactorFamily n r m)
    (query : (e : Fin m) → (Fin (E e).scope.card → ℚ) → ℕ → ℚ)
    (U b L : ℕ) (C : Finset (Fin n)) :
    (componentProgram E query U b L C).operations =
      Fintype.card (CellGrid.Grid (levels C L)) *
        ((blockFactors E C).card * (2 * b + 6) + L * C.card + 3) := by
  simp [componentProgram, sumSet_operations, productSet_operations, Expr.operations,
    weightProgram_operations, sampleProgram_operations]
  ring

/-- Actual rational-operation count, including all powers, floors and clips. -/
theorem outputProgram_operations_le {n r m Δ : ℕ} (E : FactorFamily n r m)
    (query : (e : Fin m) → (Fin (E e).scope.card → ℚ) → ℕ → ℚ)
    (hdeg : FamilyPrimalDegreeLe E 1) (hocc : FamilyBoundedOccurrence E Δ)
    (U b L : ℕ) : (outputProgram E query U b L).operations ≤
      n * (2 ^ (2 * L) * ((2 * Δ) * (2 * b + 6) + 2 * L + 3) + 1) := by
  have hc : ∀ C ∈ blocks E, (componentProgram E query U b L C).operations ≤
      2 ^ (2 * L) * ((2 * Δ) * (2 * b + 6) + 2 * L + 3) := by
    intro C hC
    rw [componentProgram_operations]
    apply Nat.mul_le_mul (grid_card_le E hdeg hC L)
    have ht := blockFactors_card_le E hdeg hocc hC
    have hcard := block_card_le_two E hdeg hC
    nlinarith
  letI := finsetOrder n
  unfold outputProgram
  exact (productSet_operations_le _ _ hc).trans (Nat.mul_le_mul_right _ (blocks_card_le E))

lemma height_le_bits (q : ℚ) : RationalProgram.height q ≤ BitComplexity.rationalBits q := by
  unfold RationalProgram.height BitComplexity.rationalBits
  omega

lemma nat_height_le (U : ℕ) : RationalProgram.height (U : ℚ) ≤ Nat.clog 2 U + 3 := by
  apply (height_le_bits _).trans
  simpa using rationalBits_of_dyadic (nat_isDyadicAt U 0) (by
    simpa only [Rat.cast_natCast, abs_of_nonneg (show (0 : ℝ) ≤ (U : ℝ) by positivity)] using
      (show (U : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 U by
        exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) U))

/-- A polynomial input-encoding bound derived from effective value access. -/
def programHeight (A degree H U b L : ℕ) : ℕ :=
  A * (1 + H + b + 2 * (2 * L + 3)) ^ degree + Nat.clog 2 U + 5

lemma height_two_le : RationalProgram.height (2 : ℚ) ≤ 2 := by
  norm_num [RationalProgram.height]
  exact Nat.size_le.mpr (by norm_num)

lemma sampleProgram_inputHeight (U b : ℕ) (answer : ℚ) {B : ℕ}
    (hB : 2 ≤ B) (hU : RationalProgram.height (U : ℚ) ≤ B)
    (hanswer : RationalProgram.height answer ≤ B) :
    (sampleProgram U b answer).inputHeight ≤ B := by
  have hp : (natPower (.atom 2) b).inputHeight ≤ B :=
    natPower_inputHeight _ _ (by omega) (height_two_le.trans hB)
  simp only [sampleProgram, Expr.inputHeight]
  exact max_le hU (max_le (by norm_num [RationalProgram.height]; omega)
    (max_le (max_le hanswer hp) hp))

lemma weightProgram_inputHeight {n : ℕ} (C : Finset (Fin n)) (L : ℕ) {B : ℕ}
    (hB : 2 ≤ B) : (weightProgram C L).inputHeight ≤ B := by
  exact max_le (by norm_num [Expr.inputHeight, RationalProgram.height]; omega)
    (natPower_inputHeight _ _ (by omega) (height_two_le.trans hB))

/-- Every leaf's actual encoding is polynomially bounded; this is derived from
the oracle's original time promise at the actual corner queries. -/
theorem outputProgram_inputHeight {n r m A degree H : ℕ} (E : FactorFamily n r m)
    (labelBits : Fin m → ℕ)
    (O : (e : Fin m) → EffectiveAccess.Oracle (E e).scope.card (E e).psi.toFun A degree (labelBits e))
    (hlabels : ∀ e, labelBits e ≤ H) (hdeg : FamilyPrimalDegreeLe E 1)
    (U b L : ℕ) (hb : 1 ≤ b) :
    (outputProgram E (fun e => (O e).valueOracle.query) U b L).inputHeight ≤
      programHeight A degree H U b L := by
  let B := programHeight A degree H U b L
  have hB : 2 ≤ B := by dsimp [B, programHeight]; omega
  letI := finsetOrder n
  unfold outputProgram
  apply productSet_inputHeight _ _ (by omega : 1 ≤ B)
  intro C hC
  letI := gridOrder (levels C L)
  unfold componentProgram
  apply sumSet_inputHeight _ _ (by omega : 1 ≤ B)
  intro z _
  apply max_le (weightProgram_inputHeight C L hB)
  apply productSet_inputHeight _ _ (by omega : 1 ≤ B)
  intro e _
  apply sampleProgram_inputHeight _ _ _ hB
  · have hu := nat_height_le U
    dsimp [B, programHeight]
    omega
  · have hh := (height_le_bits _).trans (lowDegree_answer_bits E labelBits O hlabels hb hdeg C z e)
    dsimp [B, programHeight]
    omega

/-- The actual operand-weighted arithmetic work is polynomial in the stated
parameters. Its bound counts the full sample arithmetic, not only output bits. -/
theorem outputProgram_work_le {n r m Δ A degree H : ℕ} (E : FactorFamily n r m)
    (labelBits : Fin m → ℕ)
    (O : (e : Fin m) → EffectiveAccess.Oracle (E e).scope.card (E e).psi.toFun A degree (labelBits e))
    (hlabels : ∀ e, labelBits e ≤ H) (hdeg : FamilyPrimalDegreeLe E 1)
    (hocc : FamilyBoundedOccurrence E Δ) (U b L : ℕ) (hb : 1 ≤ b) :
    let N := n * (2 ^ (2 * L) * ((2 * Δ) * (2 * b + 6) + 2 * L + 3) + 1)
    let B := programHeight A degree H U b L
    (outputProgram E (fun e => (O e).valueOracle.query) U b L).work ≤
      N * (4 * ((B + 2) * (N + 1)) + 3) ^ 3 := by
  dsimp only
  have ho := outputProgram_operations_le E (fun e => (O e).valueOracle.query) hdeg hocc U b L
  have hi := outputProgram_inputHeight E labelBits O hlabels hdeg U b L hb
  apply (Expr.work_le _).trans
  apply Nat.mul_le_mul ho
  apply Nat.pow_le_pow_left
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul_left
  exact Nat.mul_le_mul (Nat.add_le_add_right hi 2) (Nat.add_le_add_right ho 1)

/-- The expression at the algorithm's selected precisions. -/
def runProgram {n r m : ℕ} (E : FactorFamily n r m)
    (query : (e : Fin m) → (Fin (E e).scope.card → ℚ) → ℕ → ℚ)
    (Δ U T : ℕ) (ε : ℚ) : Expr :=
  outputProgram E query U (answerBits Δ U n ε) (meshLevel T n ε)

@[simp] theorem runProgram_eval {n r m : ℕ} (E : FactorFamily n r m)
    (query : (e : Fin m) → (Fin (E e).scope.card → ℚ) → ℕ → ℚ)
    (Δ U T : ℕ) (ε : ℚ) : (runProgram E query Δ U T ε).eval = runQ E query Δ U T ε := by
  exact outputProgram_eval E query U _ _

/-- Eliminating the grid exponential makes the polynomial size of the
actual selected arithmetic expression explicit. -/
theorem runProgram_operations_le {n r m Δ : ℕ} (E : FactorFamily n r m)
    (query : (e : Fin m) → (Fin (E e).scope.card → ℚ) → ℕ → ℚ)
    (hdeg : FamilyPrimalDegreeLe E 1) (hocc : FamilyBoundedOccurrence E Δ)
    (U T : ℕ) (ε : ℚ) :
    let b := answerBits Δ U n ε
    let L := meshLevel T n ε
    let M := 2 * (⌈((4 * T * n : ℕ) : ℚ) / ε⌉₊ + 1)
    (runProgram E query Δ U T ε).operations ≤
      n * (M ^ 2 * ((2 * Δ) * (2 * b + 6) + 2 * L + 3) + 1) := by
  dsimp only
  apply (outputProgram_operations_le E query hdeg hocc U _ _).trans
  apply Nat.mul_le_mul_left n
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul_right
  have hh := dyadicPrecision_pow_le (4 * T * n) ε
  change 2 ^ (2 * meshLevel T n ε) ≤ _
  rw [Nat.mul_comm 2 _, pow_mul]
  exact Nat.pow_le_pow_left hh 2

/-- At the selected precisions, arithmetic work plus the actual accumulated
oracle running time has a polynomial bound. The only value-access complexity
assumptions are those already in the original effective oracle model. -/
theorem runProgram_total_work_le {n r m Δ A degree H : ℕ} (E : FactorFamily n r m)
    (labelBits : Fin m → ℕ)
    (O : (e : Fin m) → EffectiveAccess.Oracle (E e).scope.card (E e).psi.toFun A degree (labelBits e))
    (hlabels : ∀ e, labelBits e ≤ H) (hdeg : FamilyPrimalDegreeLe E 1)
    (hocc : FamilyBoundedOccurrence E Δ) (U T : ℕ) (ε : ℚ) :
    let b := answerBits Δ U n ε
    let L := meshLevel T n ε
    let M := 2 * (⌈((4 * T * n : ℕ) : ℚ) / ε⌉₊ + 1)
    let N := n * (M ^ 2 * ((2 * Δ) * (2 * b + 6) + 2 * L + 3) + 1)
    let B := programHeight A degree H U b L
    (runProgram E (fun e => (O e).valueOracle.query) Δ U T ε).work + oracleTime E labelBits O b L ≤
      N * (4 * ((B + 2) * (N + 1)) + 3) ^ 3 +
      (n * (2 * Δ) * M ^ 2) * (A * (1 + H + b + 2 * (2 * L + 3)) ^ degree) := by
  dsimp only
  have hb := dyadicPrecision_pos (4 * (2 * Δ) * U ^ (2 * Δ - 1) * n) ε
  have ho := runProgram_operations_le E (fun e => (O e).valueOracle.query) hdeg hocc U T ε
  dsimp only at ho
  have hi := outputProgram_inputHeight E labelBits O hlabels hdeg U (answerBits Δ U n ε) (meshLevel T n ε) hb
  have hw := (runProgram E (fun e => (O e).valueOracle.query) Δ U T ε).work_le
  have hw' := hw.trans (Nat.mul_le_mul ho (Nat.pow_le_pow_left
    (Nat.add_le_add_right (Nat.mul_le_mul_left 4 (Nat.mul_le_mul
      (Nat.add_le_add_right hi 2) (Nat.add_le_add_right ho 1))) 3) 3))
  apply Nat.add_le_add hw'
  apply (oracleTime_le E labelBits O hlabels hb hdeg hocc).trans
  apply Nat.mul_le_mul_right
  apply Nat.mul_le_mul_left
  have hh := dyadicPrecision_pow_le (4 * T * n) ε
  rw [Nat.mul_comm 2 _, pow_mul]
  exact Nat.pow_le_pow_left hh 2

/-- An explicit polynomial in n/ε, the selected logarithmic precisions,
and the fixed effective-access parameters. -/
def totalWorkBound (n Δ A degree H U T : ℕ) (ε : ℚ) : ℕ :=
  let b := answerBits Δ U n ε
  let L := meshLevel T n ε
  let M := 2 * (⌈((4 * T * n : ℕ) : ℚ) / ε⌉₊ + 1)
  let N := n * (M ^ 2 * ((2 * Δ) * (2 * b + 6) + 2 * L + 3) + 1)
  let B := programHeight A degree H U b L
  N * (4 * ((B + 2) * (N + 1)) + 3) ^ 3 +
    (n * (2 * Δ) * M ^ 2) * (A * (1 + H + b + 2 * (2 * L + 3)) ^ degree)

/-- Actual rational-arithmetic work and actual oracle running time of one run. -/
def actualTotalWork {n r m A degree : ℕ} (E : FactorFamily n r m)
    (labelBits : Fin m → ℕ)
    (O : (e : Fin m) → EffectiveAccess.Oracle (E e).scope.card (E e).psi.toFun A degree (labelBits e))
    (Δ U T : ℕ) (ε : ℚ) : ℕ :=
  (runProgram E (fun e => (O e).valueOracle.query) Δ U T ε).work +
    oracleTime E labelBits O (answerBits Δ U n ε) (meshLevel T n ε)

/-- Lemma A.1: one actual rational algorithm has the claimed multiplicative
accuracy and polynomial operand-sensitive work under Assumption 1.1. -/
theorem lemma_A1_effective {n r m Δ A degree H : ℕ} (E : FactorFamily n r m)
    (labelBits : Fin m → ℕ)
    (O : (e : Fin m) → EffectiveAccess.Oracle (E e).scope.card (E e).psi.toFun A degree (labelBits e))
    (hlabels : ∀ e, labelBits e ≤ H)
    (hdeg : FamilyPrimalDegreeLe E 1) (hocc : FamilyBoundedOccurrence E Δ)
    {U K : ℝ} (hU : 1 < U) (hK : 0 < K)
    (hrange : ∀ e x, x ∈ cube (E e).scope.card →
      1 ≤ (E e).psi.toFun x ∧ (E e).psi.toFun x ≤ U)
    (hLip : ∀ e, (E e).LipOk K) (ε : ℚ) (hε : 0 < ε) :
    FPTAS.Accurate
      ((runProgram E (fun e => (O e).valueOracle.query) Δ (rangeBound U) (lipBudget Δ K U) ε).eval : ℝ)
      (partitionFunctionFactor E) ε ∧
    actualTotalWork E labelBits O Δ (rangeBound U) (lipBudget Δ K U) ε ≤
      totalWorkBound n Δ A degree H (rangeBound U) (lipBudget Δ K U) ε := by
  constructor
  · rw [runProgram_eval]
    exact lemma_A1_accuracy_all E (fun e => (O e).valueOracle) hdeg hocc hU hK hrange hLip ε hε
  · exact runProgram_total_work_le E labelBits O hlabels hdeg hocc _ _ ε

/-- The η=1 branch of the original corollary, including bit-sensitive work. -/
theorem corollary_1_3_eta_one_effective {n r m Δ A degree H : ℕ} (E : FactorFamily n r m)
    (labelBits : Fin m → ℕ)
    (O : (e : Fin m) → EffectiveAccess.Oracle (E e).scope.card (E e).psi.toFun A degree (labelBits e))
    (hlabels : ∀ e, labelBits e ≤ H)
    (hdeg : FamilyPrimalDegreeLe E 1) (hocc : FamilyBoundedOccurrence E Δ)
    {δ K : ℝ} (hρ : 1 < FPTAS.gamarnikSmediraRho Δ 1 δ) (hK : 0 < K)
    (hrange : ∀ e x, x ∈ cube (E e).scope.card →
      1 ≤ (E e).psi.toFun x ∧ (E e).psi.toFun x ≤ FPTAS.gamarnikSmediraRho Δ 1 δ)
    (hLip : ∀ e, (E e).LipOk K) (ε : ℚ) (hε : 0 < ε) :
    let U := rangeBound (FPTAS.gamarnikSmediraRho Δ 1 δ)
    let T := lipBudget Δ K (FPTAS.gamarnikSmediraRho Δ 1 δ)
    FPTAS.Accurate ((runProgram E (fun e => (O e).valueOracle.query) Δ U T ε).eval : ℝ)
      (partitionFunctionFactor E) ε ∧
    actualTotalWork E labelBits O Δ U T ε ≤ totalWorkBound n Δ A degree H U T ε :=
  lemma_A1_effective E labelBits O hlabels hdeg hocc hρ hK hrange hLip ε hε

end Paper08.LowDegreeAlgorithm
