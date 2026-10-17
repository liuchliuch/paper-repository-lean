import Paper08.PrimitiveInputHeight
import Paper08.MainTheorem

/-! # Complete rational arithmetic expression for the FPTAS

The moment expressions are substituted into the actual recursive logarithm,
then into the actual support extraction and final rational exponential. No
computed moment, coefficient or output is inserted as an input leaf.
-/
open scoped BigOperators
namespace Paper08.FPTASProgram
open RationalProgram PrimitiveProgram PrimitiveIntegralProgram FPTASAlgorithm PrimitiveMomentsQ

/-- Local logarithmic recurrence with actual primitive expressions substituted. -/
def localProgram {n m : ℕ} (scopes : Fin m → Finset (Fin n)) (query : Queries scopes)
    (B : Finset (Fin m)) (j s C : ℕ) (τ : ℚ) : Expr :=
  RationalRecurrenceProgram.recurrenceExpr (fun i => momentExpr scopes query B i s C τ) j

def logProgram {n m : ℕ} (scopes : Fin m → Finset (Fin n)) (query : Queries scopes)
    (r c s C : ℕ) (τ : ℚ) : Expr :=
  sumSet (Finset.Icc 1 s) fun p =>
    letI := pairOrder m
    sumSet (pairs scopes r c s p) fun AB =>
      .node .mul (natPower (.atom (-1)) (AB.1.card-AB.2.card))
        (localProgram scopes query AB.2 p s C τ)

/-- The complete algorithm as a real, operand-sensitive arithmetic program. -/
def runProgram {n m : ℕ} (fixed : Parameters.Fixed) (scopes : Fin m → Finset (Fin n))
    (query : Queries scopes) (r c : ℕ) (ε : ℚ) : Expr :=
  if m = 0 then .atom 1 else
    RationalRecurrenceProgram.rationalExpExpr (logProgram scopes query r c
      (Parameters.truncationOrder fixed m ε) fixed.C
      (Parameters.primitiveTolerance fixed m ε)) ε

@[simp] theorem localProgram_eval {n m : ℕ} (scopes : Fin m → Finset (Fin n)) (query : Queries scopes)
    (B : Finset (Fin m)) (j s C : ℕ) (τ : ℚ) :
    (localProgram scopes query B j s C τ).eval = localCoeff scopes query B j s C τ := by
  simp only [localProgram, RationalRecurrenceProgram.eval_recurrenceExpr, momentExpr_eval, localCoeff]
@[simp] theorem logProgram_eval {n m : ℕ} (scopes : Fin m → Finset (Fin n)) (query : Queries scopes)
    (r c s C : ℕ) (τ : ℚ) :
    (logProgram scopes query r c s C τ).eval = logApprox scopes query r c s C τ := by
  simp [logProgram, logApprox, Expr.eval, Op.eval]
@[simp] theorem runProgram_eval {n m : ℕ} (fixed : Parameters.Fixed) (scopes : Fin m → Finset (Fin n))
    (query : Queries scopes) (r c : ℕ) (ε : ℚ) :
    (runProgram fixed scopes query r c ε).eval = run fixed scopes query r c ε := by
  by_cases hm : m = 0 <;> simp [runProgram, run, hm, RationalRecurrenceProgram.eval_rationalExpExpr, Expr.eval]

def momentNodes (r s P J : ℕ) : ℕ := 4^s*(primitiveNodes r s P J+2*s+2)
def localNodes (r s P J : ℕ) : ℕ := (momentNodes r s P J+1)*2^(s+4)
def logNodes (m r c s P J : ℕ) : ℕ :=
  s*(m*(8*degreeBound r c)^s*(localNodes r s P J+s+2)+1)

theorem localProgram_operations {n m r s C j : ℕ} (scopes : Fin m → Finset (Fin n))
    (hscopes : ∀ e, (scopes e).card ≤ r) (query : Queries scopes)
    (B : Finset (Fin m)) (hB : B.card ≤ s) (hj : j ≤ s) (τ : ℚ) :
    let J := Oracle.totalLevelChoice s C τ
    let P := Oracle.samplePrecision s (Oracle.primitiveSampleTol s J C τ)
    (localProgram scopes query B j s C τ).operations ≤ localNodes r s P J := by
  dsimp only
  have hh := RationalRecurrenceProgram.operations_recurrenceExpr_le
    (fun i => momentExpr scopes query B i s C τ) s j
    (momentNodes r s (Oracle.samplePrecision s (Oracle.primitiveSampleTol s (Oracle.totalLevelChoice s C τ) C τ))
      (Oracle.totalLevelChoice s C τ)) hj
    (fun i _ hi => momentExpr_operations scopes hscopes query B hB hi τ)
  apply hh.trans
  unfold localNodes
  apply Nat.mul_le_mul_left
  exact (Nat.le_add_right _ 4).trans ((BitComplexity.recurrenceOperationCount_le j).trans
    (Nat.pow_le_pow_right (by decide) (by omega)))

theorem logProgram_operations {n m r c s C : ℕ} (scopes : Fin m → Finset (Fin n))
    (hscopes : ∀ e, (scopes e).card ≤ r) (query : Queries scopes) (τ : ℚ) :
    let J := Oracle.totalLevelChoice s C τ
    let P := Oracle.samplePrecision s (Oracle.primitiveSampleTol s J C τ)
    (logProgram scopes query r c s C τ).operations ≤ logNodes m r c s P J := by
  dsimp only
  let J := Oracle.totalLevelChoice s C τ
  let P := Oracle.samplePrecision s (Oracle.primitiveSampleTol s J C τ)
  unfold logProgram
  have hi : ∀ p ∈ Finset.Icc 1 s,
      (letI := pairOrder m
       sumSet (pairs scopes r c s p) fun AB => Expr.node .mul
        (natPower (.atom (-1)) (AB.1.card-AB.2.card))
        (localProgram scopes query AB.2 p s C τ)).operations ≤
          m*(8*degreeBound r c)^s*(localNodes r s P J+s+2) := by
    intro p hp
    letI := pairOrder m
    have hh := sumSet_operations_le (pairs scopes r c s p) (fun AB => Expr.node .mul
      (natPower (.atom (-1)) (AB.1.card-AB.2.card))
      (localProgram scopes query AB.2 p s C τ)) (N := localNodes r s P J+s+1) (by
        intro AB hAB
        have hpair := pair_subset scopes hAB
        have hB := (Finset.card_le_card hpair.1).trans hpair.2
        have hl := localProgram_operations (C := C) scopes hscopes query AB.2 hB (Finset.mem_Icc.mp hp).2 τ
        simp only [Expr.operations, natPower_operations, Nat.zero_add, Nat.mul_one]
        change (localProgram scopes query AB.2 p s C τ).operations ≤ localNodes r s P J at hl
        omega)
    exact hh.trans (Nat.mul_le_mul_right _ (pairs_card scopes))
  have hh := sumSet_operations_le (Finset.Icc 1 s) _ hi
  simpa only [Nat.card_Icc, Nat.add_sub_cancel, Nat.sub_zero] using hh

theorem localProgram_inputHeight {n m r A degree L j s C : ℕ}
    (scopes : Fin m → Finset (Fin n)) (hscopes : ∀ e, (scopes e).card ≤ r)
    (Ψ : (i : Fin m) → (Fin (scopes i).card → ℝ) → ℝ) (labelBits : Fin m → ℕ)
    (O : (i : Fin m) → EffectiveAccess.Oracle (scopes i).card (Ψ i) A degree (labelBits i))
    (hlabels : ∀ i, labelBits i ≤ L) (B : Finset (Fin m)) (hj : j ≤ s) (τ : ℚ) :
    let J := Oracle.totalLevelChoice s C τ
    let P := Oracle.samplePrecision s (Oracle.primitiveSampleTol s J C τ)
    (localProgram scopes (fun i => (O i).valueOracle.query) B j s C τ).inputHeight ≤
      PrimitiveInputHeight.inputBound A degree L r J P s := by
  dsimp only
  apply RationalRecurrenceProgram.inputHeight_recurrenceExpr_le _ s j _ hj
  · dsimp [PrimitiveInputHeight.inputBound]
    omega
  · intro i _ hi
    exact PrimitiveInputHeight.momentExpr_inputHeight_effective scopes hscopes Ψ labelBits O hlabels B hi τ

theorem logProgram_inputHeight {n m r c A degree L s C : ℕ}
    (scopes : Fin m → Finset (Fin n)) (hscopes : ∀ e, (scopes e).card ≤ r)
    (Ψ : (i : Fin m) → (Fin (scopes i).card → ℝ) → ℝ) (labelBits : Fin m → ℕ)
    (O : (i : Fin m) → EffectiveAccess.Oracle (scopes i).card (Ψ i) A degree (labelBits i))
    (hlabels : ∀ i, labelBits i ≤ L) (τ : ℚ) :
    let J := Oracle.totalLevelChoice s C τ
    let P := Oracle.samplePrecision s (Oracle.primitiveSampleTol s J C τ)
    (logProgram scopes (fun i => (O i).valueOracle.query) r c s C τ).inputHeight ≤
      PrimitiveInputHeight.inputBound A degree L r J P s := by
  dsimp only
  have hH : 1 ≤ PrimitiveInputHeight.inputBound A degree L r
      (Oracle.totalLevelChoice s C τ)
      (Oracle.samplePrecision s (Oracle.primitiveSampleTol s (Oracle.totalLevelChoice s C τ) C τ)) s := by
    dsimp [PrimitiveInputHeight.inputBound]
    omega
  unfold logProgram
  apply sumSet_inputHeight _ _ hH
  intro p hp
  letI := pairOrder m
  apply sumSet_inputHeight _ _ hH
  intro AB hAB
  apply max_le
  · apply natPower_inputHeight _ _ hH
    simp [Expr.inputHeight, height]
    exact hH
  · exact localProgram_inputHeight scopes hscopes Ψ labelBits O hlabels AB.2 (Finset.mem_Icc.mp hp).2 τ

/-- The entire executed expression has an explicit polynomial-in-parameters
node bound, including the final rational Taylor expansion and exponentiation. -/
theorem runProgram_operations {n m r c : ℕ} (fixed : Parameters.Fixed)
    (scopes : Fin m → Finset (Fin n)) (hscopes : ∀ e, (scopes e).card ≤ r)
    (query : Queries scopes) (ε : ℚ) (hm : m ≠ 0) :
    let s := Parameters.truncationOrder fixed m ε
    let J := Parameters.level fixed m ε
    let P := Parameters.precision fixed m ε
    let T := logProgram scopes query r c s fixed.C (Parameters.primitiveTolerance fixed m ε)
    let h := Algorithm.exponentialScale T.eval
    let N := Algorithm.exponentialDegree (ε/(12*(2:ℚ)^h))
    (runProgram fixed scopes query r c ε).operations ≤
      2^h*((N+1)*((N+1)*(logNodes m r c s P J+h+3)+2)+1) := by
  dsimp only
  unfold runProgram
  rw [if_neg hm]
  apply (RationalRecurrenceProgram.operations_rationalExpExpr_le _ ε).trans
  have hh := logProgram_operations (s := Parameters.truncationOrder fixed m ε)
    (C := fixed.C) scopes hscopes query (c := c) (Parameters.primitiveTolerance fixed m ε)
  gcongr
  simpa only [Parameters.precision, Parameters.level] using hh


/-- Numeric envelope for the counted arithmetic nodes, using actual parameters. -/
def runNodeBound {n m : ℕ} (fixed : Parameters.Fixed) (scopes : Fin m → Finset (Fin n))
    (query : Queries scopes) (r c : ℕ) (ε : ℚ) : ℕ :=
  let s := Parameters.truncationOrder fixed m ε
  let J := Parameters.level fixed m ε
  let P := Parameters.precision fixed m ε
  let T := logProgram scopes query r c s fixed.C (Parameters.primitiveTolerance fixed m ε)
  let h := Algorithm.exponentialScale T.eval
  let N := Algorithm.exponentialDegree (ε/(12*(2:ℚ)^h))
  2^h*((N+1)*((N+1)*(logNodes m r c s P J+h+3)+2)+1)

/-- Bound for all leaves of the complete expression, from the original access
model and the integer constants used by the final exponential polynomial. -/
def runInputBound {n m : ℕ} (fixed : Parameters.Fixed) (scopes : Fin m → Finset (Fin n))
    (query : Queries scopes) (r c A degree L : ℕ) (ε : ℚ) : ℕ :=
  let s := Parameters.truncationOrder fixed m ε
  let J := Parameters.level fixed m ε
  let P := Parameters.precision fixed m ε
  let T := logProgram scopes query r c s fixed.C (Parameters.primitiveTolerance fixed m ε)
  let h := Algorithm.exponentialScale T.eval
  let N := Algorithm.exponentialDegree (ε/(12*(2:ℚ)^h))
  PrimitiveInputHeight.inputBound A degree L r J P s + N + 3

theorem runProgram_operations_le {n m r c : ℕ} (fixed : Parameters.Fixed)
    (scopes : Fin m → Finset (Fin n)) (hscopes : ∀ e, (scopes e).card ≤ r)
    (query : Queries scopes) (ε : ℚ) :
    (runProgram fixed scopes query r c ε).operations ≤ runNodeBound fixed scopes query r c ε := by
  by_cases hm : m = 0
  · simp only [runProgram, if_pos hm, Expr.operations]
    exact Nat.zero_le _
  · exact runProgram_operations fixed scopes hscopes query ε hm

theorem runProgram_inputHeight {n m r c A degree L : ℕ} (fixed : Parameters.Fixed)
    (scopes : Fin m → Finset (Fin n)) (hscopes : ∀ e, (scopes e).card ≤ r)
    (Ψ : (i : Fin m) → (Fin (scopes i).card → ℝ) → ℝ) (labelBits : Fin m → ℕ)
    (O : (i : Fin m) → EffectiveAccess.Oracle (scopes i).card (Ψ i) A degree (labelBits i))
    (hlabels : ∀ i, labelBits i ≤ L) (ε : ℚ) :
    (runProgram fixed scopes (fun i => (O i).valueOracle.query) r c ε).inputHeight ≤
      runInputBound fixed scopes (fun i => (O i).valueOracle.query) r c A degree L ε := by
  by_cases hm : m = 0
  · simp only [runProgram, if_pos hm, Expr.inputHeight]
    rw [show height (1:ℚ) = 1 by simp [height]]
    dsimp only [runInputBound]
    omega
  · unfold runProgram
    rw [if_neg hm]
    apply RationalRecurrenceProgram.inputHeight_rationalExpExpr_le
    · apply (logProgram_inputHeight (r := r) (c := c)
        (s := Parameters.truncationOrder fixed m ε) (C := fixed.C)
        scopes hscopes Ψ labelBits O hlabels (Parameters.primitiveTolerance fixed m ε)).trans
      change PrimitiveInputHeight.inputBound A degree L r _ _ _ ≤ _
      dsimp [runInputBound, Parameters.level, Parameters.precision]
      omega
    · dsimp [runInputBound]
      omega

/-- Polynomial operand-sensitive work of the complete constructed arithmetic
program, with all input-leaf bounds derived from effective value access. -/
theorem runProgram_work_le {n m r c A degree L : ℕ} (fixed : Parameters.Fixed)
    (scopes : Fin m → Finset (Fin n)) (hscopes : ∀ e, (scopes e).card ≤ r)
    (Ψ : (i : Fin m) → (Fin (scopes i).card → ℝ) → ℝ) (labelBits : Fin m → ℕ)
    (O : (i : Fin m) → EffectiveAccess.Oracle (scopes i).card (Ψ i) A degree (labelBits i))
    (hlabels : ∀ i, labelBits i ≤ L) (ε : ℚ) :
    let N := runNodeBound fixed scopes (fun i => (O i).valueOracle.query) r c ε
    let B := runInputBound fixed scopes (fun i => (O i).valueOracle.query) r c A degree L ε
    (runProgram fixed scopes (fun i => (O i).valueOracle.query) r c ε).work ≤
      N*(4*((B+2)*(N+1))+3)^3 := by
  dsimp only
  have hn := runProgram_operations_le (c := c) fixed scopes hscopes (fun i => (O i).valueOracle.query) ε
  have hb := runProgram_inputHeight (c := c) fixed scopes hscopes Ψ labelBits O hlabels ε
  apply (runProgram fixed scopes (fun i => (O i).valueOracle.query) r c ε).work_le.trans
  gcongr

end Paper08.FPTASProgram
