import Paper08.FPTASProgram
import Paper08.FPTASOracleTime
import Paper08.SchoolbookArithmetic

/-! # Exact binary arithmetic and effective oracle execution of the FPTAS

The result is evaluated by verified long division, multiplication and Euclidean
normalization kernels. Oracle time is accumulated at the actual queried points.
These are traces of the value computation, rather than assumed time bounds.
-/
open scoped BigOperators
namespace Paper08.ImplementedAlgorithm
open PrimitiveMomentsQ

def output {n m : ℕ} (fixed : Parameters.Fixed) (scopes : Fin m → Finset (Fin n))
    (query : Queries scopes) (r c : ℕ) (ε : ℚ) : ℚ :=
  (SchoolbookArithmetic.execute (FPTASProgram.runProgram fixed scopes query r c ε)).1

def arithmeticCost {n m : ℕ} (fixed : Parameters.Fixed) (scopes : Fin m → Finset (Fin n))
    (query : Queries scopes) (r c : ℕ) (ε : ℚ) : ℕ :=
  (SchoolbookArithmetic.execute (FPTASProgram.runProgram fixed scopes query r c ε)).2

@[simp] theorem output_eq {n m : ℕ} (fixed : Parameters.Fixed) (scopes : Fin m → Finset (Fin n))
    (query : Queries scopes) (r c : ℕ) (ε : ℚ) :
    output fixed scopes query r c ε = FPTASAlgorithm.run fixed scopes query r c ε := by
  exact (SchoolbookArithmetic.execute_spec _).1.trans (FPTASProgram.runProgram_eval _ _ _ _ _ _)

theorem arithmeticCost_le {n m r c A degree L : ℕ} (fixed : Parameters.Fixed)
    (scopes : Fin m → Finset (Fin n)) (hscopes : ∀ e, (scopes e).card ≤ r)
    (Ψ : (i : Fin m) → (Fin (scopes i).card → ℝ) → ℝ) (labelBits : Fin m → ℕ)
    (O : (i : Fin m) → EffectiveAccess.Oracle (scopes i).card (Ψ i) A degree (labelBits i))
    (hlabels : ∀ i, labelBits i ≤ L) (ε : ℚ) :
    let N := FPTASProgram.runNodeBound fixed scopes (fun i => (O i).valueOracle.query) r c ε
    let B := FPTASProgram.runInputBound fixed scopes (fun i => (O i).valueOracle.query) r c A degree L ε
    arithmeticCost fixed scopes (fun i => (O i).valueOracle.query) r c ε ≤
      10000*(N*(4*((B+2)*(N+1))+3)^3) := by
  dsimp only
  rw [arithmeticCost, (SchoolbookArithmetic.execute_spec _).2]
  exact (SchoolbookArithmetic.exprBitCost_le _).trans
    (Nat.mul_le_mul_left _ (FPTASProgram.runProgram_work_le (c := c)
      fixed scopes hscopes Ψ labelBits O hlabels ε))

/-- The complete value guarantee applies to the implemented binary-arithmetic
output itself, with only the recorded external nonvanishing theorem exposed. -/
theorem output_correct {n m : ℕ} (p : FPTAS.Params) (fixed : Parameters.Fixed)
    (hb : FPTASCorrectness.FixedBounds p fixed) (E : FactorFamily n p.r m)
    (O : (e : Fin m) → Oracle.Oracle (E e).scope.card (E e).psi.toFun)
    (hc : FamilyBoundedOccurrence E p.c)
    (hE : ∀ e, (E e).RangeOk p.q) (hLip : ∀ e, (E e).LipOk p.K)
    (hne : FPTASCorrectness.CommonNonvanishing p E) {ε : ℚ}
    (hε : 0 < ε) (hεu : ε ≤ 1/2) :
    FPTAS.Accurate
      (output fixed (fun e => (E e).scope) (fun e => (O e).query) p.r p.c ε : ℝ)
      (Integral.partitionFunctionFactor E) (ε : ℝ) := by
  rw [output_eq]
  exact FPTASCorrectness.run_correct_of_common_nonvanishing p fixed hb E O hc hE hLip hne hε hεu

end Paper08.ImplementedAlgorithm
