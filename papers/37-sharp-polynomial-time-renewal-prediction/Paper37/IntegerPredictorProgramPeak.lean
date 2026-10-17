import Paper37.PredictorBatchPeak
import Paper37.IntegerQueryProgramPeak

/-! Closed dynamic representation peak of the complete fixed standard source
predictor AST. The suffix accumulator follows its genuine pair-add recurrence. -/
namespace Paper37.IntegerPredictorProgram
open Paper37.BoundedLoop Paper37.WordProgram Paper37.PredictorBatchProgram
open Paper37.PredictorBatchPeak Paper37.IntegerPredictor

lemma standard_batch_bound (n : ℕ) :
    100000*(100000*(n+2)^3+1000000000000*(n+3)^12+n*(queryBitBound (n+1)+4)+n+10) ≤
      100000000000000000000*(n+3)^13 := by
  let L:=n+3
  have hL : 1≤L := by dsimp [L];omega
  have hD : (n+2)^3≤L^13 :=
    (Nat.pow_le_pow_left (by dsimp [L];omega) 3).trans
      (Nat.pow_le_pow_right hL (by decide))
  have hQ : L^12≤L^13 := Nat.pow_le_pow_right hL (by decide)
  have h5 : L^5≤L^13 := Nat.pow_le_pow_right hL (by decide)
  have h1 : L≤L^13 := by simpa using Nat.pow_le_pow_right hL (show 1≤13 by decide)
  have h4 : 1≤L^4 := by have hp:=Nat.pow_pos (show 0<L by omega) (n:=4);omega
  have hB : queryBitBound (n+1)≤100*L^4 := by
    simpa only [L,Nat.add_assoc] using standard_queryBitBound_le (n+1)
  have hnp : n*(queryBitBound (n+1)+4)≤104*L^13 := by
    calc
      _ ≤n*(104*L^4) := Nat.mul_le_mul_left n (by omega)
      _ ≤L*(104*L^4) := Nat.mul_le_mul_right _ (by dsimp [L];omega)
      _ =104*L^5 := by ring
      _ ≤104*L^13 := Nat.mul_le_mul_left 104 h5
  have hn : n+10≤10*L^13 := by
    have hn0 : n+10≤10*L := by dsimp [L];omega
    exact hn0.trans (Nat.mul_le_mul_left 10 h1)
  have hd := Nat.mul_le_mul_left 100000 hD
  have hq := Nat.mul_le_mul_left 1000000000000 hQ
  change _≤100000000000000000000*L^13
  change 1000000000000*(n+3)^12≤1000000000000*L^13 at hq
  omega

/-- Full own-source intermediate bit/array bound. Only the actual observed
word is constrained; every unrelated initial environment slot remains free. -/
theorem predictorProgram_peak (ρ : Env) (x : List Bool) (hx : ρ 40=wordValue x) :
    predictorProgram.peak ρ≤100000000000000000000*(x.length+3)^13 := by
  let n:=x.length
  let H:=n+1
  let D:=100000*(n+2)^3
  let Q:=1000000000000*(n+3)^12
  let B:=queryBitBound (n+1)
  let f:=fun y : List Bool => conditionalPair (n+1) y
  have hq : PairQueryCorrect conditionalProgram (n+1) f := by
    intro σ y h0 hword hy
    exact conditionalProgram_eval σ (n+1) y h0 hword hy
  have hQ : QueryPeak conditionalProgram (n+1) Q := by
    intro σ y h0 hword hy
    simpa only [Paper37.IntegerQueryProgramPeak.queryPeakBound,Q,Nat.add_assoc] using
      Paper37.IntegerQueryProgramPeak.conditionalProgram_peak σ (n+1) y h0 hword hy
  have hD : DropPeak n D := by
    intro σ y j hword hj hlen hjn
    exact dropProgram_peak σ n y j hword hj hlen hjn
  have hB : ∀ y : List Bool, y.length<n+1 → Paper37.IntegerOutput.pairSize (f y)≤B := by
    intro y hy
    exact conditionalPair_binarySize (n+1) y (by omega) hy
  let ρH:=Function.update ρ 0 (.nat (n+1))
  have hb:=batchProgram_peak conditionalProgram n Q D B f hq hQ hD hB ρH x rfl
    (by simp [ρH]) (by simpa [ρH] using hx)
  have htotal := standard_batch_bound n
  have hbatch : (batchProgram conditionalProgram).peak ρH≤100000000000000000000*(n+3)^13 :=
    hb.trans htotal
  have hword : (Expr.var 40).peak ρ≤2*n+2 := by
    simpa [Expr.peak,Expr.eval,hx,n] using wordValue_size x
  have hlen := length_peak_le (.var 40) ρ (2*n+2) hword
  have hlit : (Expr.lit 1).peak ρ≤2 := by simp [Expr.peak,Expr.eval,Value.representationSize]
  have harith := binary_peak_le .add (.length (.var 40)) (.lit 1) ρ (2*n+3) 2 hlen hlit
  have hL : n+3≤(n+3)^13 := by
    simpa using Nat.pow_le_pow_right (show 1≤n+3 by omega) (show 1≤13 by decide)
  have hhead : (Expr.add (.length (.var 40)) (.lit 1)).peak ρ≤
      100000000000000000000*(n+3)^13 := by
    change (Expr.add (.length (.var 40)) (.lit 1)).peak ρ≤2*((2*n+3)+2+2) at harith
    omega
  have heval : (Expr.add (.length (.var 40)) (.lit 1)).eval ρ=.nat (n+1) := by
    simp [Expr.eval,hx,wordValue_length,n,Value.natVal]
  unfold predictorProgram
  apply (bind_peak_le ρ 0 (.add (.length (.var 40)) (.lit 1)) _).trans
  rw [heval]
  exact max_le hhead hbatch

end Paper37.IntegerPredictorProgram
