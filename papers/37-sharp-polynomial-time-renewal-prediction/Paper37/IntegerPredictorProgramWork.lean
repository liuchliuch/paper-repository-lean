import Paper37.IntegerPredictorProgram
import Paper37.PredictorBatchProgramWork
import Paper37.WordProgramWork
import Paper37.CachedCoreWork

namespace Paper37.IntegerPredictorProgram
open Paper37.BoundedLoop Paper37.WordProgram Paper37.PredictorBatchProgram
open Paper37.IntegerPredictor Paper37.CachedDP Paper37.CachedCoreProgram
open Paper37.CacheBuilderProgram Paper37.CachedOutput Paper37.ContinuationDP
open Paper37.Envelope
set_option linter.unusedSimpArgs false
private abbrev v := Expr.var

lemma continuationBody_work (ρ : Env) (H : ℕ) (z : List Bool) (R : ℕ)
    (hH : ρ 0=.nat H) (h2 : ρ 2=chooseValue (makeObservedCache H z))
    (h3 : ρ 3=powerValue (makeObservedCache H z)) (hR : ρ 12=.nat R)
    (hs : ρ 58=.array [.nat (parseAge 0 z),.nat (parseGaps 0 z).length,
      observedValue (makeObservedCache H z)]) (hz : z.length+R≤H) :
    continuationBody.work ρ≤500*(H+1)^4 := by
  let c:=makeObservedCache H z
  let A:=parseAge 0 z
  let r:=(parseGaps 0 z).length
  let ρA:=Function.update ρ 1 (.nat A)
  let ρr:=Function.update ρA 11 (.nat r)
  let ρa:=Function.update ρr 4 (observedValue c)
  have hcore:=coreProgram_eval c A ρa (by simpa [ρa,ρr,ρA] using hH)
    (by simp [ρa,ρr,ρA]) (by simpa [ρa,ρr,ρA,c] using h2)
    (by simpa [ρa,ρr,ρA,c] using h3) (by simp [ρa])
  have hwcore:=coreProgram_work_le ρa H (by simpa [ρa,ρr,ρA] using hH)
  let table:=cachedRun H c A H
  let ρt:=Function.update ρa 5 (layerValue table)
  have hout : Paper37.IntegerOutputProgram.Inputs ρt c A table r R := by
    constructor
    · simpa [ρt,ρa,ρr,ρA] using hH
    · simp [ρt,ρa,ρr,ρA]
    · simpa [ρt,ρa,ρr,ρA,c] using h3
    · simp [ρt,ρa]
    · simp [ρt]
    · simp [ρt,ρa,ρr]
    · simpa [ρt,ρa,ρr,ρA] using hR
  have hwout:=Paper37.IntegerOutputProgram.outputProgram_work_quadratic hout
    (by have ha:=age_le_length z;dsimp [A];omega)
  have hp4 : 1≤(H+1)^4 := by
    have hh : 0<(H+1)^4 := by positivity
    omega
  have hpow : (H+1)^2≤(H+1)^4 := Nat.pow_le_pow_right (by omega) (by decide)
  simp only [continuationBody,Expr.work,Expr.eval,hs]
  simp only [Function.update_of_ne (by decide : (58:ℕ)≠1),
    Function.update_of_ne (by decide : (58:ℕ)≠11),Value.arrayVal,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,hs,Value.natVal]
  change 3+1+(3+1+(3+1+(coreProgram.work ρa+1+
    Paper37.IntegerOutputProgram.outputProgram.work (Function.update ρa 5 (coreProgram.eval ρa)))))≤_
  rw [hcore]
  change 3+1+(3+1+(3+1+(coreProgram.work ρa+1+
    Paper37.IntegerOutputProgram.outputProgram.work ρt)))≤_
  omega

/-- Actual work of the single complete continuation AST, including parsed
histograms and both coefficient caches. -/
theorem continuationProgram_work (ρ : Env) (H : ℕ) (z : List Bool) (R : ℕ)
    (hH : ρ 0=.nat H) (hword : ρ 40=wordValue z) (hR : ρ 12=.nat R)
    (hz : z.length+R≤H) :
    continuationProgram.work ρ≤1000*(H+1)^4 := by
  have hchoose:=chooseProgram_source ρ H z hH
  have hwchoose:=chooseProgram_work_cubic ρ H hH
  let ρc:=Function.update ρ 2 (chooseValue (makeObservedCache H z))
  have hpower:=powerProgram_source ρc H z (by simpa [ρc] using hH)
  have hwpower:=powerProgram_work_quadratic ρc H (by simpa [ρc] using hH)
  let ρp:=Function.update ρc 3 (powerValue (makeObservedCache H z))
  have hparse:=parserProgram_eval_source ρp H z (by simpa [ρp,ρc] using hH)
    (by simpa [ρp,ρc] using hword)
  have hwparse:=parserProgram_work ρp H z (by simpa [ρp,ρc] using hH)
    (by simpa [ρp,ρc] using hword)
  let ρs:=Function.update ρp 58 (.array [.nat (parseAge 0 z),.nat (parseGaps 0 z).length,
      observedValue (makeObservedCache H z)])
  have hwbody:=continuationBody_work ρs H z R (by simpa [ρs,ρp,ρc] using hH)
    (by simp [ρs,ρp,ρc]) (by simp [ρs,ρp]) (by simpa [ρs,ρp,ρc] using hR)
    (by simp [ρs]) hz
  have hp4 : 1≤(H+1)^4 := by
    have hh : 0<(H+1)^4 := by positivity
    omega
  have hpow2 : (H+1)^2≤(H+1)^4 := Nat.pow_le_pow_right (by omega) (by decide)
  have hpow3 : (H+1)^3≤(H+1)^4 := Nat.pow_le_pow_right (by omega) (by decide)
  have hparsebound : 150*(H+1)*(z.length+1)≤150*(H+1)^2 := by
    have hlen : z.length+1≤H+1 := by omega
    calc _ ≤150*(H+1)*(H+1) := Nat.mul_le_mul_left _ hlen
         _ =_ := by ring
  rw [continuationProgram,Expr.work,hchoose]
  change chooseProgram.work ρ+1+
    (Expr.bind 3 powerProgram (.bind 58 parserProgram continuationBody)).work ρc≤_
  rw [Expr.work,hpower]
  change chooseProgram.work ρ+1+(powerProgram.work ρc+1+
    (Expr.bind 58 parserProgram continuationBody).work ρp)≤_
  rw [Expr.work,hparse]
  change chooseProgram.work ρ+1+(powerProgram.work ρc+1+
    (parserProgram.work ρp+1+continuationBody.work ρs))≤_
  omega

lemma childProgram_work (ρ : Env) (H L : ℕ) (z : List Bool) (b : Bool)
    (hH : ρ 0=.nat H) (hLslot : ρ 48=.nat L) (hword : ρ 40=wordValue z)
    (hbit : ρ 46=bitValue b) (hL : L≤H) (hz : z.length<L) :
    childProgram.work ρ≤1100*(H+1)^4 := by
  let R:=L-(z.length+1)
  let ρR:=Function.update ρ 12 (.nat R)
  have happend:=appendProgram_eval ρR z b (by simpa [ρR] using hword)
    (by simpa [ρR] using hbit)
  have hwappend:=appendProgram_work ρR z (by simpa [ρR] using hword)
  let ρb:=Function.update ρR 40 (wordValue (z++[b]))
  have hwcont:=continuationProgram_work ρb H (z++[b]) R
    (by simpa [ρb,ρR] using hH) (by simp [ρb]) (by simp [ρb,ρR]) (by simp;omega)
  have hlin : z.length+1≤(H+1)^4 := by
    have hlin' : H+1≤(H+1)^4 := le_self_pow₀ (by omega) (by decide)
    omega
  simp only [childProgram,Expr.work,Expr.eval,hLslot,hword,wordValue_length,Value.natVal]
  change 1+(2+1+1)+1+1+(appendProgram.work ρR+1+
    continuationProgram.work (Function.update ρR 40 (appendProgram.eval ρR)))≤_
  rw [happend]
  change 1+(2+1+1)+1+1+(appendProgram.work ρR+1+continuationProgram.work ρb)≤_
  omega

lemma visibleProgram_work (ρ : Env) (H L : ℕ) (z : List Bool)
    (hH : ρ 0=.nat H) (hLslot : ρ 48=.nat L) (hword : ρ 40=wordValue z)
    (hL : L≤H) (hz : z.length<L) :
    visibleProgram.work ρ≤2300*(H+1)^4 := by
  let p:=evaluatePair H (z++[false]) (L-(z.length+1))
  let ρ₀:=Function.update ρ 46 (.nat 0)
  have hfalse:=childProgram_eval ρ₀ H L z false (by simpa [ρ₀] using hH)
    (by simpa [ρ₀] using hLslot) (by simpa [ρ₀] using hword) (by rfl) hL hz
  have hwfalse:=childProgram_work ρ₀ H L z false (by simpa [ρ₀] using hH)
    (by simpa [ρ₀] using hLslot) (by simpa [ρ₀] using hword) (by rfl) hL hz
  let ρp:=Function.update ρ₀ 55 (pairValue p)
  let ρ₁:=Function.update ρp 46 (.nat 1)
  have hwtrue:=childProgram_work ρ₁ H L z true (by simpa [ρ₁,ρp,ρ₀] using hH)
    (by simpa [ρ₁,ρp,ρ₀] using hLslot) (by simpa [ρ₁,ρp,ρ₀] using hword) (by rfl) hL hz
  have hp4 : 1≤(H+1)^4 := by
    have hh : 0<(H+1)^4 := by positivity
    omega
  have harray (σ : Env) : visibleArray.work σ=13 := by simp [visibleArray,Expr.work]
  rw [visibleProgram,Expr.work,Expr.eval]
  simp only [Expr.work,Expr.eval]
  change 1+1+(childProgram.work ρ₀+1+(1+1+
    (childProgram.work (Function.update (Function.update ρ₀ 55 (childProgram.eval ρ₀)) 46 (.nat 1))+1+_)))≤_
  rw [hfalse]
  change 1+1+(childProgram.work ρ₀+1+(1+1+(childProgram.work ρ₁+1+_)))≤_
  rw [harray]
  omega

/-- Actual charge of the complete first-renewal conditional branch. -/
theorem conditionalProgram_work (ρ : Env) (H : ℕ) (y : List Bool)
    (hH : ρ 0=.nat H) (hword : ρ 40=wordValue y) (hy : y.length<H) :
    conditionalProgram.work ρ≤2500*(H+1)^4 := by
  let ρlen:=Function.update ρ 49 (.nat y.length)
  have hidx:=firstIndexProgram_eval ρlen y (by simpa [ρlen] using hword)
  have hwidx:=firstIndexProgram_work ρlen y (by simpa [ρlen] using hword)
  let ρidx:=Function.update ρlen 47 (.nat (firstIndex y))
  have hp4 : 1≤(H+1)^4 := by
    have hh : 0<(H+1)^4 := by positivity
    omega
  have hlin : y.length+1≤(H+1)^4 := by
    have hh : H+1≤(H+1)^4 := le_self_pow₀ (by omega) (by decide)
    omega
  cases hs : Paper37.Prediction.firstSuffix y with
  | none =>
    have hi:=firstIndex_none y hs
    simp only [conditionalProgram,Expr.work,Expr.eval,hword,wordValue_length]
    dsimp only [ρlen] at hidx hwidx
    rw [hidx]
    simp only [Function.update_apply,if_true,show (49:ℕ)≠47 by decide,if_false,
      Value.natVal,hi,lt_self_iff_false]
    simp only [Expr.work,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    omega
  | some z =>
    obtain ⟨hlen,hdrop⟩:=firstIndex_some y z hs
    have hi : firstIndex y<y.length := by omega
    let ρd:=Function.update ρidx 44 (.nat (firstIndex y+1))
    have hdropEval:=dropProgram_eval ρd y (firstIndex y+1)
      (by simpa [ρd,ρidx,ρlen] using hword) (by simp [ρd])
    rw [hdrop] at hdropEval
    have hwDrop:=dropProgram_work ρd y (firstIndex y+1)
      (by simpa [ρd,ρidx,ρlen] using hword) (by simp [ρd])
    let ρz:=Function.update ρd 40 (wordValue z)
    have hwvisible:=visibleProgram_work (Function.update ρz 48 (.nat (H-y.length+z.length))) H
      (H-y.length+z.length) z (by simpa [ρz,ρd,ρidx,ρlen] using hH) (by simp)
      (by simp [ρz]) (by omega) (by omega)
    simp only [conditionalProgram,Expr.work,Expr.eval,hword,wordValue_length]
    dsimp only [ρlen] at hidx hwidx
    rw [hidx]
    simp only [Function.update_apply,if_true,show (49:ℕ)≠47 by decide,if_false,
      Value.natVal,hi,if_true]
    dsimp only [ρd,ρidx,ρlen] at hdropEval hwDrop
    rw [hdropEval]
    simp only [Function.update_apply,if_true,
      show (0:ℕ)≠40 by decide,show (0:ℕ)≠44 by decide,
      show (0:ℕ)≠47 by decide,show (0:ℕ)≠49 by decide,
      show (49:ℕ)≠40 by decide,show (49:ℕ)≠44 by decide,
      show (49:ℕ)≠47 by decide,if_false,hH,Value.natVal,wordValue_length]
    dsimp only [ρz,ρd,ρidx,ρlen] at hwvisible
    omega

/-- All operations of the fixed standard predictor AST have a uniform fifth
power bound in the actual input-word length. -/
theorem predictorProgram_work (ρ : Env) (x : List Bool) (hx : ρ 40=wordValue x) :
    predictorProgram.work ρ≤3000*(x.length+2)^5 := by
  have hq : QueryWork conditionalProgram (x.length+1) (2500*(x.length+2)^4) := by
    intro σ y hH hword hy
    exact conditionalProgram_work σ (x.length+1) y hH hword hy
  let ρH:=Function.update ρ 0 (.nat (x.length+1))
  have hb:=batchProgram_work conditionalProgram x.length (2500*(x.length+2)^4) hq ρH x rfl
    (by simpa [ρH] using hx) (by simp [ρH])
  have hp4 : 1≤(x.length+2)^4 := by
    have hh : 0<(x.length+2)^4 := by positivity
    omega
  have hlin : x.length+1≤(x.length+2)^4 := by
    have hh : x.length+2≤(x.length+2)^4 := le_self_pow₀ (by omega) (by decide)
    omega
  have hstep : 2500*(x.length+2)^4+20*(x.length+1)+104≤2700*(x.length+2)^4 := by omega
  have hm:=Nat.mul_le_mul_left x.length hstep
  have ht : x.length*(2700*(x.length+2)^4)≤2700*(x.length+2)^5 := by
    calc _ ≤(x.length+2)*(2700*(x.length+2)^4) := Nat.mul_le_mul_right _ (by omega)
         _ =_ := by ring
  have hp5 : 1≤(x.length+2)^5 := by
    have hh : 0<(x.length+2)^5 := by positivity
    omega
  simp only [predictorProgram,Expr.work,Expr.eval,hx,wordValue_length,Value.natVal]
  change 2+1+1+1+(batchProgram conditionalProgram).work ρH≤_
  omega

end Paper37.IntegerPredictorProgram
