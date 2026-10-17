import Paper37.AdaptiveQueryProgram
import Paper37.RefinedCoreWork
import Paper37.RefinedOutputWork
import Paper37.AdaptiveBatchWork
import Paper37.WordProgramWork
import Paper37.CachedCoreWork

namespace Paper37.AdaptiveQueryProgram
open Paper37.BoundedLoop Paper37.WordProgram Paper37.AdaptiveBatchProgram
open Paper37.AdaptiveIntegerOutput Paper37.CachedDP Paper37.RefinedCoreProgram
open Paper37.CachedCoreProgram (chooseValue powerValue observedValue natArray)
open Paper37.CachedRefinedDP
open Paper37.CacheBuilderProgram Paper37.CachedOutput Paper37.ContinuationDP
open Paper37.Envelope
set_option linter.unusedSimpArgs false
private abbrev v := Expr.var

lemma continuationBody_work (ρ : Env) (H : ℕ) (z : List Bool) (R : ℕ)
    (hH : ρ 0=.nat H) (h2 : ρ 2=chooseValue (makeObservedCache H z))
    (h3 : ρ 3=powerValue (makeObservedCache H z)) (hR : ρ 12=.nat R)
    (hs : ρ 58=.array [.nat (parseAge 0 z),.nat (parseGaps 0 z).length,
      observedValue (makeObservedCache H z)]) (hz : z.length+R≤H) :
    continuationBody.work ρ≤600*(H+1)^5 := by
  let c:=makeObservedCache H z
  let A:=parseAge 0 z
  let r:=(parseGaps 0 z).length
  let ρA:=Function.update ρ 1 (.nat A)
  let ρr:=Function.update ρA 11 (.nat r)
  let ρa:=Function.update ρr 4 (observedValue c)
  have hcore:=coreProgram_eval c A ρa (by simpa [ρa,ρr,ρA] using hH)
    (by simp [ρa,ρr,ρA]) (by simpa [ρa,ρr,ρA,c] using h2)
    (by simpa [ρa,ρr,ρA,c] using h3) (by simp [ρa])
  have hwcore:=coreProgram_work_quintic ρa H (by simpa [ρa,ρr,ρA] using hH)
  let table:=cachedRefinedRun H c A H
  let ρt:=Function.update ρa 5 (layerValue table)
  have hout : Paper37.RefinedOutputProgram.Inputs ρt c A table r R := by
    constructor
    · simpa [ρt,ρa,ρr,ρA] using hH
    · simp [ρt,ρa,ρr,ρA]
    · simpa [ρt,ρa,ρr,ρA,c] using h3
    · simp [ρt,ρa]
    · simp [ρt]
    · simp [ρt,ρa,ρr]
    · simpa [ρt,ρa,ρr,ρA] using hR
  have hwout:=Paper37.RefinedOutputProgram.outputProgram_work_quartic ρt H hout.horizon
    (by simp [Paper37.RefinedOutputProgram.totalFuture,Expr.eval,hout.age,hout.remaining,Value.natVal];
        have ha:=age_le_length z;dsimp [A];omega)
  have hp4 : 1≤(H+1)^5 := by
    have hh : 0<(H+1)^5 := by positivity
    omega
  have hpow : (H+1)^4≤(H+1)^5 := Nat.pow_le_pow_right (by omega) (by decide)
  simp only [continuationBody,Expr.work,Expr.eval,hs]
  simp only [Function.update_of_ne (by decide : (58:ℕ)≠1),
    Function.update_of_ne (by decide : (58:ℕ)≠11),Value.arrayVal,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,hs,Value.natVal]
  change 3+1+(3+1+(3+1+(coreProgram.work ρa+1+
    Paper37.RefinedOutputProgram.outputProgram.work (Function.update ρa 5 (coreProgram.eval ρa)))))≤_
  rw [hcore]
  change 3+1+(3+1+(3+1+(coreProgram.work ρa+1+
    Paper37.RefinedOutputProgram.outputProgram.work ρt)))≤_
  omega

/-- Actual work of the single complete continuation AST, including parsed
histograms and both coefficient caches. -/
theorem continuationProgram_work (ρ : Env) (H : ℕ) (z : List Bool) (R : ℕ)
    (hH : ρ 0=.nat H) (hword : ρ 40=wordValue z) (hR : ρ 12=.nat R)
    (hz : z.length+R≤H) :
    continuationProgram.work ρ≤1000*(H+1)^5 := by
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
  have hp4 : 1≤(H+1)^5 := by
    have hh : 0<(H+1)^5 := by positivity
    omega
  have hpow2 : (H+1)^2≤(H+1)^5 := Nat.pow_le_pow_right (by omega) (by decide)
  have hpow3 : (H+1)^3≤(H+1)^5 := Nat.pow_le_pow_right (by omega) (by decide)
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

lemma weightProgram_work (ρ : Env) : weightProgram.work ρ≤30 := by
  simp only [weightProgram,componentIndex,Expr.work]
  split_ifs <;> simp [Expr.work] <;> omega

lemma componentProgram_work (ρ : Env) : componentProgram.work ρ≤80 := by
  have hw:=weightProgram_work ρ
  have hb (σ:Env) : (Expr.array [
    .mul (.get (.var 63) (.lit 0)) (.get (.var 60) (.min componentIndex (.var 0))),
    .mul (.mul (.get (.var 63) (.lit 1)) (.add (.var 0) (.lit 1)))
      (.get (.var 61) (.min componentIndex (.var 0)))]).work σ=29 := by
    simp [Expr.work,componentIndex]
  rw [componentProgram,Expr.work,hb]
  omega

lemma mixBody_work (ρ : Env) : mixBody.work ρ≤140 := by
  have hc:=componentProgram_work (Function.update ρ 53 (ρ 64))
  have hp:=pairAddProgram_work (Function.update (Function.update ρ 53 (ρ 64)) 54
    (componentProgram.eval (Function.update ρ 53 (ρ 64))))
  rw [mixBody,Expr.work]
  simp only [Expr.work,Expr.eval]
  omega

theorem mixProgram_work (ρ : Env) : mixProgram.work ρ≤7+144*(ρ 0).natVal := by
  have hh:=Paper37.IntegerOutputProgram.fold_work_le ρ 62 64 (.var 0) (.array [.lit 0,.lit 1]) mixBody
    140 (by intro t ht a;exact mixBody_work _)
  simpa only [mixProgram,Expr.work,Expr.eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    Nat.reduceAdd,Nat.mul_comm] using hh

lemma visiblePrefixProgram_work (ρ : Env) (N L : ℕ) (z : List Bool)
    (hN:ρ 0=.nat N) (hLslot:ρ 48=.nat L) (hz:ρ 40=wordValue z)
    (hL:L≤N) (hzL:z.length≤L) : visiblePrefixProgram.work ρ≤2200*(N+1)^5 := by
  let ρR:=Function.update ρ 12 (.nat (L-z.length))
  have hc:=continuationProgram_eval ρR N z (L-z.length) (by simpa [ρR] using hN)
    (by simpa [ρR] using hz) (by simp [ρR]) (by omega)
  have hwc:=continuationProgram_work ρR N z (L-z.length) (by simpa [ρR] using hN)
    (by simpa [ρR] using hz) (by simp [ρR]) (by omega)
  let ρm:=Function.update ρR 60 (natArray (allNumerators N z (L-z.length)))
  let ρempty:=Function.update (Function.update ρm 40 (wordValue [])) 12 (.nat L)
  have hwe:=continuationProgram_work ρempty N [] L (by simpa [ρempty,ρm,ρR] using hN)
    (by simp [ρempty]) (by simp [ρempty]) (by simpa using hL)
  let normExpr:Expr:=Expr.bind 40 (.array []) (.bind 12 (.var 48) continuationProgram)
  have hwn:normExpr.work ρm≤1000*(N+1)^5+4 := by
    have h48:ρm 48=.nat L := by simpa [ρm,ρR] using hLslot
    simp only [normExpr,Expr.work,Expr.eval]
    simp only [Function.update_of_ne (by decide : (48:ℕ)≠40),h48]
    change 1+1+(1+1+continuationProgram.work ρempty)≤_
    omega
  have hwm:=mixProgram_work (Function.update ρm 61 (normExpr.eval ρm))
  have h0:(Function.update ρm 61 (normExpr.eval ρm)) 0=.nat N := by simpa [ρm,ρR] using hN
  rw [h0] at hwm
  simp only [Value.natVal] at hwm
  have hR:(Expr.sub (.var 48) (.length (.var 40))).eval ρ=.nat (L-z.length) := by
    simp [Expr.eval,hLslot,hz,Value.natVal]
  have hRw:(Expr.sub (.var 48) (.length (.var 40))).work ρ=4 := by simp [Expr.work]
  rw [visiblePrefixProgram,Expr.work,hR,hRw]
  change 4+1+(Expr.bind 60 continuationProgram (.bind 61 normExpr mixProgram)).work ρR≤_
  rw [Expr.work,hc]
  change 4+1+(continuationProgram.work ρR+1+(Expr.bind 61 normExpr mixProgram).work ρm)≤_
  rw [Expr.work]
  have hlin:N+1≤(N+1)^5 := le_self_pow₀ (by omega) (by decide)
  have hone:1≤(N+1)^5 := one_le_pow₀ (by omega)
  omega

/-- Actual work of the complete E.3 mixed-prefix AST. -/
theorem prefixProgram_work (ρ : Env) (N : ℕ) (y : List Bool)
    (hN:ρ 0=.nat N) (hword:ρ 40=wordValue y) (hy:y.length≤N) :
    prefixProgram.work ρ≤2400*(N+1)^5 := by
  let ρlen:=Function.update ρ 49 (.nat y.length)
  have hidx:=firstIndexProgram_eval ρlen y (by simpa [ρlen] using hword)
  have hwidx:=firstIndexProgram_work ρlen y (by simpa [ρlen] using hword)
  let ρidx:=Function.update ρlen 47 (.nat (firstIndex y))
  have hp5:1≤(N+1)^5 := one_le_pow₀ (by omega)
  have hlin:y.length+1≤(N+1)^5 := by
    have hh:N+1≤(N+1)^5 := le_self_pow₀ (by omega) (by decide)
    omega
  cases hs:Paper37.Prediction.firstSuffix y with
  | none =>
    have hi:=firstIndex_none y hs
    simp only [prefixProgram,Expr.work,Expr.eval,hword,wordValue_length]
    dsimp only [ρlen] at hidx hwidx
    rw [hidx]
    simp only [Function.update_apply,if_true,show (49:ℕ)≠47 by decide,if_false,
      Value.natVal,hi,lt_self_iff_false]
    simp only [Expr.work,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    omega
  | some z =>
    obtain ⟨hlen,hdrop⟩:=firstIndex_some y z hs
    have hi:firstIndex y<y.length := by omega
    let ρd:=Function.update ρidx 44 (.nat (firstIndex y+1))
    have hd:=dropProgram_eval ρd y (firstIndex y+1)
      (by simpa [ρd,ρidx,ρlen] using hword) (by simp [ρd])
    rw [hdrop] at hd
    have hwd:=dropProgram_work ρd y (firstIndex y+1)
      (by simpa [ρd,ρidx,ρlen] using hword) (by simp [ρd])
    let ρz:=Function.update ρd 40 (wordValue z)
    have hwv:=visiblePrefixProgram_work (Function.update ρz 48 (.nat (N-y.length+z.length))) N
      (N-y.length+z.length) z (by simpa [ρz,ρd,ρidx,ρlen] using hN) (by simp)
      (by simp [ρz]) (by omega) (by omega)
    simp only [prefixProgram,Expr.work,Expr.eval,hword,wordValue_length]
    dsimp only [ρlen] at hidx hwidx
    rw [hidx]
    simp only [Function.update_apply,if_true,show (49:ℕ)≠47 by decide,if_false,Value.natVal,hi,if_true]
    dsimp only [ρd,ρidx,ρlen] at hd hwd
    rw [hd]
    simp only [Function.update_apply,if_true,
      show (0:ℕ)≠40 by decide,show (0:ℕ)≠44 by decide,
      show (0:ℕ)≠47 by decide,show (0:ℕ)≠49 by decide,
      show (49:ℕ)≠40 by decide,show (49:ℕ)≠44 by decide,
      show (49:ℕ)≠47 by decide,if_false,hN,Value.natVal,wordValue_length]
    dsimp only [ρz,ρd,ρidx,ρlen] at hwv
    omega

theorem conditionalProgram_work (ρ : Env) (N : ℕ) (y : List Bool)
    (hN:ρ 0=.nat N) (hword:ρ 40=wordValue y) (hy:y.length<N) :
    conditionalProgram.work ρ≤5100*(N+1)^5 := by
  let ρbit:=Function.update ρ 46 (bitValue true)
  have happ:=appendProgram_eval ρbit y true (by simpa [ρbit] using hword) (by simp [ρbit])
  have hwa:=appendProgram_work ρbit y (by simpa [ρbit] using hword)
  let ρchild:=Function.update ρbit 40 (wordValue (y++[true]))
  have hwc:=prefixProgram_work ρchild N (y++[true]) (by simpa [ρchild,ρbit] using hN)
    (by simp [ρchild]) (by simp;omega)
  have hc:=prefixProgram_eval ρchild N (y++[true]) (by simpa [ρchild,ρbit] using hN)
    (by simp [ρchild]) (by simp;omega)
  let childExpr:Expr:=.bind 46 (.lit 1) (.bind 40 appendProgram prefixProgram)
  have he:childExpr.eval ρ=pairValue (prefixPair N (y++[true])) := by
    simp only [childExpr,Expr.eval]
    change prefixProgram.eval (Function.update ρbit 40 (appendProgram.eval ρbit))=_
    rw [happ]
    exact hc
  have hwchild:childExpr.work ρ≤2400*(N+1)^5+20*(y.length+1)+4 := by
    simp only [childExpr,Expr.work,Expr.eval]
    change 1+1+(appendProgram.work ρbit+1+prefixProgram.work (Function.update ρbit 40 (appendProgram.eval ρbit)))≤_
    rw [happ]
    change 1+1+(appendProgram.work ρbit+1+prefixProgram.work ρchild)≤_
    omega
  let ρc:=Function.update ρ 71 (pairValue (prefixPair N (y++[true])))
  have hwp:=prefixProgram_work ρc N y (by simpa [ρc] using hN) (by simpa [ρc] using hword) hy.le
  have harray (σ:Env):conditionalArray.work σ≤20 := by simp [conditionalArray,Expr.work]
  change (Expr.bind 71 childExpr (.bind 72 prefixProgram conditionalArray)).work ρ≤_
  rw [Expr.work,he]
  change childExpr.work ρ+1+(Expr.bind 72 prefixProgram conditionalArray).work ρc≤_
  have hbind:(Expr.bind 72 prefixProgram conditionalArray).work ρc=
      prefixProgram.work ρc+1+conditionalArray.work (Function.update ρc 72 (prefixProgram.eval ρc)) := by
    rw [Expr.work]
  rw [hbind]
  have hlin:y.length+1≤(N+1)^5 := by
    have hh:N+1≤(N+1)^5 := le_self_pow₀ (by omega) (by decide)
    omega
  have hone:1≤(N+1)^5 := one_le_pow₀ (by omega)
  have ha:=harray (Function.update ρc 72 (prefixProgram.eval ρc))
  change childExpr.work ρ+1+(prefixProgram.work ρc+1+conditionalArray.work
    (Function.update ρc 72 (prefixProgram.eval ρc)))≤_
  omega

/-- A sixth-degree bound on the actual work of the one fixed adaptive
predictor AST, including all requested suffixes and integer mixture arithmetic. -/
theorem predictorProgram_work (ρ : Env) (x : List Bool) (hx:ρ 40=wordValue x) :
    predictorProgram.work ρ≤6000*(x.length+2)^6 := by
  have hq:QueryWork conditionalProgram (x.length+1) (5100*(x.length+2)^5) := by
    intro σ y hN hw hy
    exact conditionalProgram_work σ (x.length+1) y hN hw hy
  let ρH:=Function.update ρ 0 (.nat (x.length+1))
  have hb:=batchProgram_work conditionalProgram x.length (5100*(x.length+2)^5) hq ρH x rfl
    (by simpa [ρH] using hx) (by simp [ρH])
  have hp5:1≤(x.length+2)^5 := one_le_pow₀ (by omega)
  have hlin:x.length+1≤(x.length+2)^5 := by
    have hh:x.length+2≤(x.length+2)^5 := le_self_pow₀ (by omega) (by decide)
    omega
  have hstep:5100*(x.length+2)^5+20*(x.length+1)+104≤5300*(x.length+2)^5 := by omega
  have hm:=Nat.mul_le_mul_left x.length hstep
  have ht:x.length*(5300*(x.length+2)^5)≤5300*(x.length+2)^6 := by
    calc _≤(x.length+2)*(5300*(x.length+2)^5) := Nat.mul_le_mul_right _ (by omega)
         _=_ := by ring
  have hp6:1≤(x.length+2)^6 := one_le_pow₀ (by omega)
  simp only [predictorProgram,Expr.work,Expr.eval,hx,wordValue_length,Value.natVal]
  change 2+1+1+1+(batchProgram conditionalProgram).work ρH≤_
  omega

end Paper37.AdaptiveQueryProgram
