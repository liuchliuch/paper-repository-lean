import Paper37.IntegerPredictorProgram
import Paper37.IntegerOutputPeak
import Paper37.CacheBuilderProgramPeak
import Paper37.CachedCorePolynomial
import Paper37.WordProgramPeak

/-! Actual dynamic intermediate-size bounds for the fixed continuation and
conditional query ASTs, composed from their real parser, cache, core and output
executions. All source inputs remain explicit and unused slots are arbitrary. -/
namespace Paper37.IntegerQueryProgramPeak
open Paper37.BoundedLoop Paper37.WordProgram Paper37.IntegerPredictorProgram
open Paper37.PredictorBatchProgram Paper37.IntegerPredictor
open Paper37.CachedDP Paper37.CachedCoreProgram Paper37.CacheBuilderProgram
open Paper37.CachedOutput Paper37.ContinuationDP Paper37.Envelope
open Paper37.IntegerOutputProgram Paper37.IntegerOutputPeak
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
private abbrev v := BoundedLoop.Expr.var
private abbrev n := BoundedLoop.Expr.lit

def queryPeakBound (H : ℕ) : ℕ := 1000000000000*(H+2)^12

lemma poly2_le_query (H C k : ℕ) (hC : C≤1000000000000) (hk : k≤12) :
    C*(H+2)^k≤queryPeakBound H := by
  unfold queryPeakBound
  exact Nat.mul_le_mul hC (Nat.pow_le_pow_right (by omega) hk)
lemma poly1_le_query (H C k : ℕ) (hC : C≤1000000000000) (hk : k≤12) :
    C*(H+1)^k≤queryPeakBound H :=
  (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega) k)).trans (poly2_le_query H C k hC hk)
lemma nat_representation (a H : ℕ) (ha : a≤H) :
    (Value.nat a).representationSize≤H+1 := by
  have hh:=(Paper37.DP.binarySize_le_self a).trans ha
  simpa only [Value.representationSize] using Nat.add_le_add_right hh 1
lemma nat_rep_query (a H : ℕ) (ha : a≤H+1) : (Value.nat a).representationSize≤queryPeakBound H :=
  (nat_representation a (H+1) ha).trans (by
    have hh:=poly2_le_query H 1 1 (by norm_num) (by norm_num)
    simpa using hh)
lemma lit_peak_query (ρ : Env) (H a : ℕ) (ha : a≤H+1) :
    (BoundedLoop.Expr.lit a).peak ρ≤queryPeakBound H :=
  lit_peak_of_rep ρ a _ (nat_rep_query a H ha)

lemma pairValue_evaluatePair_size (H : ℕ) (z : List Bool) (R : ℕ) (hH : 0<H)
    (hz : z.length+R≤H) :
    (pairValue (evaluatePair H z R)).representationSize≤200000000*(H+1)^4 := by
  let c:=makeObservedCache H z
  let table:=cachedRun H c (parseAge 0 z) H
  let σ:=outputEnv c (parseAge 0 z) table (parseGaps 0 z).length R
  have he:=outputProgram_evaluatePair H z R hz
  change outputProgram.eval σ=pairValue (evaluatePair H z R) at he
  have hp:=outputProgram_evaluatePair_peak H z R hH hz
  change outputProgram.peak σ≤_ at hp
  rw [← he]
  exact (representationSize_le_peak outputProgram σ).trans hp

lemma parsed_frame_size (H : ℕ) (z : List Bool) (hz : z.length≤H) :
    (Value.array [.nat (parseAge 0 z),.nat (parseGaps 0 z).length,
      observedValue (makeObservedCache H z)]).representationSize≤10*(H+2)^2 := by
  have ha:=nat_representation (parseAge 0 z) H ((age_le_length z).trans hz)
  have hr:=nat_representation (parseGaps 0 z).length H (by have hh:=Paper37.IntegerOutput.count_add_age_le z;omega)
  have hc:=source_observed_representation H z hz
  simp only [Value.representationSize,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at *
  nlinarith

lemma get_literal_peak (ρ : Env) (x k B : ℕ) (hx : (ρ x).representationSize≤B) :
    (BoundedLoop.Expr.get (.var x) (.lit k)).peak ρ≤B+(k.size+1)+1 := by
  exact get_peak_le _ _ ρ _ _ (var_peak_of_rep ρ x B hx)
    (by simp [BoundedLoop.Expr.peak,BoundedLoop.Expr.eval,Value.representationSize])

lemma frame_get_peak (ρ : Env) (H k : ℕ) (hk : k≤2)
    (hs : (ρ 58).representationSize≤10*(H+2)^2) :
    (BoundedLoop.Expr.get (.var 58) (.lit k)).peak ρ≤queryPeakBound H := by
  have hh:=get_literal_peak ρ 58 k _ hs
  have hks:=(Paper37.DP.binarySize_le_self k).trans hk
  apply hh.trans
  have hp:=poly2_le_query H 20 2 (by norm_num) (by norm_num)
  have ht : 4≤(H+2)^2 := by
    simpa using Nat.pow_le_pow_left (show 2≤H+2 by omega) 2
  omega

lemma continuationBody_peak (ρ : Env) (H : ℕ) (z : List Bool) (R : ℕ) (hpos : 0<H)
    (hH : ρ 0=.nat H) (h2 : ρ 2=chooseValue (makeObservedCache H z))
    (h3 : ρ 3=powerValue (makeObservedCache H z)) (hR : ρ 12=.nat R)
    (hs : ρ 58=.array [.nat (parseAge 0 z),.nat (parseGaps 0 z).length,
      observedValue (makeObservedCache H z)]) (hz : z.length+R≤H) :
    continuationBody.peak ρ≤queryPeakBound H := by
  let c:=makeObservedCache H z
  let A:=parseAge 0 z
  let r:=(parseGaps 0 z).length
  let ρA:=Function.update ρ 1 (.nat A)
  let ρr:=Function.update ρA 11 (.nat r)
  let ρa:=Function.update ρr 4 (observedValue c)
  have hcore:=coreProgram_eval c A ρa (by simpa [ρa,ρr,ρA] using hH)
    (by simp [ρa,ρr,ρA]) (by simpa [ρa,ρr,ρA,c] using h2)
    (by simpa [ρa,ρr,ρA,c] using h3) (by simp [ρa])
  have hpcore:=coreProgram_peak_polynomial H z A ρa hpos (by omega)
    (by dsimp [A];exact (age_le_length z).trans (by omega))
    (by simpa [ρa,ρr,ρA] using hH) (by simp [ρa,ρr,ρA])
    (by simpa [ρa,ρr,ρA,c] using h2) (by simpa [ρa,ρr,ρA,c] using h3) (by simp [ρa,c])
  let table:=cachedRun H c A H
  let ρt:=Function.update ρa 5 (layerValue table)
  have hout : Inputs ρt c A table r R := by
    constructor
    · simpa [ρt,ρa,ρr,ρA] using hH
    · simp [ρt,ρa,ρr,ρA]
    · simpa [ρt,ρa,ρr,ρA,c] using h3
    · simp [ρt,ρa]
    · simp [ρt]
    · simp [ρt,ρa,ρr]
    · simpa [ρt,ρa,ρr,ρA] using hR
  have hpout:=outputProgram_source_peak hpos z (by omega) hout
    (by have hh:=age_le_length z;dsimp [A];omega) (by have hh:=Paper37.IntegerOutput.count_add_age_le z;dsimp [r];omega)
  have hframe : (ρ 58).representationSize≤10*(H+2)^2 := by
    rw [hs]
    exact parsed_frame_size H z (by omega)
  have hgA : (Expr.get (.var 58) (.lit 0)).eval ρ=.nat A := by
    simp [Expr.eval,hs,A,Value.arrayVal,Value.natVal]
  have hgr : (Expr.get (.var 58) (.lit 1)).eval ρA=.nat r := by
    simp [Expr.eval,ρA,hs,r,Value.arrayVal,Value.natVal]
  have hga : (Expr.get (.var 58) (.lit 2)).eval ρr=observedValue c := by
    simp [Expr.eval,ρr,ρA,hs,c,Value.arrayVal,Value.natVal]
  rw [continuationBody]
  apply bind_peak_bound
  · exact frame_get_peak ρ H 0 (by omega) hframe
  · rw [hgA]
    change (Expr.bind 11 (.get (.var 58) (.lit 1))
      (.bind 4 (.get (.var 58) (.lit 2)) (.bind 5 coreProgram outputProgram))).peak ρA≤_
    apply bind_peak_bound
    · exact frame_get_peak ρA H 1 (by omega) (by simpa [ρA] using hframe)
    · rw [hgr]
      change (Expr.bind 4 (.get (.var 58) (.lit 2)) (.bind 5 coreProgram outputProgram)).peak ρr≤_
      apply bind_peak_bound
      · exact frame_get_peak ρr H 2 (by omega) (by simpa [ρr,ρA] using hframe)
      · rw [hga]
        change (Expr.bind 5 coreProgram outputProgram).peak ρa≤_
        apply bind_peak_bound
        · exact hpcore.trans (poly1_le_query H 101000000 6 (by norm_num) (by norm_num))
        · rw [hcore]
          exact hpout.trans (poly1_le_query H 200000000 4 (by norm_num) (by norm_num))

/-- Complete continuation query, including its actual cache construction,
parser, materialized recurrence and integer pair output. -/
theorem continuationProgram_peak (ρ : Env) (H : ℕ) (z : List Bool) (R : ℕ) (hpos : 0<H)
    (hH : ρ 0=.nat H) (hword : ρ 40=wordValue z) (hR : ρ 12=.nat R)
    (hz : z.length+R≤H) : continuationProgram.peak ρ≤queryPeakBound H := by
  have hchoose:=Paper37.IntegerPredictorProgram.chooseProgram_source ρ H z hH
  have hpchoose:=Paper37.CacheBuilderProgramPeak.chooseProgram_peak ρ H hH
  let ρc:=Function.update ρ 2 (chooseValue (makeObservedCache H z))
  have hpower:=Paper37.IntegerPredictorProgram.powerProgram_source ρc H z (by simpa [ρc] using hH)
  have hppower:=Paper37.CacheBuilderProgramPeak.powerProgram_peak ρc H (by simpa [ρc] using hH)
  let ρp:=Function.update ρc 3 (powerValue (makeObservedCache H z))
  have hparse:=parserProgram_eval_source ρp H z (by simpa [ρp,ρc] using hH)
    (by simpa [ρp,ρc] using hword)
  have hpparse:=parserProgram_peak ρp H z (by simpa [ρp,ρc] using hH)
    (by simpa [ρp,ρc] using hword) (by omega)
  let ρs:=Function.update ρp 58 (.array [.nat (parseAge 0 z),.nat (parseGaps 0 z).length,
      observedValue (makeObservedCache H z)])
  have hpbody:=continuationBody_peak ρs H z R hpos (by simpa [ρs,ρp,ρc] using hH)
    (by simp [ρs,ρp,ρc]) (by simp [ρs,ρp]) (by simpa [ρs,ρp,ρc] using hR) (by simp [ρs]) hz
  rw [continuationProgram]
  apply bind_peak_bound
  · exact hpchoose.trans (poly1_le_query H 200 3 (by norm_num) (by norm_num))
  · rw [hchoose]
    change (Expr.bind 3 powerProgram (.bind 58 parserProgram continuationBody)).peak ρc≤_
    apply bind_peak_bound
    · exact hppower.trans (poly1_le_query H 1000 3 (by norm_num) (by norm_num))
    · rw [hpower]
      change (Expr.bind 58 parserProgram continuationBody).peak ρp≤_
      apply bind_peak_bound
      · exact hpparse.trans (poly2_le_query H 1000000 4 (by norm_num) (by norm_num))
      · rw [hparse]
        exact hpbody


private def remainingExpr : Expr := .sub (.var 48) (.add (.length (.var 40)) (.lit 1))
private lemma remainingExpr_flat : Flat remainingExpr := by
  unfold remainingExpr
  repeat' first | apply Flat.binary .sub | apply Flat.binary .add | apply Flat.length | apply Flat.var | apply Flat.lit

lemma remainingExpr_peak (ρ : Env) (H L : ℕ) (z : List Bool)
    (hLslot : ρ 48=.nat L) (hword : ρ 40=wordValue z) (hL : L≤H) (hz : z.length≤H) :
    remainingExpr.peak ρ≤queryPeakBound H := by
  have hLr:=nat_representation L H hL
  have hwr:=wordValue_size z
  have hh:=flat_peak_le remainingExpr_flat ρ (4*(H+2)) (by
    simp only [remainingExpr,Expr.varsBound,hLslot,hword]
    constructor
    · nlinarith
    · exact ⟨by nlinarith,trivial⟩)
  apply hh.trans
  have hp:=poly2_le_query H 1000 1 (by norm_num) (by norm_num)
  norm_num [remainingExpr,Expr.flatBudget]
  nlinarith

lemma childProgram_peak (ρ : Env) (H L : ℕ) (z : List Bool) (b : Bool) (hpos : 0<H)
    (hH : ρ 0=.nat H) (hLslot : ρ 48=.nat L) (hword : ρ 40=wordValue z)
    (hbit : ρ 46=bitValue b) (hL : L≤H) (hz : z.length<L) :
    childProgram.peak ρ≤queryPeakBound H := by
  let R:=L-(z.length+1)
  let ρR:=Function.update ρ 12 (.nat R)
  have happend:=appendProgram_eval ρR z b (by simpa [ρR] using hword) (by simpa [ρR] using hbit)
  have hpappend:=appendProgram_peak ρR H z b (by simpa [ρR] using hword)
    (by simpa [ρR] using hbit) (by omega)
  let ρb:=Function.update ρR 40 (wordValue (z++[b]))
  have hpcont:=continuationProgram_peak ρb H (z++[b]) R hpos
    (by simpa [ρb,ρR] using hH) (by simp [ρb]) (by simp [ρb,ρR]) (by simp;omega)
  have hrem : remainingExpr.eval ρ=.nat R := by
    simp [remainingExpr,Expr.eval,hLslot,hword,wordValue_length,Value.natVal,R]
  rw [childProgram]
  apply bind_peak_bound
  · exact remainingExpr_peak ρ H L z hLslot hword hL (by omega)
  · change (Expr.bind 40 appendProgram continuationProgram).peak (Function.update ρ 12 (remainingExpr.eval ρ))≤_
    rw [hrem]
    change (Expr.bind 40 appendProgram continuationProgram).peak ρR≤_
    apply bind_peak_bound
    · exact hpappend.trans (poly2_le_query H 100000 3 (by norm_num) (by norm_num))
    · rw [happend]
      exact hpcont

private lemma visibleArray_flat : Flat visibleArray := by
  unfold visibleArray
  apply Flat.array
  intro e he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl
  · repeat' first | apply Flat.get | apply Flat.var | apply Flat.lit
  · repeat' first | apply Flat.binary .add | apply Flat.get | apply Flat.var | apply Flat.lit

lemma visibleArray_peak_le (ρ : Env) (B : ℕ)
    (hp : (ρ 55).representationSize≤B) (hq : (ρ 56).representationSize≤B) :
    visibleArray.peak ρ≤100*(B+1) := by
  have hg55:=get_literal_peak ρ 55 0 B hp
  have hg56:=get_literal_peak ρ 56 0 B hq
  simp only [Nat.size_zero] at hg55 hg56
  have hadd:=binary_peak_le .add (.get (.var 55) (.lit 0)) (.get (.var 56) (.lit 0))
    ρ _ _ hg55 hg56
  have harray:=array_peak_le [.get (.var 56) (.lit 0),
      .add (.get (.var 55) (.lit 0)) (.get (.var 56) (.lit 0))] ρ (fun _=>20*(B+1)) (by
    intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl
    · change (Expr.get (.var 56) (.lit 0)).peak ρ≤20*(B+1)
      exact hg56.trans (by omega)
    · change (Expr.add (.get (.var 55) (.lit 0)) (.get (.var 56) (.lit 0))).peak ρ≤20*(B+1)
      exact hadd.trans (by omega))
  exact harray.trans (by simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil];omega)

lemma visibleArray_peak (ρ : Env) (H : ℕ) (p q : ℕ×ℕ)
    (hp : ρ 55=pairValue p) (hq : ρ 56=pairValue q)
    (hps : (pairValue p).representationSize≤200000000*(H+1)^4)
    (hqs : (pairValue q).representationSize≤200000000*(H+1)^4) :
    visibleArray.peak ρ≤queryPeakBound H := by
  have hh:=visibleArray_peak_le ρ (200000000*(H+1)^4)
    (by rw [hp];exact hps) (by rw [hq];exact hqs)
  apply hh.trans
  have hpoly:=poly1_le_query H 30000000000 4 (by norm_num) (by norm_num)
  have ht : 1≤(H+1)^4 := by
    have hh : 0<(H+1)^4 := by positivity
    omega
  nlinarith

lemma visibleProgram_peak (ρ : Env) (H L : ℕ) (z : List Bool) (hpos : 0<H)
    (hH : ρ 0=.nat H) (hLslot : ρ 48=.nat L) (hword : ρ 40=wordValue z)
    (hL : L≤H) (hz : z.length<L) :
    visibleProgram.peak ρ≤queryPeakBound H := by
  let p:=evaluatePair H (z++[false]) (L-(z.length+1))
  let q:=evaluatePair H (z++[true]) (L-(z.length+1))
  let ρ₀:=Function.update ρ 46 (.nat 0)
  have hf:=childProgram_eval ρ₀ H L z false (by simpa [ρ₀] using hH)
    (by simpa [ρ₀] using hLslot) (by simpa [ρ₀] using hword) (by rfl) hL hz
  have hpf:=childProgram_peak ρ₀ H L z false hpos (by simpa [ρ₀] using hH)
    (by simpa [ρ₀] using hLslot) (by simpa [ρ₀] using hword) (by rfl) hL hz
  let ρp:=Function.update ρ₀ 55 (pairValue p)
  let ρ₁:=Function.update ρp 46 (.nat 1)
  have ht:=childProgram_eval ρ₁ H L z true (by simpa [ρ₁,ρp,ρ₀] using hH)
    (by simpa [ρ₁,ρp,ρ₀] using hLslot) (by simpa [ρ₁,ρp,ρ₀] using hword) (by rfl) hL hz
  have hpt:=childProgram_peak ρ₁ H L z true hpos (by simpa [ρ₁,ρp,ρ₀] using hH)
    (by simpa [ρ₁,ρp,ρ₀] using hLslot) (by simpa [ρ₁,ρp,ρ₀] using hword) (by rfl) hL hz
  let ρq:=Function.update ρ₁ 56 (pairValue q)
  have hpa:=visibleArray_peak ρq H p q (by simp [ρq,ρ₁,ρp]) (by simp [ρq])
    (pairValue_evaluatePair_size H _ _ hpos (by simp;omega))
    (pairValue_evaluatePair_size H _ _ hpos (by simp;omega))
  rw [visibleProgram]
  apply bind_peak_bound
  · exact lit_peak_query ρ H 0 (by omega)
  · rw [show (Expr.lit 0).eval ρ=.nat 0 by simp [Expr.eval]]
    change (Expr.bind 55 childProgram (.bind 46 (.lit 1) (.bind 56 childProgram visibleArray))).peak ρ₀≤_
    apply bind_peak_bound
    · exact hpf
    · rw [hf]
      change (Expr.bind 46 (.lit 1) (.bind 56 childProgram visibleArray)).peak ρp≤_
      apply bind_peak_bound
      · exact lit_peak_query ρp H 1 (by omega)
      · rw [show (Expr.lit 1).eval ρp=.nat 1 by simp [Expr.eval]]
        change (Expr.bind 56 childProgram visibleArray).peak ρ₁≤_
        apply bind_peak_bound
        · exact hpt
        · rw [ht]
          exact hpa


lemma if_true_peak (ρ : Env) (a b t e : Expr) (P : ℕ)
    (hc : (a.eval ρ).natVal<(b.eval ρ).natVal)
    (ha : a.peak ρ≤P) (hb : b.peak ρ≤P) (ht : t.peak ρ≤P) :
    (Expr.ifLT a b t e).peak ρ≤P := by
  have hr:=representationSize_le_peak t ρ
  rw [Expr.peak,Expr.eval]
  simp only [if_pos hc]
  exact max_le (hr.trans ht) (max_le ha (max_le hb ht))
lemma if_false_peak (ρ : Env) (a b t e : Expr) (P : ℕ)
    (hc : ¬(a.eval ρ).natVal<(b.eval ρ).natVal)
    (ha : a.peak ρ≤P) (hb : b.peak ρ≤P) (he : e.peak ρ≤P) :
    (Expr.ifLT a b t e).peak ρ≤P := by
  have hr:=representationSize_le_peak e ρ
  rw [Expr.peak,Expr.eval]
  simp only [if_neg hc]
  exact max_le (hr.trans he) (max_le ha (max_le hb he))

private def effectiveExpr : Expr := .add (.sub (.var 0) (.var 49)) (.length (.var 40))
private def noRenewalExpr : Expr := .array [.lit 1,.add (.sub (.var 0) (.var 49)) (.lit 1)]
private def visibleBranch : Expr :=
  .bind 44 (.add (.var 47) (.lit 1)) (.bind 40 dropProgram (.bind 48 effectiveExpr visibleProgram))
private lemma effectiveExpr_flat : Flat effectiveExpr := by
  unfold effectiveExpr
  repeat' first | apply Flat.binary .add | apply Flat.binary .sub | apply Flat.length | apply Flat.var
private lemma noRenewalExpr_flat : Flat noRenewalExpr := by
  unfold noRenewalExpr
  apply Flat.array
  intro e he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl
  · exact Flat.lit _
  · repeat' first | apply Flat.binary .add | apply Flat.binary .sub | apply Flat.var | apply Flat.lit

lemma effectiveExpr_peak (ρ : Env) (H m : ℕ) (z : List Bool)
    (hH : ρ 0=.nat H) (hm : ρ 49=.nat m) (hword : ρ 40=wordValue z)
    (hmH : m≤H) (hz : z.length≤H) : effectiveExpr.peak ρ≤queryPeakBound H := by
  have hHr:=nat_representation H H le_rfl
  have hmr:=nat_representation m H hmH
  have hwr:=wordValue_size z
  have hh:=flat_peak_le effectiveExpr_flat ρ (4*(H+2)) (by
    simp only [effectiveExpr,Expr.varsBound,hH,hm,hword]
    exact ⟨⟨by nlinarith,by nlinarith⟩,by nlinarith⟩)
  apply hh.trans
  have hp:=poly2_le_query H 1000 1 (by norm_num) (by norm_num)
  norm_num [effectiveExpr,Expr.flatBudget]
  nlinarith

lemma noRenewalExpr_peak (ρ : Env) (H m : ℕ)
    (hH : ρ 0=.nat H) (hm : ρ 49=.nat m) (hmH : m≤H) :
    noRenewalExpr.peak ρ≤queryPeakBound H := by
  have hHr:=nat_representation H H le_rfl
  have hmr:=nat_representation m H hmH
  have hh:=flat_peak_le noRenewalExpr_flat ρ (H+1) (by
    simp only [noRenewalExpr,Expr.varsBound,hH,hm]
    intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl
    · simp [Expr.varsBound]
    · simpa only [Expr.varsBound,hH,hm] using And.intro (And.intro hHr hmr) True.intro)
  apply hh.trans
  have hp:=poly2_le_query H 1000 1 (by norm_num) (by norm_num)
  norm_num [noRenewalExpr,Expr.flatBudget]
  nlinarith

lemma visibleBranch_peak (ρ : Env) (H : ℕ) (y z : List Bool) (hpos : 0<H)
    (hH : ρ 0=.nat H) (hword : ρ 40=wordValue y)
    (hlen : ρ 49=.nat y.length) (hidx : ρ 47=.nat (firstIndex y))
    (hs : Paper37.Prediction.firstSuffix y=some z) (hy : y.length<H) :
    visibleBranch.peak ρ≤queryPeakBound H := by
  obtain ⟨hsize,hdrop⟩:=firstIndex_some y z hs
  have hi : firstIndex y<y.length := by omega
  let ρd:=Function.update ρ 44 (.nat (firstIndex y+1))
  have hd:=dropProgram_eval ρd y (firstIndex y+1) (by simpa [ρd] using hword) (by simp [ρd])
  rw [hdrop] at hd
  have hpd:=dropProgram_peak ρd H y (firstIndex y+1) (by simpa [ρd] using hword)
    (by simp [ρd]) (by omega) (by omega)
  let ρz:=Function.update ρd 40 (wordValue z)
  let L:=H-y.length+z.length
  have hL : L≤H := by dsimp [L];omega
  have hz : z.length<L := by dsimp [L];omega
  have heff : effectiveExpr.eval ρz=.nat L := by
    simp [effectiveExpr,Expr.eval,ρz,ρd,hH,hlen,wordValue_length,Value.natVal,L]
  have hpe:=effectiveExpr_peak ρz H y.length z (by simpa [ρz,ρd] using hH)
    (by simpa [ρz,ρd] using hlen) (by simp [ρz]) (by omega) (by omega)
  have hpv:=visibleProgram_peak (Function.update ρz 48 (.nat L)) H L z hpos
    (by simpa [ρz,ρd] using hH) (by simp) (by simp [ρz]) hL hz
  have hind : (Expr.add (.var 47) (.lit 1)).eval ρ=.nat (firstIndex y+1) := by
    simp [Expr.eval,hidx,Value.natVal]
  have hpi : (Expr.add (.var 47) (.lit 1)).peak ρ≤queryPeakBound H := by
    have hvar:=var_peak_of_rep ρ 47 (H+1) (by rw [hidx];exact nat_representation _ H (by omega))
    have hlit : (Expr.lit 1).peak ρ≤2 := by simp [Expr.peak,Expr.eval,Value.representationSize]
    have hh:=binary_peak_le .add (.var 47) (.lit 1) ρ _ _ hvar hlit
    have hpoly:=poly2_le_query H 1000 1 (by norm_num) (by norm_num)
    exact hh.trans (by nlinarith)
  rw [visibleBranch]
  apply bind_peak_bound
  · exact hpi
  · rw [hind]
    change (Expr.bind 40 dropProgram (.bind 48 effectiveExpr visibleProgram)).peak ρd≤_
    apply bind_peak_bound
    · exact hpd.trans (poly2_le_query H 100000 3 (by norm_num) (by norm_num))
    · rw [hd]
      change (Expr.bind 48 effectiveExpr visibleProgram).peak ρz≤_
      apply bind_peak_bound
      · exact hpe
      · rw [heff]
        exact hpv

/-- Closed source-level peak theorem for the actual first-renewal conditional
query. Only its actual horizon and encoded input word are assumed. -/
theorem conditionalProgram_peak (ρ : Env) (H : ℕ) (y : List Bool)
    (hH : ρ 0=.nat H) (hword : ρ 40=wordValue y) (hy : y.length<H) :
    conditionalProgram.peak ρ≤queryPeakBound H := by
  have hpos : 0<H := by omega
  let ρlen:=Function.update ρ 49 (.nat y.length)
  have hidx:=firstIndexProgram_eval ρlen y (by simpa [ρlen] using hword)
  have hpidx:=firstIndexProgram_peak ρlen H y (by simpa [ρlen] using hword) (by omega)
  let ρidx:=Function.update ρlen 47 (.nat (firstIndex y))
  have hlenEval : (Expr.length (.var 40)).eval ρ=.nat y.length := by
    simp [Expr.eval,hword,wordValue_length]
  have hpLen : (Expr.length (.var 40)).peak ρ≤queryPeakBound H := by
    have hw:=wordValue_size y
    have hvar:=var_peak_of_rep ρ 40 (2*y.length+2) (by rw [hword];exact hw)
    have hh:=length_peak_le (.var 40) ρ _ hvar
    have hpoly:=poly2_le_query H 1000 1 (by norm_num) (by norm_num)
    exact hh.trans (by nlinarith)
  have h47 : (Expr.var 47).peak ρidx≤queryPeakBound H := by
    apply var_peak_of_rep
    simp only [ρidx,Function.update_self]
    exact nat_rep_query _ H ((firstIndex_le_length y).trans (by omega))
  have h49 : (Expr.var 49).peak ρidx≤queryPeakBound H := by
    apply var_peak_of_rep
    simp only [ρidx,ρlen,Function.update_of_ne (by decide : (49:ℕ)≠47),Function.update_self]
    exact nat_rep_query _ H (by omega)
  rw [conditionalProgram]
  apply bind_peak_bound
  · exact hpLen
  · rw [hlenEval]
    change (Expr.bind 47 firstIndexProgram (.ifLT (.var 47) (.var 49) visibleBranch noRenewalExpr)).peak ρlen≤_
    apply bind_peak_bound
    · exact hpidx.trans (poly2_le_query H 100000 3 (by norm_num) (by norm_num))
    · rw [hidx]
      change (Expr.ifLT (.var 47) (.var 49) visibleBranch noRenewalExpr).peak ρidx≤_
      cases hs : Paper37.Prediction.firstSuffix y with
      | none =>
        have hi:=firstIndex_none y hs
        apply if_false_peak
        · simp [Expr.eval,ρidx,ρlen,hi,Value.natVal]
        · exact h47
        · exact h49
        · exact noRenewalExpr_peak ρidx H y.length (by simpa [ρidx,ρlen] using hH)
            (by simp [ρidx,ρlen]) (by omega)
      | some z =>
        obtain ⟨hlen,hdrop⟩:=firstIndex_some y z hs
        have hi : firstIndex y<y.length := by omega
        apply if_true_peak
        · simp [Expr.eval,ρidx,ρlen,hi,Value.natVal]
        · exact h47
        · exact h49
        · exact visibleBranch_peak ρidx H y z hpos (by simpa [ρidx,ρlen] using hH)
            (by simpa [ρidx,ρlen] using hword) (by simp [ρidx,ρlen]) (by simp [ρidx]) hs hy

end Paper37.IntegerQueryProgramPeak
