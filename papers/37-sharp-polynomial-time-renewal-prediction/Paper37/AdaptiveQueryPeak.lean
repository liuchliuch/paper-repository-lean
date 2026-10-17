import Paper37.AdaptiveQueryProgram
import Paper37.AdaptiveMixPeak
import Paper37.WordProgramPeak
import Paper37.CacheBuilderProgramPeak
import Paper37.RefinedCorePolynomial
import Paper37.RefinedOutputPeak
import Paper37.PredictorBatchPeak
import Paper37.IntegerOutputPeak

/-! Actual dynamic peaks for the complete adaptive query AST. The generous
polynomial envelopes below bound real interpreter intermediates. -/
namespace Paper37.AdaptiveQueryPeak
open Paper37.BoundedLoop Paper37.WordProgram Paper37.AdaptiveQueryProgram
open Paper37.AdaptiveIntegerOutput Paper37.CachedDP Paper37.CachedRefinedDP
open Paper37.RefinedCoreProgram
open Paper37.RefinedOutputProgram (outputProgram)
open Paper37.CachedCoreProgram (chooseValue powerValue observedValue natArray)
open Paper37.CacheBuilderProgram Paper37.CachedOutput Paper37.ContinuationDP Paper37.Envelope
open Paper37.IntegerOutputPeak
set_option linter.unusedSimpArgs false
private abbrev v := BoundedLoop.Expr.var

def queryPeakBound (H : ℕ) : ℕ := 1000000000000000000*(H+2)^20

lemma poly2_le_query (H C k : ℕ) (hC : C≤1000000000000000000) (hk : k≤20) :
    C*(H+2)^k≤queryPeakBound H := by
  unfold queryPeakBound
  exact Nat.mul_le_mul hC (Nat.pow_le_pow_right (by omega) hk)
lemma poly1_le_query (H C k : ℕ) (hC : C≤1000000000000000000) (hk : k≤20) :
    C*(H+1)^k≤queryPeakBound H :=
  (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega) k)).trans (poly2_le_query H C k hC hk)

lemma nat_representation (a H : ℕ) (ha : a≤H) :
    (Value.nat a).representationSize≤H+1 := nat_representation_le ha

lemma nat_rep_query (a H : ℕ) (ha : a≤H+1) :
    (Value.nat a).representationSize≤queryPeakBound H := by
  exact (nat_representation_le ha).trans (by
    have hh:=poly2_le_query H 1 1 (by norm_num) (by norm_num)
    simpa using hh)

lemma outputBitBound_polynomial (H : ℕ) :
    Paper37.IntegerPredictor.outputBitBound H≤100*(H+2)^3 := by
  have h1:=Paper37.DP.binarySize_le_self (H+1)
  have h2:=Paper37.DP.binarySize_le_self (2*H)
  have h3:=Paper37.DP.binarySize_le_self H
  have hd : H*(H+1)/2≤H*(H+1) := Nat.div_le_self _ _
  unfold Paper37.IntegerPredictor.outputBitBound
  calc _ ≤2*(H+1)+(4*H+1)*(2*H)+(H*(H+1))*H+5 := by gcongr
       _ ≤_ := by ring_nf;omega

lemma componentBitBound_polynomial (H : ℕ) : componentBitBound H≤200*(H+2)^3 := by
  have ho:=outputBitBound_polynomial H
  have hw:=Paper37.DP.binarySize_le_self (2*(H+1))
  have hn:=Paper37.DP.binarySize_le_self (H+1)
  unfold componentBitBound weightBitBound
  calc _ ≤2*(2*(H+1))+1+100*(H+2)^3+(H+1)+2 := by omega
       _ ≤_ := by ring_nf;omega

lemma prefixBitBound_polynomial (H : ℕ) : prefixBitBound H≤1000*(H+2)^4 := by
  have hc:=componentBitBound_polynomial H
  have hn:=Paper37.DP.binarySize_le_self (H+1)
  unfold prefixBitBound
  calc _ ≤H*(200*(H+2)^3+4)+(H+1)+3 := by gcongr
       _ ≤_ := by ring_nf;omega

lemma conditionalBitBound_polynomial (H : ℕ) : conditionalBitBound H≤3000*(H+2)^4 := by
  have hp:=prefixBitBound_polynomial H
  unfold conditionalBitBound
  calc _ ≤2*(1000*(H+2)^4)+1 := by omega
       _ ≤_ := by ring_nf;omega

lemma pairValue_size (p : ℕ×ℕ) :
    (pairValue p).representationSize≤2*Paper37.IntegerOutput.pairSize p+4 := by
  have h1 : p.1.size≤Paper37.IntegerOutput.pairSize p := le_max_left _ _
  have h2 : p.2.size≤Paper37.IntegerOutput.pairSize p := le_max_right _ _
  simp only [pairValue,Value.representationSize,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  omega

lemma prefixPair_size (H : ℕ) (y : List Bool) (hH : 0<H) (hy : y.length≤H) :
    (pairValue (prefixPair H y)).representationSize≤3000*(H+2)^4 := by
  have hs:=pairValue_size (prefixPair H y)
  have hp:=prefixPair_binarySize H y hH hy
  have hb:=prefixBitBound_polynomial H
  have hpow : 1≤(H+2)^4 := one_le_pow₀ (by omega)
  omega

lemma allNumerators_size (H : ℕ) (z : List Bool) (R : ℕ) (hH : 0<H)
    (hz : z.length+R≤H) :
    (natArray (allNumerators H z R)).representationSize≤1000*(H+2)^4 := by
  have hs:=Paper37.CachedCoreProgram.natArray_size_le (allNumerators H z R)
    (Paper37.IntegerPredictor.outputBitBound H) (allNumerators_binarySize H z R hH hz)
  have hb:=outputBitBound_polynomial H
  calc _ ≤(H+1)*(100*(H+2)^3+1)+2 := hs.trans (by gcongr)
       _ ≤_ := by ring_nf;omega

lemma parsed_frame_size (H : ℕ) (z : List Bool) (hz : z.length≤H) :
    (Value.array [.nat (parseAge 0 z),.nat (parseGaps 0 z).length,
      observedValue (makeObservedCache H z)]).representationSize≤10*(H+2)^2 := by
  have ha:=nat_representation_le ((age_le_length z).trans hz)
  have hr:=nat_representation_le (show (parseGaps 0 z).length≤H by have hh:=Paper37.IntegerOutput.count_add_age_le z;omega)
  have hc:=source_observed_representation H z hz
  simp only [Value.representationSize,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at *
  nlinarith

lemma frame_get_peak (ρ : Env) (H k : ℕ) (hk : k≤2)
    (hs : (ρ 58).representationSize≤10*(H+2)^2) :
    (BoundedLoop.Expr.get (.var 58) (.lit k)).peak ρ≤queryPeakBound H := by
  have hg:=get_peak_le (.var 58) (.lit k) ρ (10*(H+2)^2) 3
    (var_peak_of_rep ρ 58 _ hs) (by
      have hh:=nat_representation_le hk
      simpa [Expr.peak,Expr.eval,Value.representationSize] using hh)
  have hp:=poly2_le_query H 20 2 (by norm_num) (by norm_num)
  have hp2 : 1≤(H+2)^2 := one_le_pow₀ (by omega)
  omega

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

def remainingExpr : Expr := .sub (.var 48) (.length (.var 40))
def effectiveExpr : Expr := .add (.sub (.var 0) (.var 49)) (.length (.var 40))
def noRenewalExpr : Expr := .array
  [.add (.sub (.var 0) (.var 49)) (.lit 1),.add (.var 0) (.lit 1)]
def visibleBranch : Expr := .bind 44 (.add (.var 47) (.lit 1))
  (.bind 40 dropProgram (.bind 48 effectiveExpr visiblePrefixProgram))

lemma remainingExpr_flat : Flat remainingExpr := by
  exact Flat.binary .sub _ _ (Flat.var _) (Flat.length _ (Flat.var _))
lemma effectiveExpr_flat : Flat effectiveExpr := by
  exact Flat.binary .add _ _ (Flat.binary .sub _ _ (Flat.var _) (Flat.var _))
    (Flat.length _ (Flat.var _))
lemma noRenewalExpr_flat : Flat noRenewalExpr := by
  unfold noRenewalExpr
  apply Flat.array
  intro e he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl
  · exact Flat.binary .add _ _ (Flat.binary .sub _ _ (Flat.var _) (Flat.var _)) (Flat.lit _)
  · exact Flat.binary .add _ _ (Flat.var _) (Flat.lit _)

lemma remainingExpr_peak (ρ : Env) (H L : ℕ) (z : List Bool)
    (hLslot : ρ 48=.nat L) (hword : ρ 40=wordValue z) (hL : L≤H) (hz : z.length≤H) :
    remainingExpr.peak ρ≤queryPeakBound H := by
  have hLr:=nat_representation_le hL
  have hwr:=wordValue_size z
  have hh:=flat_peak_le remainingExpr_flat ρ (wordFrame H) (by
    simp only [remainingExpr,Expr.varsBound,hLslot,hword]
    exact ⟨(nat_wordFrame (show L≤H+1 by omega)),word_frame z H hz⟩)
  apply hh.trans
  have hp:=poly2_le_query H 1000 1 (by norm_num) (by norm_num)
  simp only [pow_one] at hp
  simp [remainingExpr,Expr.flatBudget,wordFrame]
  omega

lemma effectiveExpr_peak (ρ : Env) (H m : ℕ) (z : List Bool)
    (hH : ρ 0=.nat H) (hm : ρ 49=.nat m) (hword : ρ 40=wordValue z)
    (hmH : m≤H) (hz : z.length≤H) : effectiveExpr.peak ρ≤queryPeakBound H := by
  have hh:=flat_peak_le effectiveExpr_flat ρ (wordFrame H) (by
    simp only [effectiveExpr,Expr.varsBound,hH,hm,hword]
    exact ⟨⟨nat_wordFrame (by omega),nat_wordFrame (by omega)⟩,word_frame z H hz⟩)
  apply hh.trans
  have hp:=poly2_le_query H 1000 1 (by norm_num) (by norm_num)
  simp only [pow_one] at hp
  simp [effectiveExpr,Expr.flatBudget,wordFrame]
  omega

lemma noRenewalExpr_peak (ρ : Env) (H m : ℕ)
    (hH : ρ 0=.nat H) (hm : ρ 49=.nat m) (hmH : m≤H) :
    noRenewalExpr.peak ρ≤queryPeakBound H := by
  have hHr:=nat_representation_le (show H≤H by rfl)
  have hmr:=nat_representation_le hmH
  have hh:=flat_peak_le noRenewalExpr_flat ρ (H+1) (by
    simp only [noRenewalExpr,Expr.varsBound,hH,hm]
    intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl
    · simpa only [Expr.varsBound,hH,hm] using And.intro (And.intro hHr hmr) True.intro
    · simpa only [Expr.varsBound,hH] using And.intro hHr True.intro)
  apply hh.trans
  have hp:=poly2_le_query H 1000 1 (by norm_num) (by norm_num)
  simp only [pow_one] at hp
  have ho : (1:ℕ).size=1 := by simpa using Nat.size_pow 0
  simp [noRenewalExpr,Expr.flatBudget,ho]
  omega

lemma conditionalArray_flat : Flat conditionalArray := by
  unfold conditionalArray
  apply Flat.array
  intro e he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl
  all_goals exact (Flat.binary .mul _ _
    (Flat.get _ _ (Flat.var _) (Flat.lit _)) (Flat.get _ _ (Flat.var _) (Flat.lit _)))

lemma conditionalArray_peak (ρ : Env) (H : ℕ) (p q : ℕ×ℕ)
    (hp : ρ 71=pairValue p) (hq : ρ 72=pairValue q)
    (hps : (pairValue p).representationSize≤3000*(H+2)^4)
    (hqs : (pairValue q).representationSize≤3000*(H+2)^4) :
    conditionalArray.peak ρ≤queryPeakBound H := by
  have hh:=flat_peak_le conditionalArray_flat ρ (3000*(H+2)^4) (by
    simp only [conditionalArray,Expr.varsBound,hp,hq]
    intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl
    · simpa only [Expr.varsBound,hp,hq] using And.intro (And.intro hps True.intro) (And.intro hqs True.intro)
    · simpa only [Expr.varsBound,hp,hq] using And.intro (And.intro hps True.intro) (And.intro hqs True.intro))
  apply hh.trans
  have hp:=poly2_le_query H 100000 4 (by norm_num) (by norm_num)
  have hpow : 1≤(H+2)^4 := one_le_pow₀ (by omega)
  have ho : (1:ℕ).size=1 := by simpa using Nat.size_pow 0
  simp [conditionalArray,Expr.flatBudget,ho]
  omega

/-- The actual finite E.3 mixture reads two already-computed shared vectors.
All component weights and every partial cross-multiplication are included. -/
lemma mixProgram_source_peak (ρ : Env) (H L : ℕ) (z : List Bool) (hpos : 0<H)
    (hH : ρ 0=.nat H) (hL : L≤H) (hz : z.length≤L)
    (hm : ρ 60=natArray (allNumerators H z (L-z.length)))
    (hn : ρ 61=natArray (allNumerators H [] L)) :
    mixProgram.peak ρ≤queryPeakBound H := by
  have hp:=Paper37.AdaptiveMixPeak.mixProgram_peak_le ρ H
    (Paper37.IntegerPredictor.outputBitBound H)
    (allNumerators H z (L-z.length)) (allNumerators H [] L) hpos hH hm hn
    (allNumerators_binarySize H z (L-z.length) hpos (by omega))
    (allNumerators_binarySize H [] L hpos (by simpa using hL))
  apply hp.trans
  have hb:=outputBitBound_polynomial H
  have hpoly : 10000000*(H+1)^2*(100*(H+2)^3+H+10)≤1000000000000*(H+2)^5 := by
    ring_nf
    omega
  exact (Nat.mul_le_mul_left _ (Nat.add_le_add_right hb (H+10))).trans
    (hpoly.trans (poly2_le_query H 1000000000000 5 (by norm_num) (by norm_num)))

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
  have hpcore:=Paper37.RefinedCoreProgram.coreProgram_source_peak_polynomial H z A ρa hpos (by omega)
    (by dsimp [A];exact (age_le_length z).trans (by omega))
    (by simpa [ρa,ρr,ρA] using hH) (by simp [ρa,ρr,ρA])
    (by simpa [ρa,ρr,ρA,c] using h2) (by simpa [ρa,ρr,ρA,c] using h3) (by simp [ρa,c])
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
  have hpout:=Paper37.RefinedOutputPeak.outputProgram_source_peak H z R ρt hpos hz hout
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
        · exact hpcore.trans (poly1_le_query H 2510000000 8 (by norm_num) (by norm_num))
        · rw [hcore]
          exact hpout.trans (poly2_le_query H 1000000000000000 12 (by norm_num) (by norm_num))

/-- Complete continuation query, including its actual cache construction,
parser, materialized recurrence and integer pair output. -/
theorem continuationProgram_peak (ρ : Env) (H : ℕ) (z : List Bool) (R : ℕ) (hpos : 0<H)
    (hH : ρ 0=.nat H) (hword : ρ 40=wordValue z) (hR : ρ 12=.nat R)
    (hz : z.length+R≤H) : continuationProgram.peak ρ≤queryPeakBound H := by
  have hchoose:=Paper37.CacheBuilderProgram.chooseProgram_source ρ H z hH
  have hpchoose:=Paper37.CacheBuilderProgramPeak.chooseProgram_peak ρ H hH
  let ρc:=Function.update ρ 2 (chooseValue (makeObservedCache H z))
  have hpower:=Paper37.CacheBuilderProgram.powerProgram_source ρc H z (by simpa [ρc] using hH)
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


lemma visiblePrefixProgram_peak (ρ : Env) (H L : ℕ) (z : List Bool) (hpos : 0<H)
    (hH : ρ 0=.nat H) (hLslot : ρ 48=.nat L) (hword : ρ 40=wordValue z)
    (hL : L≤H) (hz : z.length≤L) :
    visiblePrefixProgram.peak ρ≤queryPeakBound H := by
  let ρR:=Function.update ρ 12 (.nat (L-z.length))
  have hc:=continuationProgram_eval ρR H z (L-z.length) (by simpa [ρR] using hH)
    (by simpa [ρR] using hword) (by simp [ρR]) (by omega)
  have hpc:=continuationProgram_peak ρR H z (L-z.length) hpos (by simpa [ρR] using hH)
    (by simpa [ρR] using hword) (by simp [ρR]) (by omega)
  let ρm:=Function.update ρR 60 (natArray (allNumerators H z (L-z.length)))
  let ρempty:=Function.update (Function.update ρm 40 (wordValue [])) 12 (.nat L)
  have he:=continuationProgram_eval ρempty H [] L (by simpa [ρempty,ρm,ρR] using hH)
    (by simp [ρempty]) (by simp [ρempty]) (by simpa using hL)
  have hpe:=continuationProgram_peak ρempty H [] L hpos (by simpa [ρempty,ρm,ρR] using hH)
    (by simp [ρempty]) (by simp [ρempty]) (by simpa using hL)
  let normExpr:Expr:=.bind 40 (.array []) (.bind 12 (.var 48) continuationProgram)
  have hnorm:normExpr.eval ρm=natArray (allNumerators H [] L) := by
    simp only [normExpr,Expr.eval]
    have h48 : ρm 48=.nat L := by simpa [ρm,ρR] using hLslot
    simp only [Function.update_of_ne (by decide : (48:ℕ)≠40),h48]
    exact he
  have hpnorm:normExpr.peak ρm≤queryPeakBound H := by
    have h48 : ρm 48=.nat L := by simpa [ρm,ρR] using hLslot
    unfold normExpr
    apply bind_peak_bound
    · have hpoly:=poly2_le_query H 1 1 (by norm_num) (by norm_num)
      have hsmall : H+2≤queryPeakBound H := by simpa using hpoly
      have htwo : 2≤queryPeakBound H := by omega
      simpa [Expr.peak,Expr.eval,Value.representationSize] using htwo
    · rw [show (Expr.array []).eval ρm=wordValue [] by simp [Expr.eval,wordValue]]
      change (Expr.bind 12 (.var 48) continuationProgram).peak
        (Function.update ρm 40 (wordValue []))≤_
      apply bind_peak_bound
      · apply var_peak_of_rep
        simpa [h48] using nat_rep_query L H (by omega)
      · simp only [Expr.eval,Function.update_of_ne (by decide : (48:ℕ)≠40),h48]
        exact hpe
  let ρn:=Function.update ρm 61 (natArray (allNumerators H [] L))
  have hpmix:=mixProgram_source_peak ρn H L z hpos (by simpa [ρn,ρm,ρR] using hH)
    hL hz (by simp [ρn,ρm]) (by simp [ρn])
  have hR:remainingExpr.eval ρ=.nat (L-z.length) := by
    simp [remainingExpr,Expr.eval,hLslot,hword,Value.natVal]
  rw [visiblePrefixProgram]
  apply bind_peak_bound
  · exact remainingExpr_peak ρ H L z hLslot hword hL (by omega)
  · change (Expr.bind 60 continuationProgram (.bind 61 normExpr mixProgram)).peak
      (Function.update ρ 12 (remainingExpr.eval ρ))≤_
    rw [hR]
    change (Expr.bind 60 continuationProgram (.bind 61 normExpr mixProgram)).peak ρR≤_
    apply bind_peak_bound
    · exact hpc
    · rw [hc]
      change (Expr.bind 61 normExpr mixProgram).peak ρm≤_
      apply bind_peak_bound
      · exact hpnorm
      · rw [hnorm]
        exact hpmix


lemma visibleBranch_peak (ρ : Env) (H : ℕ) (y z : List Bool) (hpos : 0<H)
    (hH : ρ 0=.nat H) (hword : ρ 40=wordValue y)
    (hlen : ρ 49=.nat y.length) (hidx : ρ 47=.nat (firstIndex y))
    (hs : Paper37.Prediction.firstSuffix y=some z) (hy : y.length≤H) :
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
  have hz : z.length≤L := by dsimp [L];omega
  have heff : effectiveExpr.eval ρz=.nat L := by
    simp [effectiveExpr,Expr.eval,ρz,ρd,hH,hlen,wordValue_length,Value.natVal,L]
  have hpe:=effectiveExpr_peak ρz H y.length z (by simpa [ρz,ρd] using hH)
    (by simpa [ρz,ρd] using hlen) (by simp [ρz]) (by omega) (by omega)
  have hpv:=visiblePrefixProgram_peak (Function.update ρz 48 (.nat L)) H L z hpos
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
    change (Expr.bind 40 dropProgram (.bind 48 effectiveExpr visiblePrefixProgram)).peak ρd≤_
    apply bind_peak_bound
    · exact hpd.trans (poly2_le_query H 100000 3 (by norm_num) (by norm_num))
    · rw [hd]
      change (Expr.bind 48 effectiveExpr visiblePrefixProgram).peak ρz≤_
      apply bind_peak_bound
      · exact hpe
      · rw [heff]
        exact hpv

/-- Closed source-level peak theorem for the actual first-renewal conditional
query. Only its actual horizon and encoded input word are assumed. -/
theorem prefixProgram_peak (ρ : Env) (H : ℕ) (y : List Bool) (hpos : 0<H)
    (hH : ρ 0=.nat H) (hword : ρ 40=wordValue y) (hy : y.length≤H) :
    prefixProgram.peak ρ≤queryPeakBound H := by
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
  rw [prefixProgram]
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


/-- Closed dynamic-peak bound for the actual adaptive conditional query. -/
theorem conditionalProgram_peak (ρ : Env) (H : ℕ) (y : List Bool)
    (hH : ρ 0=.nat H) (hword : ρ 40=wordValue y) (hy : y.length<H) :
    conditionalProgram.peak ρ≤queryPeakBound H := by
  have hpos : 0<H := by omega
  let ρbit:=Function.update ρ 46 (bitValue true)
  have happ:=appendProgram_eval ρbit y true (by simpa [ρbit] using hword) (by simp [ρbit])
  have hpapp:=appendProgram_peak ρbit H y true (by simpa [ρbit] using hword)
    (by simp [ρbit]) (by omega)
  let ρchild:=Function.update ρbit 40 (wordValue (y++[true]))
  have hc:=prefixProgram_eval ρchild H (y++[true]) (by simpa [ρchild,ρbit] using hH)
    (by simp [ρchild]) (by simp;omega)
  have hpc:=prefixProgram_peak ρchild H (y++[true]) hpos (by simpa [ρchild,ρbit] using hH)
    (by simp [ρchild]) (by simp;omega)
  let childExpr:Expr:=.bind 46 (.lit 1) (.bind 40 appendProgram prefixProgram)
  have he:childExpr.eval ρ=pairValue (prefixPair H (y++[true])) := by
    simp only [childExpr,Expr.eval]
    change prefixProgram.eval (Function.update ρbit 40 (appendProgram.eval ρbit))=_
    rw [happ]
    exact hc
  have hpchild:childExpr.peak ρ≤queryPeakBound H := by
    unfold childExpr
    apply bind_peak_bound
    · exact lit_peak_of_rep ρ 1 _ (nat_rep_query 1 H (by omega))
    · rw [show (Expr.lit 1).eval ρ=bitValue true by simp [Expr.eval,bitValue]]
      change (Expr.bind 40 appendProgram prefixProgram).peak ρbit≤_
      apply bind_peak_bound
      · exact hpapp.trans (poly2_le_query H 100000 3 (by norm_num) (by norm_num))
      · rw [happ]
        exact hpc
  let ρc:=Function.update ρ 71 (pairValue (prefixPair H (y++[true])))
  have hp:=prefixProgram_eval ρc H y (by simpa [ρc] using hH) (by simpa [ρc] using hword) hy.le
  have hpp:=prefixProgram_peak ρc H y hpos (by simpa [ρc] using hH) (by simpa [ρc] using hword) hy.le
  let ρp:=Function.update ρc 72 (pairValue (prefixPair H y))
  have hpa:=conditionalArray_peak ρp H (prefixPair H (y++[true])) (prefixPair H y)
    (by simp [ρp,ρc]) (by simp [ρp]) (prefixPair_size H _ hpos (by simp;omega))
    (prefixPair_size H y hpos hy.le)
  change (Expr.bind 71 childExpr (.bind 72 prefixProgram conditionalArray)).peak ρ≤_
  apply bind_peak_bound
  · exact hpchild
  · rw [he]
    change (Expr.bind 72 prefixProgram conditionalArray).peak ρc≤_
    apply bind_peak_bound
    · exact hpp
    · rw [hp]
      exact hpa


/-- Closed peak of the one fixed adaptive predictor, including the actual
suffix-loop accumulator and every component/query intermediate. -/
theorem predictorProgram_peak (ρ : Env) (x : List Bool) (hx : ρ 40=wordValue x) :
    predictorProgram.peak ρ≤10^30*(x.length+2)^21 := by
  let n:=x.length
  let ρH:=Function.update ρ 0 (.nat (n+1))
  have hq : Paper37.PredictorBatchPeak.PairQueryCorrect conditionalProgram (n+1)
      (Paper37.AdaptiveIntegerOutput.conditionalPair (n+1)) := by
    intro σ y hN hw hy
    exact conditionalProgram_eval σ (n+1) y hN hw hy
  have hQ : Paper37.PredictorBatchPeak.QueryPeak conditionalProgram (n+1) (queryPeakBound (n+1)) := by
    intro σ y hN hw hy
    exact conditionalProgram_peak σ (n+1) y hN hw hy
  have hD : Paper37.PredictorBatchPeak.DropPeak n (100000*(n+2)^3) := by
    intro σ y t hw ht hy htn
    exact dropProgram_peak σ n y t hw ht hy htn
  have hB : ∀ y : List Bool,y.length<n+1 →
      Paper37.IntegerOutput.pairSize (Paper37.AdaptiveIntegerOutput.conditionalPair (n+1) y)≤conditionalBitBound (n+1) := by
    intro y hy
    exact conditionalPair_binarySize (n+1) y hy
  have hb:=Paper37.PredictorBatchPeak.batchProgram_peak conditionalProgram n
    (queryPeakBound (n+1)) (100000*(n+2)^3) (conditionalBitBound (n+1))
    (Paper37.AdaptiveIntegerOutput.conditionalPair (n+1)) hq hQ hD hB ρH x rfl
    (by simp [ρH]) (by simpa [ρH] using hx)
  have hshift (k : ℕ) : (n+3)^k≤2^k*(n+2)^k := by
    calc _ ≤(2*(n+2))^k := Nat.pow_le_pow_left (by omega) k
         _ =_ := mul_pow _ _ _
  have hQbound : queryPeakBound (n+1)≤10^25*(n+2)^20 := by
    unfold queryPeakBound
    have hp:=Nat.mul_le_mul_left 1000000000000000000 (hshift 20)
    calc _ ≤1000000000000000000*(2^20*(n+2)^20) := hp
         _ ≤_ := by norm_num;omega
  have hBbound : conditionalBitBound (n+1)≤50000*(n+2)^4 := by
    have hp:=conditionalBitBound_polynomial (n+1)
    have hm:=Nat.mul_le_mul_left 3000 (hshift 4)
    calc _ ≤3000*(n+3)^4 := hp
         _ ≤3000*(2^4*(n+2)^4) := hm
         _ ≤_ := by norm_num;omega
  have hp3 : (n+2)^3≤(n+2)^20 := Nat.pow_le_pow_right (by omega) (by decide)
  have hp5 : (n+2)^5≤(n+2)^20 := Nat.pow_le_pow_right (by omega) (by decide)
  have hp1 : n+2≤(n+2)^20 := le_self_pow₀ (by omega) (by decide)
  have hp0 : 1≤(n+2)^20 := one_le_pow₀ (by omega)
  have hDbound:=Nat.mul_le_mul_left 100000 hp3
  have hterm : n*(conditionalBitBound (n+1)+4)≤100000*(n+2)^20 := by
    calc _ ≤(n+2)*(50000*(n+2)^4+4) := Nat.mul_le_mul (by omega) (by omega)
         _ ≤60000*(n+2)^5 := by ring_nf;omega
         _ ≤100000*(n+2)^20 := (Nat.mul_le_mul_left 60000 hp5).trans (by omega)
  have hsum : 100000*(n+2)^3+queryPeakBound (n+1)+n*(conditionalBitBound (n+1)+4)+n+10≤
      2*10^25*(n+2)^20 := by norm_num at *;omega
  have hbatch : 100000*(100000*(n+2)^3+queryPeakBound (n+1)+n*(conditionalBitBound (n+1)+4)+n+10)≤
      10^30*(n+2)^21 := by
    have hm:=Nat.mul_le_mul_left 100000 hsum
    have ht:=Nat.mul_le_mul_left (10^30*(n+2)^20) (show 2≤n+2 by omega)
    have he : 100000*(2*10^25*(n+2)^20)=2*(10^30*(n+2)^20) := by ring
    rw [he] at hm
    calc _ ≤2*(10^30*(n+2)^20) := hm
         _ ≤(10^30*(n+2)^20)*(n+2) := by simpa [Nat.mul_comm] using ht
         _ =_ := by ring
  have hb' : (Paper37.AdaptiveBatchProgram.batchProgram conditionalProgram).peak ρH≤10^30*(n+2)^21 := by
    change (Paper37.PredictorBatchProgram.batchProgram conditionalProgram).peak ρH≤_
    exact hb.trans hbatch
  have hhorizon : (Expr.add (.length (.var 40)) (.lit 1)).peak ρ≤10^30*(n+2)^21 := by
    have hw:=wordValue_size x
    have hvar:=var_peak_of_rep ρ 40 (2*n+2) (by simpa [hx,n] using hw)
    have hlen:=length_peak_le (.var 40) ρ (2*n+2) hvar
    have hlit : (Expr.lit 1).peak ρ≤2 := by simp [Expr.peak,Expr.eval,Value.representationSize]
    have hp:=binary_peak_le .add (.length (.var 40)) (.lit 1) ρ (2*n+3) 2 hlen hlit
    have hp21 : n+2≤(n+2)^21 := le_self_pow₀ (by omega) (by decide)
    have hm:=Nat.mul_le_mul_left (10^30) hp21
    exact hp.trans (by norm_num [Op.expr] at *;omega)
  rw [predictorProgram]
  apply bind_peak_bound
  · exact hhorizon
  · rw [show (Expr.add (.length (.var 40)) (.lit 1)).eval ρ=.nat (n+1) by
      simp [Expr.eval,hx,n,Value.natVal]]
    exact hb'

end Paper37.AdaptiveQueryPeak
