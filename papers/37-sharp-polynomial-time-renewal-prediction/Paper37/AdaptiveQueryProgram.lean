import Paper37.AdaptiveBatchProgram
import Paper37.RefinedOutputProgram
import Paper37.CacheBuilderProgram
import Paper37.RefinedCoreProgram
import Paper37.IntegerOutputProgram

/-! A fixed first-order program for the exact standard source predictor.
Every query builds finite coefficient arrays, parses the actual input word,
executes the cached refined recurrence and extracts all integer restrictions. -/
namespace Paper37.AdaptiveQueryProgram
open Paper37.BoundedLoop Paper37.WordProgram Paper37.AdaptiveBatchProgram
open Paper37.AdaptiveIntegerOutput Paper37.CachedDP Paper37.RefinedCoreProgram
open Paper37.CachedCoreProgram (chooseValue powerValue observedValue natArray)
open Paper37.CachedRefinedDP
open Paper37.CacheBuilderProgram Paper37.CachedOutput Paper37.ContinuationDP
open Paper37.Envelope
set_option linter.unusedSimpArgs false
private abbrev v := Expr.var

def continuationBody : Expr := .bind 1 (.get (v 58) (Expr.lit 0))
  (.bind 11 (.get (v 58) (Expr.lit 1))
    (.bind 4 (.get (v 58) (Expr.lit 2))
      (.bind 5 coreProgram Paper37.RefinedOutputProgram.outputProgram)))

def continuationProgram : Expr := .bind 2 chooseProgram
  (.bind 3 powerProgram (.bind 58 parserProgram continuationBody))

lemma continuationBody_eval (ρ : Env) (H : ℕ) (z : List Bool) (R : ℕ)
    (hH : ρ 0=.nat H) (h2 : ρ 2=chooseValue (makeObservedCache H z))
    (h3 : ρ 3=powerValue (makeObservedCache H z)) (hR : ρ 12=.nat R)
    (hs : ρ 58=.array [.nat (parseAge 0 z),.nat (parseGaps 0 z).length,
      observedValue (makeObservedCache H z)]) (hz : z.length+R≤H) :
    continuationBody.eval ρ=natArray (allNumerators H z R) := by
  let c:=makeObservedCache H z
  let A:=parseAge 0 z
  let r:=(parseGaps 0 z).length
  let ρA:=Function.update ρ 1 (.nat A)
  let ρr:=Function.update ρA 11 (.nat r)
  let ρa:=Function.update ρr 4 (observedValue c)
  have hcore:=coreProgram_eval c A ρa (by simpa [ρa,ρr,ρA] using hH)
    (by simp [ρa,ρr,ρA]) (by simpa [ρa,ρr,ρA,c] using h2)
    (by simpa [ρa,ρr,ρA,c] using h3) (by simp [ρa])
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
  have houtput := Paper37.RefinedOutputProgram.outputProgram_eval_inputs hout
    (by have ha:=age_le_length z;dsimp [A];omega)
  rw [Paper37.RefinedOutputProgram.outputValues_source H z R (by omega)] at houtput
  simp only [continuationBody,Expr.eval,hs]
  simp only [Function.update_of_ne (by decide : (58:ℕ)≠1),
    Function.update_of_ne (by decide : (58:ℕ)≠11),Value.arrayVal,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,hs,Value.natVal]
  change Paper37.RefinedOutputProgram.outputProgram.eval
    (Function.update ρa 5 (coreProgram.eval ρa))=_
  rw [hcore]
  exact houtput

/-- Uniform exact C.8 query: the only inputs are finite word40, horizon0 and
remaining-length12. All coefficient arrays and histograms are constructed. -/
theorem continuationProgram_eval (ρ : Env) (H : ℕ) (z : List Bool) (R : ℕ)
    (hH : ρ 0=.nat H) (hword : ρ 40=wordValue z) (hR : ρ 12=.nat R)
    (hz : z.length+R≤H) :
    continuationProgram.eval ρ=natArray (allNumerators H z R) := by
  have hchoose:=Paper37.CacheBuilderProgram.chooseProgram_source ρ H z hH
  let ρc:=Function.update ρ 2 (chooseValue (makeObservedCache H z))
  have hpower:=Paper37.CacheBuilderProgram.powerProgram_source ρc H z (by simpa [ρc] using hH)
  let ρp:=Function.update ρc 3 (powerValue (makeObservedCache H z))
  have hparse:=parserProgram_eval_source ρp H z (by simpa [ρp,ρc] using hH)
    (by simpa [ρp,ρc] using hword)
  rw [continuationProgram,Expr.eval,hchoose]
  change (Expr.bind 3 powerProgram (.bind 58 parserProgram continuationBody)).eval ρc=_
  rw [Expr.eval,hpower]
  change (Expr.bind 58 parserProgram continuationBody).eval ρp=_
  rw [Expr.eval,hparse]
  apply continuationBody_eval
  · simpa [ρp,ρc] using hH
  · simp [ρp,ρc]
  · simp [ρp]
  · simpa [ρp,ρc] using hR
  · simp
  · exact hz


def componentIndex : Expr := .add (v 62) (.lit 1)
def weightProgram : Expr := .ifLT componentIndex (v 0)
  (.array [.lit 1,.mul (.mul (.lit 2) componentIndex) (.add componentIndex (.lit 1))])
  (.array [.add (v 0) (.lit 1),.mul (.lit 2) (v 0)])

def componentProgram : Expr := .bind 63 weightProgram (.array [
  .mul (.get (v 63) (.lit 0)) (.get (v 60) (.min componentIndex (v 0))),
  .mul (.mul (.get (v 63) (.lit 1)) (.add (v 0) (.lit 1)))
    (.get (v 61) (.min componentIndex (v 0)))])

def mixBody : Expr := .bind 53 (v 64) (.bind 54 componentProgram pairAddProgram)
def mixProgram : Expr := .fold 62 64 (v 0) (.array [.lit 0,.lit 1]) mixBody

lemma weightProgram_eval (ρ : Env) (N t : ℕ) (hN:ρ 0=.nat N) (ht:ρ 62=.nat t) (htN:t<N) :
    weightProgram.eval ρ=pairValue (weightPair N (t+1)) := by
  simp only [weightProgram,componentIndex,Expr.eval,hN,ht,Value.natVal]
  by_cases he:t+1=N
  · simp [he,weightPair,pairValue,Expr.eval,Value.natVal,hN,ht,v]
  · have hl:t+1<N := by omega
    simp [hl,he,weightPair,pairValue,Expr.eval,Value.natVal,hN,ht,v]

lemma componentProgram_eval (ρ : Env) (N t : ℕ) (masses norms : Vector ℕ (N+1))
    (hN:ρ 0=.nat N) (ht:ρ 62=.nat t) (htN:t<N)
    (hm:ρ 60=natArray masses) (hn:ρ 61=natArray norms) :
    componentProgram.eval ρ=pairValue
      ((weightPair N (t+1)).1*lookupNumerator masses (t+1),
       (weightPair N (t+1)).2*(N+1)*lookupNumerator norms (t+1)) := by
  rw [componentProgram,Expr.eval,weightProgram_eval ρ N t hN ht htN]
  simp only [componentIndex,v,Expr.eval,Function.update_apply,
    show (0:ℕ)≠63 by decide,show (62:ℕ)≠63 by decide,show (60:ℕ)≠63 by decide,
    show (61:ℕ)≠63 by decide,if_false,if_true,hN,ht,hm,hn,Value.natVal,
    pairValue_get_zero,pairValue_get_one,List.map_cons,List.map_nil]
  rw [Paper37.CachedCoreProgram.natArray_get masses (min (t+1) N) (by have hh:=min_le_right (t+1) N;omega),
    Paper37.CachedCoreProgram.natArray_get norms (min (t+1) N) (by have hh:=min_le_right (t+1) N;omega)]
  rfl

lemma mixBody_eval (ρ : Env) (N t : ℕ) (masses norms : Vector ℕ (N+1)) (p : ℕ×ℕ)
    (hN:ρ 0=.nat N) (ht:ρ 62=.nat t) (htN:t<N)
    (hm:ρ 60=natArray masses) (hn:ρ 61=natArray norms) (hp:ρ 64=pairValue p) :
    mixBody.eval ρ=pairValue (Paper37.IntegerOutput.pairAdd p
      ((weightPair N (t+1)).1*lookupNumerator masses (t+1),
       (weightPair N (t+1)).2*(N+1)*lookupNumerator norms (t+1))) := by
  let σ:=Function.update ρ 53 (pairValue p)
  have hc:=componentProgram_eval σ N t masses norms (by simpa [σ] using hN)
    (by simpa [σ] using ht) htN (by simpa [σ] using hm) (by simpa [σ] using hn)
  simp only [mixBody,Expr.eval,v,hp]
  change pairAddProgram.eval (Function.update σ 54 (componentProgram.eval σ))=_
  rw [hc]
  apply pairAddProgram_eval <;> simp [σ]

lemma mixProgram_eval (ρ : Env) (N : ℕ) (masses norms : Vector ℕ (N+1))
    (hN:ρ 0=.nat N) (hm:ρ 60=natArray masses) (hn:ρ 61=natArray norms) :
    mixProgram.eval ρ=pairValue (Paper37.IntegerOutput.pairSum (componentPairs N masses norms)) := by
  let f:=fun t=>((weightPair N (t+1)).1*lookupNumerator masses (t+1),
    (weightPair N (t+1)).2*(N+1)*lookupNumerator norms (t+1))
  have hf : ∀(is:List ℕ),(∀t∈is,t<N)→∀p,
      is.foldl (fun val t=>mixBody.eval (Function.update (Function.update ρ 62 (.nat t)) 64 val))
        (pairValue p)=pairValue ((is.map f).foldl Paper37.IntegerOutput.pairAdd p) := by
    intro is
    induction is with
    | nil => intros;rfl
    | cons t is ih =>
      intro his p
      simp only [List.foldl_cons,List.map_cons]
      rw [mixBody_eval _ N t masses norms p (by simpa using hN) (by simp) (his t (by simp))
        (by simpa using hm) (by simpa using hn) (by simp)]
      exact ih (fun j hj=>his j (by simp [hj])) _
  have hl : (List.range N).map f=componentPairs N masses norms := by
    apply List.ext_getElem (by simp [componentPairs])
    intro i hi hj
    simp [f,componentPairs]
  have hh:=hf (List.range N) (fun _ ht=>List.mem_range.mp ht) (0,1)
  rw [hl,foldl_pairAdd,pairAdd_zero] at hh
  simpa [mixProgram,Expr.eval,hN,Value.natVal,pairValue] using hh

/-- Slot48 is the effective horizon after the first visible renewal. Both
all-restriction tables are computed once, then every mixture weight reads them. -/
def visiblePrefixProgram : Expr := .bind 12 (.sub (v 48) (.length (v 40)))
  (.bind 60 continuationProgram
    (.bind 61 (.bind 40 (.array []) (.bind 12 (v 48) continuationProgram)) mixProgram))

lemma visiblePrefixProgram_eval (ρ : Env) (N L : ℕ) (z : List Bool)
    (hN:ρ 0=.nat N) (hLslot:ρ 48=.nat L) (hz:ρ 40=wordValue z)
    (hL:L≤N) (hzL:z.length≤L) :
    visiblePrefixProgram.eval ρ=pairValue (Paper37.IntegerOutput.pairSum
      (componentPairs N (allNumerators N z (L-z.length)) (allNumerators N [] L))) := by
  let ρR:=Function.update ρ 12 (.nat (L-z.length))
  have hc:=continuationProgram_eval ρR N z (L-z.length) (by simpa [ρR] using hN)
    (by simpa [ρR] using hz) (by simp [ρR]) (by omega)
  let ρm:=Function.update ρR 60 (natArray (allNumerators N z (L-z.length)))
  let ρempty:=Function.update (Function.update ρm 40 (wordValue [])) 12 (.nat L)
  have he:=continuationProgram_eval ρempty N [] L (by simpa [ρempty,ρm,ρR] using hN)
    (by simp [ρempty]) (by simp [ρempty]) (by simpa using hL)
  have hnorm : (Expr.bind 40 (.array []) (.bind 12 (v 48) continuationProgram)).eval ρm=
      natArray (allNumerators N [] L) := by
    simp only [Expr.eval]
    have h48:ρm 48=.nat L := by simpa [ρm,ρR] using hLslot
    simp only [Function.update_of_ne (by decide : (48:ℕ)≠40),h48]
    exact he
  rw [visiblePrefixProgram,Expr.eval]
  rw [show (Expr.sub (v 48) (.length (v 40))).eval ρ=.nat (L-z.length) by
    simp [Expr.eval,hLslot,hz,Value.natVal]]
  change (Expr.bind 60 continuationProgram _).eval ρR=_
  rw [Expr.eval,hc]
  change (Expr.bind 61 _ mixProgram).eval ρm=_
  rw [Expr.eval,hnorm]
  apply mixProgram_eval
  · simpa [ρm,ρR] using hN
  · simp [ρm]
  · simp

/-- Parse the first renewal in the actual word before selecting its exact
integer all-zero or shared-refinement mixture branch. -/
def prefixProgram : Expr := .bind 49 (.length (v 40)) (.bind 47 firstIndexProgram
  (.ifLT (v 47) (v 49)
    (.bind 44 (.add (v 47) (.lit 1)) (.bind 40 dropProgram
      (.bind 48 (.add (.sub (v 0) (v 49)) (.length (v 40))) visiblePrefixProgram)))
    (.array [.add (.sub (v 0) (v 49)) (.lit 1),.add (v 0) (.lit 1)])))

lemma prefixProgram_eval (ρ : Env) (N : ℕ) (y : List Bool)
    (hN:ρ 0=.nat N) (hword:ρ 40=wordValue y) (hy:y.length≤N) :
    prefixProgram.eval ρ=pairValue (prefixPair N y) := by
  let ρlen:=Function.update ρ 49 (.nat y.length)
  have hidx:=firstIndexProgram_eval ρlen y (by simpa [ρlen] using hword)
  let ρidx:=Function.update ρlen 47 (.nat (firstIndex y))
  rw [prefixProgram,Expr.eval]
  rw [show (Expr.length (v 40)).eval ρ=Value.nat y.length by simp [Expr.eval,hword]]
  change (Expr.bind 47 firstIndexProgram _).eval ρlen=_
  rw [Expr.eval,hidx]
  change (Expr.ifLT (v 47) (v 49) _ _).eval ρidx=_
  cases hs:Paper37.Prediction.firstSuffix y with
  | none =>
    have hi:=firstIndex_none y hs
    simp [Expr.eval,ρidx,ρlen,hi,hN,pairValue,prefixPair,hs,Value.natVal]
  | some z =>
    obtain ⟨hlen,hdrop⟩:=firstIndex_some y z hs
    have hi:firstIndex y<y.length := by omega
    have hbranch : (Expr.ifLT (v 47) (v 49)
      (.bind 44 (.add (v 47) (.lit 1)) (.bind 40 dropProgram
        (.bind 48 (.add (.sub (v 0) (v 49)) (.length (v 40))) visiblePrefixProgram)))
      (.array [.add (.sub (v 0) (v 49)) (.lit 1),.add (v 0) (.lit 1)])).eval ρidx=
      (Expr.bind 44 (.add (v 47) (.lit 1)) (.bind 40 dropProgram
        (.bind 48 (.add (.sub (v 0) (v 49)) (.length (v 40))) visiblePrefixProgram))).eval ρidx := by
      simp [Expr.eval,ρidx,ρlen,hi,Value.natVal]
    rw [hbranch]
    let ρd:=Function.update ρidx 44 (.nat (firstIndex y+1))
    have hd:=dropProgram_eval ρd y (firstIndex y+1) (by simpa [ρd,ρidx,ρlen] using hword) (by simp [ρd])
    rw [hdrop] at hd
    simp only [Expr.eval]
    simp only [ρidx,Function.update_self,Value.natVal]
    dsimp only [ρd,ρidx] at hd
    rw [hd]
    let ρz:=Function.update ρd 40 (wordValue z)
    have hv:=visiblePrefixProgram_eval (Function.update ρz 48 (.nat (N-y.length+z.length))) N
      (N-y.length+z.length) z (by simpa [ρz,ρd,ρidx,ρlen] using hN) (by simp)
      (by simp [ρz]) (by omega) (by omega)
    simp only [ρz,ρd,ρidx,ρlen,Function.update_of_ne (by decide : (0:ℕ)≠40),
      Function.update_of_ne (by decide : (0:ℕ)≠44),Function.update_of_ne (by decide : (0:ℕ)≠47),
      Function.update_of_ne (by decide : (0:ℕ)≠49),hN]
    simp only [Function.update_apply,if_false,if_true,wordValue_length,Value.natVal]
    change visiblePrefixProgram.eval
      (Function.update ρz 48 (.nat (N-y.length+z.length)))=_
    rw [hv]
    simp [prefixPair,hs]

def conditionalArray : Expr := .array [
  .mul (.get (v 71) (.lit 0)) (.get (v 72) (.lit 1)),
  .mul (.get (v 71) (.lit 1)) (.get (v 72) (.lit 0))]
def conditionalProgram : Expr :=
  .bind 71 (.bind 46 (.lit 1) (.bind 40 appendProgram prefixProgram))
    (.bind 72 prefixProgram conditionalArray)

lemma conditionalProgram_eval (ρ : Env) (N : ℕ) (y : List Bool)
    (hN:ρ 0=.nat N) (hword:ρ 40=wordValue y) (hy:y.length<N) :
    conditionalProgram.eval ρ=pairValue (conditionalPair N y) := by
  let ρbit:=Function.update ρ 46 (bitValue true)
  have happ:=appendProgram_eval ρbit y true (by simpa [ρbit] using hword) (by simp [ρbit])
  have hchild:=prefixProgram_eval (Function.update ρbit 40 (wordValue (y++[true]))) N (y++[true])
    (by simpa [ρbit] using hN) (by simp) (by simp;omega)
  have hc : (Expr.bind 46 (.lit 1) (.bind 40 appendProgram prefixProgram)).eval ρ=
      pairValue (prefixPair N (y++[true])) := by
    simp only [Expr.eval]
    change prefixProgram.eval (Function.update ρbit 40 (appendProgram.eval ρbit))=_
    rw [happ]
    exact hchild
  let ρc:=Function.update ρ 71 (pairValue (prefixPair N (y++[true])))
  have hp:=prefixProgram_eval ρc N y (by simpa [ρc] using hN) (by simpa [ρc] using hword) hy.le
  rw [conditionalProgram,Expr.eval,hc]
  change (Expr.bind 72 prefixProgram conditionalArray).eval ρc=_
  rw [Expr.eval,hp]
  simp [conditionalArray,Expr.eval,ρc,pairValue,conditionalPair,Value.arrayVal,Value.natVal]

/-- The single final syntax term constructs its horizon from the input word
and performs the specified suffix batch; no higher-order query oracle remains. -/
def predictorProgram : Expr := .bind 0 (.add (.length (v 40)) (.lit 1))
  (batchProgram conditionalProgram)

theorem predictorProgram_eval (ρ : Env) (x : List Bool) (hx:ρ 40=wordValue x) :
    predictorProgram.eval ρ=pairValue (predictorPair x.length x) := by
  have hq:QueryCorrect conditionalProgram (x.length+1) := fun σ y hN hw hy=>
    conditionalProgram_eval σ _ y hN hw hy
  simp only [predictorProgram,Expr.eval,hx,wordValue_length,Value.natVal]
  exact batchProgram_eval conditionalProgram x.length hq _ x rfl (by simp) (by simpa using hx)

theorem predictorProgram_source (ρ : Env) (x : List Bool) (hx:ρ 40=wordValue x) :
    let out:=predictorProgram.eval ρ
    ((out.arrayVal[0]?.getD (Value.nat 0)).natVal:ℚ)/
      (out.arrayVal[1]?.getD (Value.nat 0)).natVal=Paper37.Adaptive.adaptivePredict x.length x := by
  rw [predictorProgram_eval ρ x hx]
  exact predictorPair_exact x.length x rfl

end Paper37.AdaptiveQueryProgram
