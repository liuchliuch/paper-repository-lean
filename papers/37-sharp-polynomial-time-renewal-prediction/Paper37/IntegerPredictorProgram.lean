import Paper37.PredictorBatchProgram
import Paper37.CacheBuilderProgram
import Paper37.CachedCoreCorrect
import Paper37.IntegerOutputProgram

/-! A fixed first-order program for the exact standard source predictor.
Every query builds finite coefficient arrays, parses the actual input word,
executes the cached recurrence and sums the shared-table integer output. -/
namespace Paper37.IntegerPredictorProgram
open Paper37.BoundedLoop Paper37.WordProgram Paper37.PredictorBatchProgram
open Paper37.IntegerPredictor Paper37.CachedDP Paper37.CachedCoreProgram
open Paper37.CacheBuilderProgram Paper37.CachedOutput Paper37.ContinuationDP
open Paper37.Envelope
set_option linter.unusedSimpArgs false
private abbrev v := Expr.var

lemma chooseProgram_source (ρ : Env) (H : ℕ) (z : List Bool) (hH : ρ 0=.nat H) :
    chooseProgram.eval ρ=chooseValue (makeObservedCache H z) := by
  rw [chooseProgram_eval ρ H hH]
  unfold chooseValue
  congr 1
  apply List.map_congr_left
  intro k hk
  have hkH : k<H+1 := List.mem_range.mp hk
  simp only [encodeVector]
  congr 1
  apply List.map_congr_left
  intro b hb
  have hbH : b<H+1 := List.mem_range.mp hb
  simp [hkH,hbH,chooseAt,makeObservedCache,chooseCache,Vector.getElem_ofFn]

lemma powerProgram_source (ρ : Env) (H : ℕ) (z : List Bool) (hH : ρ 0=.nat H) :
    powerProgram.eval ρ=powerValue (makeObservedCache H z) := by
  rw [powerProgram_eval ρ H hH]
  rfl

def continuationBody : Expr := .bind 1 (.get (v 58) (Expr.lit 0))
  (.bind 11 (.get (v 58) (Expr.lit 1))
    (.bind 4 (.get (v 58) (Expr.lit 2))
      (.bind 5 coreProgram Paper37.IntegerOutputProgram.outputProgram)))

def continuationProgram : Expr := .bind 2 chooseProgram
  (.bind 3 powerProgram (.bind 58 parserProgram continuationBody))

lemma continuationBody_eval (ρ : Env) (H : ℕ) (z : List Bool) (R : ℕ)
    (hH : ρ 0=.nat H) (h2 : ρ 2=chooseValue (makeObservedCache H z))
    (h3 : ρ 3=powerValue (makeObservedCache H z)) (hR : ρ 12=.nat R)
    (hs : ρ 58=.array [.nat (parseAge 0 z),.nat (parseGaps 0 z).length,
      observedValue (makeObservedCache H z)]) (hz : z.length+R≤H) :
    continuationBody.eval ρ=pairValue (evaluatePair H z R) := by
  let c:=makeObservedCache H z
  let A:=parseAge 0 z
  let r:=(parseGaps 0 z).length
  let ρA:=Function.update ρ 1 (.nat A)
  let ρr:=Function.update ρA 11 (.nat r)
  let ρa:=Function.update ρr 4 (observedValue c)
  have hcore:=coreProgram_eval c A ρa (by simpa [ρa,ρr,ρA] using hH)
    (by simp [ρa,ρr,ρA]) (by simpa [ρa,ρr,ρA,c] using h2)
    (by simpa [ρa,ρr,ρA,c] using h3) (by simp [ρa])
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
  have houtput := Paper37.IntegerOutputProgram.outputProgram_eval_inputs hout
    (by have ha:=age_le_length z;dsimp [A];omega)
  rw [Paper37.IntegerOutputProgram.outputPair_source] at houtput
  simp only [continuationBody,Expr.eval,hs]
  simp only [Function.update_of_ne (by decide : (58:ℕ)≠1),
    Function.update_of_ne (by decide : (58:ℕ)≠11),Value.arrayVal,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,hs,Value.natVal]
  change Paper37.IntegerOutputProgram.outputProgram.eval
    (Function.update ρa 5 (coreProgram.eval ρa))=_
  rw [hcore]
  exact houtput

/-- Uniform exact C.8 query: the only inputs are finite word40, horizon0 and
remaining-length12. All coefficient arrays and histograms are constructed. -/
theorem continuationProgram_eval (ρ : Env) (H : ℕ) (z : List Bool) (R : ℕ)
    (hH : ρ 0=.nat H) (hword : ρ 40=wordValue z) (hR : ρ 12=.nat R)
    (hz : z.length+R≤H) :
    continuationProgram.eval ρ=pairValue (evaluatePair H z R) := by
  have hchoose:=chooseProgram_source ρ H z hH
  let ρc:=Function.update ρ 2 (chooseValue (makeObservedCache H z))
  have hpower:=powerProgram_source ρc H z (by simpa [ρc] using hH)
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

/-- The next bit in slot46 is appended by an array loop before the actual
integer continuation program runs. Slot48 is the effective visible horizon. -/
def childProgram : Expr := .bind 12
  (.sub (v 48) (.add (.length (v 40)) (Expr.lit 1)))
  (.bind 40 appendProgram continuationProgram)

lemma childProgram_eval (ρ : Env) (H L : ℕ) (z : List Bool) (b : Bool)
    (hH : ρ 0=.nat H) (hLslot : ρ 48=.nat L) (hword : ρ 40=wordValue z)
    (hbit : ρ 46=bitValue b) (hL : L≤H) (hz : z.length<L) :
    childProgram.eval ρ=pairValue (evaluatePair H (z++[b]) (L-(z.length+1))) := by
  let R:=L-(z.length+1)
  let ρR:=Function.update ρ 12 (.nat R)
  have happend:=appendProgram_eval ρR z b (by simpa [ρR] using hword)
    (by simpa [ρR] using hbit)
  have hcont:=continuationProgram_eval (Function.update ρR 40 (wordValue (z++[b]))) H
    (z++[b]) R (by simpa [ρR] using hH) (by simp) (by simp [ρR]) (by simp;omega)
  simp only [childProgram,Expr.eval,hLslot,hword,wordValue_length,Value.natVal]
  change continuationProgram.eval (Function.update ρR 40 (appendProgram.eval ρR))=_
  rw [happend]
  exact hcont

def visibleArray : Expr := .array [.get (v 56) (Expr.lit 0),
  .add (.get (v 55) (Expr.lit 0)) (.get (v 56) (Expr.lit 0))]

def visibleProgram : Expr := .bind 46 (Expr.lit 0) (.bind 55 childProgram
  (.bind 46 (Expr.lit 1) (.bind 56 childProgram visibleArray)))

lemma visibleProgram_eval (ρ : Env) (H L : ℕ) (z : List Bool)
    (hH : ρ 0=.nat H) (hLslot : ρ 48=.nat L) (hword : ρ 40=wordValue z)
    (hL : L≤H) (hz : z.length<L) :
    visibleProgram.eval ρ=pairValue (visiblePair H L z) := by
  let p:=evaluatePair H (z++[false]) (L-(z.length+1))
  let q:=evaluatePair H (z++[true]) (L-(z.length+1))
  let ρ₀:=Function.update ρ 46 (.nat 0)
  have hfalse:=childProgram_eval ρ₀ H L z false (by simpa [ρ₀] using hH)
    (by simpa [ρ₀] using hLslot) (by simpa [ρ₀] using hword) (by rfl) hL hz
  let ρp:=Function.update ρ₀ 55 (pairValue p)
  let ρ₁:=Function.update ρp 46 (.nat 1)
  have htrue:=childProgram_eval ρ₁ H L z true (by simpa [ρ₁,ρp,ρ₀] using hH)
    (by simpa [ρ₁,ρp,ρ₀] using hLslot) (by simpa [ρ₁,ρp,ρ₀] using hword) (by rfl) hL hz
  rw [visibleProgram,Expr.eval,show (Expr.lit 0).eval ρ=Value.nat 0 by simp [Expr.eval]]
  change (Expr.bind 55 childProgram (.bind 46 (Expr.lit 1) (.bind 56 childProgram visibleArray))).eval ρ₀=_
  rw [Expr.eval,hfalse]
  change (Expr.bind 46 (Expr.lit 1) (.bind 56 childProgram visibleArray)).eval ρp=_
  rw [Expr.eval,show (Expr.lit 1).eval ρp=Value.nat 1 by simp [Expr.eval]]
  change (Expr.bind 56 childProgram visibleArray).eval ρ₁=_
  rw [Expr.eval,htrue]
  simp [visibleArray,Expr.eval,ρ₁,ρp,ρ₀,p,q,pairValue,visiblePair,Value.arrayVal,Value.natVal]

/-- The no-visible-renewal branch uses its exact source integer formula.
The other branch computes the two children of the parsed visible tail. -/
def conditionalProgram : Expr := .bind 49 (.length (v 40))
  (.bind 47 firstIndexProgram
    (.ifLT (v 47) (v 49)
      (Expr.bind 44 (.add (v 47) (Expr.lit 1)) (.bind 40 dropProgram
        (.bind 48 (.add (.sub (v 0) (v 49)) (.length (v 40))) visibleProgram)))
      (.array [Expr.lit 1,.add (.sub (v 0) (v 49)) (Expr.lit 1)])))

/-- A concrete query program computes the actual source conditional pair;
no query-semantics hypothesis remains. -/
theorem conditionalProgram_eval (ρ : Env) (H : ℕ) (y : List Bool)
    (hH : ρ 0=.nat H) (hword : ρ 40=wordValue y) (hy : y.length<H) :
    conditionalProgram.eval ρ=pairValue (conditionalPair H y) := by
  let ρlen:=Function.update ρ 49 (.nat y.length)
  have hidx:=firstIndexProgram_eval ρlen y (by simpa [ρlen] using hword)
  let ρidx:=Function.update ρlen 47 (.nat (firstIndex y))
  rw [conditionalProgram,Expr.eval]
  rw [show (Expr.length (v 40)).eval ρ=Value.nat y.length by simp [Expr.eval,hword]]
  change (Expr.bind 47 firstIndexProgram _).eval ρlen=_
  rw [Expr.eval,hidx]
  change (Expr.ifLT (v 47) (v 49) _ _).eval ρidx=_
  cases hs : Paper37.Prediction.firstSuffix y with
  | none =>
    have hi:=firstIndex_none y hs
    simp [Expr.eval,ρidx,ρlen,hi,hH,pairValue,conditionalPair,hs,Value.natVal]
  | some z =>
    obtain ⟨hlen,hdrop⟩:=firstIndex_some y z hs
    have hi : firstIndex y<y.length := by omega
    have hvis : (Expr.ifLT (v 47) (v 49)
      (Expr.bind 44 (.add (v 47) (Expr.lit 1)) (.bind 40 dropProgram
        (.bind 48 (.add (.sub (v 0) (v 49)) (.length (v 40))) visibleProgram)))
      (.array [Expr.lit 1,.add (.sub (v 0) (v 49)) (Expr.lit 1)])).eval ρidx =
      (Expr.bind 44 (.add (v 47) (Expr.lit 1)) (.bind 40 dropProgram
        (.bind 48 (.add (.sub (v 0) (v 49)) (.length (v 40))) visibleProgram))).eval ρidx := by
      simp [Expr.eval,ρidx,ρlen,hi,Value.natVal]
    rw [hvis]
    let ρd:=Function.update ρidx 44 (.nat (firstIndex y+1))
    have hdropEval:=dropProgram_eval ρd y (firstIndex y+1)
      (by simpa [ρd,ρidx,ρlen] using hword) (by simp [ρd])
    rw [hdrop] at hdropEval
    simp only [Expr.eval]
    simp only [ρidx,Function.update_self,Value.natVal]
    dsimp only [ρd,ρidx] at hdropEval
    rw [hdropEval]
    let ρz:=Function.update ρd 40 (wordValue z)
    have hL : H-y.length+z.length≤H := by omega
    have hz : z.length<H-y.length+z.length := by omega
    have hv:=visibleProgram_eval (Function.update ρz 48 (.nat (H-y.length+z.length))) H
      (H-y.length+z.length) z (by simpa [ρz,ρd,ρidx,ρlen] using hH) (by simp)
      (by simp [ρz]) hL hz
    simp only [ρz,ρd,ρidx,ρlen,Function.update_of_ne (by decide : (0:ℕ)≠40),
      Function.update_of_ne (by decide : (0:ℕ)≠44),Function.update_of_ne (by decide : (0:ℕ)≠47),
      Function.update_of_ne (by decide : (0:ℕ)≠49),
      Function.update_of_ne (by decide : (49:ℕ)≠40),Function.update_of_ne (by decide : (49:ℕ)≠44),
      Function.update_of_ne (by decide : (49:ℕ)≠47),Function.update_self,hH,Value.natVal,wordValue_length]
    change visibleProgram.eval
      (Function.update ρz 48 (.nat (H-y.length+z.length)))=_
    rw [hv]
    simp [conditionalPair,hs]

/-- One fixed finite AST for every sample size. The source sample size is
read from the input array; its horizon is computed inside the program. -/
def predictorProgram : Expr := .bind 0 (.add (.length (v 40)) (Expr.lit 1))
  (batchProgram conditionalProgram)

theorem predictorProgram_eval (ρ : Env) (x : List Bool) (hx : ρ 40=wordValue x) :
    predictorProgram.eval ρ=pairValue (predictorPair x.length x) := by
  have hq : QueryCorrect conditionalProgram (x.length+1) := fun σ y hH hword hy =>
    conditionalProgram_eval σ _ y hH hword hy
  simp only [predictorProgram,Expr.eval,hx,wordValue_length,Value.natVal]
  exact batchProgram_eval conditionalProgram x.length hq _ x rfl (by simp) (by simpa using hx)

/-- The fixed program's integer output ratio is exactly the source predictor. -/
theorem predictorProgram_source (ρ : Env) (x : List Bool) (hx : ρ 40=wordValue x) :
    let out:=predictorProgram.eval ρ
    ((out.arrayVal[0]?.getD (Value.nat 0)).natVal:ℚ) /
      (out.arrayVal[1]?.getD (Value.nat 0)).natVal=Paper37.Prediction.predict x.length x := by
  rw [predictorProgram_eval ρ x hx]
  exact predictorPair_exact x.length x rfl

end Paper37.IntegerPredictorProgram
