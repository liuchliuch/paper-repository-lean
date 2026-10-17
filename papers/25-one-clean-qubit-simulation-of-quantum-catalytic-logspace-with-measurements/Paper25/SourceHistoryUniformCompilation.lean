import Paper25.BinaryDataCompilation
import Paper25.ClockUniformCompilation
import Paper25.SimulatorParameterUniform
import Paper25.FullFilterPlacement
import Paper25.ClockCounterDescription
import Paper25.SourceUniformCompilation
import Paper25.CompilationGateBounds
import Paper25.SourceTermUniformGenerated
import Paper25.SimulatorExternalInputs

/-! Uniform description generation for the actual history and compression walk
lists. Only generic classical string, arithmetic, bit conversion and instruction
machines are inputs. The source term emitter is composed at its original source
description interface; neither a history nor a walk generator is an input. -/
noncomputable section
namespace Paper25.OperationalModel.SourceHistoryUniformCompilation
open LocalCompilation UniformCompilation
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2400000
set_option synthInstance.maxSize 512

abbrev WordContext {α : Type} (encode : α → Input) (ell : α → ℕ) :=
  elementContext encode (fun a => @List.ofFn Bit (ell a))

lemma word_pullback (classical : FLListClosure) {α : Type}
    (encode : α → Input) (ell : α → ℕ) (output : α → Input)
    (h : LogspaceComputes encode output) :
    LogspaceComputes (WordContext encode ell) (fun p => output p.1) :=
  classical.strings.compose _ encode Sigma.fst output
    (classical.strings.contextLeft _ _) h

lemma circuit_word_pullback (classical : FLListClosure) {G : EffectiveGateSet} {α : Type}
    {q : α → ℕ} (encode : α → Input) (ell : α → ℕ)
    (C : ∀ a, EffectiveCircuit G (q a)) (h : GeneratedCircuit encode C) :
    GeneratedCircuit (WordContext encode ell) (fun p => C p.1) :=
  h.pullback classical _ encode Sigma.fst C (classical.strings.contextLeft _ _)

lemma poly_const {α : Type} (encode : α → Input) (n : ℕ) :
    PolynomialBoundOn encode (fun _ => n) := ⟨n,0,by intro a; simp⟩

lemma poly_mono {α : Type} (encode : α → Input) {f g : α → ℕ}
    (h : ∀ a, f a ≤ g a) (hg : PolynomialBoundOn encode g) : PolynomialBoundOn encode f := by
  obtain ⟨C,d,hg⟩ := hg
  exact ⟨C,d,fun a => (h a).trans (hg a)⟩

lemma poly_add {α : Type} (encode : α → Input) {f g : α → ℕ}
    (hf : PolynomialBoundOn encode f) (hg : PolynomialBoundOn encode g) :
    PolynomialBoundOn encode (fun a => f a+g a) := by
  obtain ⟨C,d,hf⟩ := hf
  obtain ⟨D,e,hg⟩ := hg
  refine ⟨C+D,d+e,fun a => ?_⟩
  have hd : ((encode a).length+1)^d ≤ ((encode a).length+1)^(d+e) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have he : ((encode a).length+1)^e ≤ ((encode a).length+1)^(d+e) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  nlinarith [hf a,hg a,Nat.mul_le_mul_left C hd,Nat.mul_le_mul_left D he]

lemma poly_word {α : Type} (encode : α → Input) (ell : α → ℕ) (f : α → ℕ)
    (h : PolynomialBoundOn encode f) :
    PolynomialBoundOn (WordContext encode ell) (fun p => f p.1) := by
  obtain ⟨C,d,h⟩ := h
  refine ⟨C,d,fun p => (h p.1).trans ?_⟩
  have hl : (encode p.1).length+1 ≤ (WordContext encode ell p).length+1 := by
    simp only [WordContext,elementContext,List.length_append]
    omega
  gcongr

lemma word_value (classical : FLListClosure) (binary : BinaryDataDescription)
    {α : Type} (encode : α → Input) (ell : α → ℕ)
    (hell : LogspaceComputes encode (fun a => encodeNat (ell a)))
    (hstates : LogspaceComputes encode (fun a => encodeNat (2^(ell a)))) :
    LogspaceComputes (WordContext encode ell)
      (fun p => encodeNat (SelectedFilter.bitsBinaryIndex (ell p.1) p.2).val) :=
  word_value_generated classical binary _ (fun p => p.2)
    (word_pullback classical encode ell _ hell)
    (word_pullback classical encode ell _ hstates)
    (classical.strings.contextRight _ _)

lemma selector_value (j : Basis 3) :
    (Paper25.selectorIndex3 (uniform3Layout j)).val =
      (SelectedFilter.bitsBinaryIndex 3 j).val := by
  simp [Paper25.selectorIndex3,uniform3Layout,tensorBits,oneBit,
    SelectedFilter.bitsBinaryIndex,StatePreparation.splitBits,finProdFinEquiv]

lemma one_value (j : Basis 1) : (oneBit j).val =
    (SelectedFilter.bitsBinaryIndex 1 j).val := by
  simp [oneBit,SelectedFilter.bitsBinaryIndex,StatePreparation.splitBits,finProdFinEquiv]

lemma history_negative_indices (classical : FLListClosure)
    (arithmetic : NatArithmeticDescription) : NegativeIndexDescription := by
  constructor
  · apply placement_generated classical arithmetic encodeNat
      (fun q => placementOfEmbedding (LocalCompilation.firstWire q))
    · exact nat_add classical arithmetic encodeNat id (fun _ => 1)
        (classical.strings.identity _) (nat_const classical _ 1)
    · exact nat_const classical _ 1
    · exact poly_const _ 1
    · simpa only [active_placementOfEmbedding,LocalCompilation.firstWire] using
        nat_const classical (indexedInput encodeNat (fun _ => 1)) 0
  · exact nat_sub classical arithmetic positiveWidthInput (fun q => q.1) (fun _ => 1)
      (classical.strings.identity _) (nat_const classical _ 1)
  · apply placement_generated classical arithmetic positiveWidthInput
      (fun q => placementOfEmbedding
        (finCongr (show q.1-1+1=q.1 by have := q.2; omega)).toEmbedding)
    · exact classical.strings.identity _
    · simpa only [show ∀ q : PositiveWidth, q.1-1+1=q.1 from fun q => by have := q.2; omega]
        using classical.strings.identity positiveWidthInput
    · refine ⟨1,1,?_⟩
      intro q
      simp [positiveWidthInput,encodeNat]
      omega
    · exact indexed_counter_generated classical positiveWidthInput (fun q => q.1-1+1)

lemma identity_rewire_generated (classical : FLListClosure) (grammar : InstructionDescriptionClosure)
    (arithmetic : NatArithmeticDescription) {G : EffectiveGateSet} {α : Type}
    {q r : α → ℕ} (encode : α → Input) (e : ∀ a, Fin (q a) ≃ Fin (r a))
    (he : ∀ a i, (e a i).val=i.val) (C : ∀ a, EffectiveCircuit G (q a))
    (hq : LogspaceComputes encode (fun a => encodeNat (q a)))
    (hr : LogspaceComputes encode (fun a => encodeNat (r a)))
    (hpoly : PolynomialBoundOn encode q) (hC : GeneratedCircuit encode C) :
    GeneratedCircuit encode (fun a => rewireCircuit (e a) (C a)) := by
  apply rewire_generated classical grammar encode e C ?_ hC
  apply placement_generated classical arithmetic encode _ hr hq hpoly
  have hh : ∀ a i, (active (placementOfEmbedding (e a).toEmbedding) i).val=i.val := by
    intro a i
    simpa only [active_placementOfEmbedding] using he a i
  simpa only [hh] using indexed_counter_generated classical encode q

lemma selectorPrepare_generated (classical : FLListClosure) (grammar : InstructionDescriptionClosure)
    {G : EffectiveGateSet} (conv : GateConvention G) {α : Type}
    (encode : α → Input) (q : α → ℕ)
    (hq : LogspaceComputes encode (fun a => encodeNat (q a))) :
    GeneratedCircuit encode (fun a => selectorPrepareCircuit conv (q a)) :=
  tensorCircuit_generated classical grammar encode (fun _ => uniform3Circuit conv)
    (fun a => ([] : EffectiveCircuit G (q a))) (constant_generated classical encode _)
    (nil_generated classical encode q) (nat_const classical encode 3) hq

lemma sourceLCU_generated (classical : FLListClosure) (grammar : InstructionDescriptionClosure)
    {G : EffectiveGateSet} {conv : GateConvention G} (primitive : PrimitiveDescriptionConvention conv)
    {α : Type} {q : α → ℕ} (encode : α → Input)
    (K : ∀ a, Fin 8 → EffectiveCircuit G (q a))
    (hq : LogspaceComputes encode (fun a => encodeNat (q a)))
    (hK : GeneratedCircuit (WordContext encode (fun _ => 3))
      (fun p => K p.1 (Paper25.selectorIndex3 (uniform3Layout p.2)))) :
    GeneratedCircuit encode (fun a => sourceLCUCircuit conv (K a)) := by
  apply coherentFilterCircuit_generated classical primitive encode _ _
    (selectorPrepare_generated classical grammar conv encode q hq)
  exact selectCircuit_generated classical primitive encode _
    (classical.strings.constant encode (encodeNat 3++encodeNat 8))
    (nat_const classical encode 8) hK

lemma weightedDifference_generated (classical : FLListClosure) (grammar : InstructionDescriptionClosure)
    (arithmetic : NatArithmeticDescription) (binary : BinaryDataDescription)
    {G : EffectiveGateSet} {conv : GateConvention G} (primitive : PrimitiveDescriptionConvention conv)
    {α : Type} {q : α → ℕ} (encode : α → Input)
    (prepare : α → EffectiveCircuit G 1) (C negative : ∀ a, EffectiveCircuit G (q a))
    (hq : LogspaceComputes encode (fun a => encodeNat (q a)))
    (hp : GeneratedCircuit encode prepare) (hC : GeneratedCircuit encode C)
    (hn : GeneratedCircuit encode negative) :
    GeneratedCircuit encode (fun a => weightedDifferenceCircuit conv (prepare a) (C a) (negative a)) := by
  have hprep := tensorCircuit_generated classical grammar encode prepare
    (fun a => ([] : EffectiveCircuit G (q a))) hp (nil_generated classical encode q)
    (nat_const classical encode 1) hq
  have hvalue := word_value classical binary encode (fun _ => 1)
    (nat_const classical encode 1) (nat_const classical encode 2)
  have hz := nat_eq classical arithmetic (WordContext encode (fun _ => 1))
    (fun p => (oneBit p.2).val) (fun _ => 0)
    (by simpa only [one_value] using hvalue) (nat_const classical _ 0)
  have hbranches : GeneratedCircuit (WordContext encode (fun _ => 1))
      (fun p => differenceBranches (C p.1) (negative p.1) p.2) := by
    have h := conditional_generated classical (WordContext encode (fun _ => 1))
      (fun p => decide ((oneBit p.2).val=0))
      (fun p => ([] : EffectiveCircuit G (q p.1)))
      (fun p => C p.1++negative p.1) hz (nil_generated classical _ _)
      (append_generated classical _ _ _
        (circuit_word_pullback classical encode (fun _ => 1) C hC)
        (circuit_word_pullback classical encode (fun _ => 1) negative hn))
    simpa only [differenceBranches,decide_eq_true_eq,Fin.ext_iff,Fin.val_zero] using h
  exact coherentFilterCircuit_generated classical primitive encode _ _ hprep
    (selectCircuit_generated classical primitive encode _
      (classical.strings.constant encode (encodeNat 1++encodeNat 2))
      (nat_const classical encode 2) hbranches)

lemma swapPrefix_value (a b c : ℕ) (i : Fin (a+(b+c))) :
    (swapPrefix a b c i).val =
      if i.val<a then b+i.val else if i.val<a+b then i.val-a else i.val := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [swapPrefix,j.isLt]
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simp [swapPrefix]
    · simp [swapPrefix]
      omega

lemma swapPrefix_generated (classical : FLListClosure) (grammar : InstructionDescriptionClosure)
    (arithmetic : NatArithmeticDescription) {G : EffectiveGateSet} {α : Type}
    (encode : α → Input) (a b c : α → ℕ)
    (C : ∀ x, EffectiveCircuit G (a x+(b x+c x)))
    (ha : LogspaceComputes encode (fun x => encodeNat (a x)))
    (hb : LogspaceComputes encode (fun x => encodeNat (b x)))
    (hc : LogspaceComputes encode (fun x => encodeNat (c x)))
    (hpoly : PolynomialBoundOn encode (fun x => a x+(b x+c x)))
    (hC : GeneratedCircuit encode C) :
    GeneratedCircuit encode (fun x => rewireCircuit (swapPrefix (a x) (b x) (c x)) (C x)) := by
  have hbc := nat_add classical arithmetic encode b c hb hc
  have hq := nat_add classical arithmetic encode a _ ha hbc
  have hac := nat_add classical arithmetic encode a c ha hc
  have hr := nat_add classical arithmetic encode b _ hb hac
  apply rewire_generated classical grammar encode _ C ?_ hC
  apply placement_generated classical arithmetic encode _ hr hq hpoly
  let ctx := indexedInput encode (fun x => a x+(b x+c x))
  have hleft := indexed_input_generated classical encode (fun x => a x+(b x+c x))
  have ha' := classical.strings.compose ctx encode Sigma.fst _ hleft ha
  have hb' := classical.strings.compose ctx encode Sigma.fst _ hleft hb
  have hi := indexed_counter_generated classical encode (fun x => a x+(b x+c x))
  have hab' := nat_add classical arithmetic ctx (fun p => a p.1) (fun p => b p.1) ha' hb'
  have hinner := nat_if classical ctx (fun p => decide (p.2.val<a p.1+b p.1))
    (fun p => p.2.val-a p.1) (fun p => p.2.val)
    (nat_lt classical arithmetic ctx _ _ hi hab')
    (nat_sub classical arithmetic ctx _ _ hi ha') hi
  have hf := nat_if classical ctx (fun p => decide (p.2.val<a p.1))
    (fun p => b p.1+p.2.val)
    (fun p => if p.2.val<a p.1+b p.1 then p.2.val-a p.1 else p.2.val)
    (nat_lt classical arithmetic ctx _ _ hi ha')
    (nat_add classical arithmetic ctx _ _ hb' hi)
    (by simpa only [decide_eq_true_eq] using hinner)
  simpa only [active_placementOfEmbedding,Equiv.toEmbedding_apply,swapPrefix_value,
    decide_eq_true_eq] using hf

lemma nativeHistory_generated (classical : FLListClosure) (grammar : InstructionDescriptionClosure)
    (arithmetic : NatArithmeticDescription) (binary : BinaryDataDescription)
    {G : EffectiveGateSet} {conv : GateConvention G} (primitive : PrimitiveDescriptionConvention conv)
    (clockIndices : ClockIndexDescription) {α : Type} (encode : α → Input) (q ell T : α → ℕ)
    (hqpos : ∀ a, 0<q a) (K : ∀ a, ℕ → Fin 8 → EffectiveCircuit G (q a))
    (prepare : α → EffectiveCircuit G 1)
    (hq : LogspaceComputes encode (fun a => encodeNat (q a)))
    (hell : LogspaceComputes encode (fun a => encodeNat (ell a)))
    (hstates : LogspaceComputes encode (fun a => encodeNat (2^(ell a))))
    (hT : LogspaceComputes encode (fun a => encodeNat (T a)))
    (qpoly : PolynomialBoundOn encode q) (ellpoly : PolynomialBoundOn encode ell)
    (hp : GeneratedCircuit encode prepare)
    (hK : GeneratedCircuit (WordContext (WordContext encode ell) (fun _ => 3))
      (fun p => K p.1.1 (SelectedFilter.clockIndex (ell p.1.1) p.1.2).val
        (Paper25.selectorIndex3 (uniform3Layout p.2)))) :
    GeneratedCircuit encode (fun a => nativeHistoryACircuit conv (hqpos a)
      (T a) (ell a) (K a) (prepare a)) := by
  let negative (a : α) := negativeOn conv (q a) (hqpos a)
  have indices := history_negative_indices classical arithmetic
  have hn := negativeOn_generated classical grammar primitive indices encode q hqpos hq
  let clockCtx := WordContext encode ell
  let termCtx := WordContext clockCtx (fun _ => 3)
  have hqclock := word_pullback classical encode ell _ hq
  have hnegclock := circuit_word_pullback classical encode ell negative hn
  have hclock : LogspaceComputes clockCtx
      (fun p => encodeNat (SelectedFilter.clockIndex (ell p.1) p.2).val) :=
    word_value classical binary encode ell hell hstates
  have hactive := nat_lt classical arithmetic clockCtx
    (fun p => (SelectedFilter.clockIndex (ell p.1) p.2).val) (fun p => T p.1)
    hclock (word_pullback classical encode ell _ hT)
  have hselector := word_value classical binary clockCtx (fun _ => 3)
    (nat_const classical clockCtx 3) (nat_const classical clockCtx 8)
  have hfirst := nat_lt classical arithmetic termCtx
    (fun p => (Paper25.selectorIndex3 (uniform3Layout p.2)).val) (fun _ => 4)
    (by simpa only [selector_value] using hselector) (nat_const classical termCtx 4)
  have hinactive : GeneratedCircuit termCtx
      (fun p => inactiveCircuits (negative p.1.1) (Paper25.selectorIndex3 (uniform3Layout p.2))) := by
    have hh := conditional_generated classical termCtx
      (fun p => decide ((Paper25.selectorIndex3 (uniform3Layout p.2)).val<4))
      (fun p => ([] : EffectiveCircuit G (q p.1.1))) (fun p => negative p.1.1)
      hfirst (nil_generated classical termCtx _) (circuit_word_pullback classical clockCtx
        (fun _ => 3) (fun p => negative p.1) hnegclock)
    simpa only [inactiveCircuits,decide_eq_true_eq] using hh
  have hchoose := conditional_generated classical termCtx
    (fun p => decide ((SelectedFilter.clockIndex (ell p.1.1) p.1.2).val<T p.1.1))
    (fun p => K p.1.1 (SelectedFilter.clockIndex (ell p.1.1) p.1.2).val
      (Paper25.selectorIndex3 (uniform3Layout p.2)))
    (fun p => inactiveCircuits (negative p.1.1) (Paper25.selectorIndex3 (uniform3Layout p.2)))
    (word_pullback classical clockCtx (fun _ => 3) _ hactive) hK hinactive
  have hbranch : GeneratedCircuit clockCtx (fun p => clockBranchCircuit conv (T p.1)
      (SelectedFilter.clockIndex (ell p.1)) (negative p.1) (K p.1) p.2) := by
    apply sourceLCU_generated classical grammar primitive clockCtx _ hqclock
    simpa only [clockBranchCircuit,ite_apply,decide_eq_true_eq] using hchoose
  have hselect := selectCircuit_generated classical primitive encode
    (fun a => clockBranchCircuit conv (T a) (SelectedFilter.clockIndex (ell a))
      (negative a) (K a))
    (classical.strings.concat encode _ _ hell hstates) hstates hbranch
  have hinc := increment_generated classical grammar primitive clockIndices encode ell hell hstates ellpoly
  have hthreeq := nat_add classical arithmetic encode (fun _ => 3) q (nat_const classical encode 3) hq
  have hincExt := tensorCircuit_generated classical grammar encode
    (fun a => ClockCompilation.increment conv (ell a))
    (fun a => ([] : EffectiveCircuit G (3+q a))) hinc (nil_generated classical encode _)
    hell hthreeq
  have hraw := append_generated classical encode _ _ hselect hincExt
  have hqraw := poly_add encode ellpoly (poly_add encode (poly_const encode 3) qpoly)
  have hhist := swapPrefix_generated classical grammar arithmetic encode ell (fun _ => 3) q
    (fun a => rawHistoryCircuit conv (T a) (SelectedFilter.clockIndex (ell a))
      (negative a) (K a) (ClockCompilation.increment conv (ell a)))
    hell (nat_const classical encode 3) hq hqraw hraw
  have hellq := nat_add classical arithmetic encode ell q hell hq
  have hhistWidth := nat_add classical arithmetic encode (fun _ => 3) _
    (nat_const classical encode 3) hellq
  have hnegativeHist := negativeOn_generated classical grammar primitive indices encode
    (fun a => 3+(ell a+q a)) (show ∀ a : α, 0<3+(ell a+q a) from by intro a; omega) hhistWidth
  exact weightedDifference_generated classical grammar arithmetic binary primitive encode
    prepare _ _ hhistWidth hp hhist hnegativeHist

lemma dilation_generated (classical : FLListClosure) (grammar : InstructionDescriptionClosure)
    (arithmetic : NatArithmeticDescription) {G : EffectiveGateSet} {conv : GateConvention G}
    (primitive : PrimitiveDescriptionConvention conv) {α : Type} {q : α → ℕ}
    (encode : α → Input) (C : ∀ a, EffectiveCircuit G (q a))
    (hq : LogspaceComputes encode (fun a => encodeNat (q a)))
    (hC : GeneratedCircuit encode C) :
    GeneratedCircuit encode (fun a => dilationCircuit conv (C a)) := by
  have hx := flipCircuit_generated classical grammar (conv := conv)
    (history_negative_indices classical arithmetic) encode q hq
  have ha := controlledCircuit_generated classical primitive encode _
    (adjointCircuit_generated classical primitive encode C hC)
  have hc := controlledCircuit_generated classical primitive encode C hC
  exact append_generated classical encode _ _
    (append_generated classical encode _ _
      (append_generated classical encode _ _ (append_generated classical encode _ _ hx ha) hx) hc) hx

lemma data_generated (classical : FLListClosure) (grammar : InstructionDescriptionClosure)
    (arithmetic : NatArithmeticDescription) {G : EffectiveGateSet} {α : Type} {q : α → ℕ}
    (encode : α → Input) (C : ∀ a, EffectiveCircuit G (q a))
    (hq : LogspaceComputes encode (fun a => encodeNat (q a)))
    (qpoly : PolynomialBoundOn encode q) (hC : GeneratedCircuit encode C) :
    GeneratedCircuit encode (fun a => dataCircuit (C a)) := by
  apply embedCircuit_generated classical grammar encode _ C ?_ hC
  apply placement_generated classical arithmetic encode _
    (nat_add classical arithmetic encode q (fun _ => 1) hq (nat_const classical encode 1)) hq qpoly
  simpa only [active_placementOfEmbedding,dataWires,Fin.val_succ] using
    nat_add classical arithmetic (indexedInput encode q) (fun p => p.2.val) (fun _ => 1)
      (indexed_counter_generated classical encode q) (nat_const classical _ 1)

lemma word_zero_iff (ell : ℕ) (j : Basis ell) :
    (SelectedFilter.bitsBinaryIndex ell j).val=0 ↔ j=(fun _ => 0) := by
  have hz := SelectedFilter.bitsBinaryIndex_zero ell
  constructor
  · intro h
    apply (SelectedFilter.bitsBinaryIndex ell).injective
    exact (Fin.ext h).trans hz.symm
  · intro h
    simpa only [h] using congrArg Fin.val hz

lemma zeroReflection4_generated (classical : FLListClosure)
    (arithmetic : NatArithmeticDescription) (binary : BinaryDataDescription)
    (grammar : InstructionDescriptionClosure) {G : EffectiveGateSet} {conv : GateConvention G}
    (primitive : PrimitiveDescriptionConvention conv) {α : Type} (encode : α → Input)
    (q : α → ℕ) (hq : LogspaceComputes encode (fun a => encodeNat (q a))) :
    GeneratedCircuit encode (fun a => zeroReflectionCircuit conv 4 (q a)) := by
  let ctx := WordContext encode (fun _ => 4)
  have hv := word_value classical binary encode (fun _ => 4)
    (nat_const classical encode 4) (nat_const classical encode 16)
  have hz := nat_eq classical arithmetic ctx
    (fun p => (SelectedFilter.bitsBinaryIndex 4 p.2).val) (fun _ => 0) hv (nat_const classical ctx 0)
  have hn := negativeCircuit_generated classical grammar primitive
    (history_negative_indices classical arithmetic) encode q hq
  have hbranches := conditional_generated classical ctx (fun p => decide (p.2=(fun _ => 0)))
    (fun p => ([] : EffectiveCircuit G (q p.1+1)))
    (fun p => negativeCircuit conv (q p.1))
    (by simpa only [word_zero_iff] using hz) (nil_generated classical ctx _)
    (circuit_word_pullback classical encode (fun _ => 4) _ hn)
  exact selectCircuit_generated classical primitive encode _
    (classical.strings.constant encode (encodeNat 4++encodeNat 16))
    (nat_const classical encode 16) (by simpa only [decide_eq_true_eq] using hbranches)

lemma sourceWalk_of_history_generated (classical : FLListClosure)
    (grammar : InstructionDescriptionClosure) (arithmetic : NatArithmeticDescription)
    (binary : BinaryDataDescription) {G : EffectiveGateSet} {conv : GateConvention G}
    (primitive : PrimitiveDescriptionConvention conv) {α : Type} (encode : α → Input)
    (S : α → EffectiveSourceComputation G) (ell : α → ℕ)
    (prepare : α → EffectiveCircuit G 1)
    (hd : LogspaceComputes encode (fun a => encodeNat (SourceHistoryCompilation.DataQubits (S a))))
    (hell : LogspaceComputes encode (fun a => encodeNat (ell a)))
    (dpoly : PolynomialBoundOn encode (fun a => SourceHistoryCompilation.DataQubits (S a)))
    (ellpoly : PolynomialBoundOn encode ell)
    (hA : GeneratedCircuit encode (fun a => SourceHistoryCompilation.circuit conv (S a) (ell a) (prepare a))) :
    GeneratedCircuit encode (fun a => FullFilterPlacement.nativeWalk conv (S a) (ell a) (prepare a)) := by
  let d (a : α) := SourceHistoryCompilation.DataQubits (S a)
  have hr := nat_add classical arithmetic encode ell d hell hd
  have h4r := nat_add classical arithmetic encode (fun _ => 4) _ (nat_const classical encode 4) hr
  have h3r := nat_add classical arithmetic encode (fun _ => 3) _ (nat_const classical encode 3) hr
  have h1_3r := nat_add classical arithmetic encode (fun _ => 1) _ (nat_const classical encode 1) h3r
  have rpoly := poly_add encode ellpoly dpoly
  have ePoly := poly_add encode (poly_const encode 4) rpoly
  have oldPoly := poly_add encode (poly_const encode 1) (poly_add encode (poly_const encode 3) rpoly)
  have hencoder := identity_rewire_generated classical grammar arithmetic encode
    (fun a => SourceWalkCompilation.prefixWire (S a) (ell a)) (by intro a i; rfl)
    _ h1_3r h4r oldPoly hA
  have hrminus := nat_sub classical arithmetic encode (fun a => ell a+d a) (fun _ => 1)
    hr (nat_const classical encode 1)
  have hreflection := zeroReflection4_generated classical arithmetic binary grammar primitive encode _ hrminus
  have hrminusOne := nat_add classical arithmetic encode (fun a => ell a+d a-1) (fun _ => 1)
    hrminus (nat_const classical encode 1)
  have hReflectionWidth := nat_add classical arithmetic encode (fun _ => 4) _
    (nat_const classical encode 4) hrminusOne
  have hrefPoly : PolynomialBoundOn encode (fun a => 4+((ell a+d a-1)+1)) :=
    poly_mono encode (fun a => by have h := SourceHistoryCompilation.dataQubits_pos (S a); dsimp [d]; omega) ePoly
  have href := identity_rewire_generated classical grammar arithmetic encode
    (fun a => finCongr (show 4+((ell a+SourceHistoryCompilation.DataQubits (S a)-1)+1)=
      4+(ell a+SourceHistoryCompilation.DataQubits (S a)) by
      have h := SourceHistoryCompilation.dataQubits_pos (S a); omega))
    (by intro a i; rfl) _ hReflectionWidth h4r hrefPoly hreflection
  have hdata := data_generated classical grammar arithmetic encode _ h4r ePoly href
  have hdilation := dilation_generated classical grammar arithmetic primitive encode _ h4r hencoder
  have hwalk := append_generated classical encode _ _ hdilation hdata
  have hwalkWidth := nat_add classical arithmetic encode (fun a => 4+(ell a+d a)) (fun _ => 1)
    h4r (nat_const classical encode 1)
  have hwalkPoly := poly_add encode ePoly (poly_const encode 1)
  have h := identity_rewire_generated classical grammar arithmetic encode
    (fun a => FullFilterPlacement.walkWire (S a) (ell a)) (by intro a i; rfl)
    (fun a => SourceWalkCompilation.circuit conv (S a) (ell a) (prepare a))
    hwalkWidth (by
      convert hwalkWidth using 1
      funext a
      congr 1
      dsimp [d,SourcePreparationPlacement.walkQubits,SourcePreparationPlacement.encoderQubits,
        SourceHistoryCompilation.DataQubits]
      omega) hwalkPoly hwalk
  exact h

/-- Original source bytes and two explicit unary counters are the only query
sent to the source-term emitter, including the inactive padded times. -/
lemma source_term_queries (classical : FLListClosure) (numeric : ClassicalDescriptionClosure)
    (binary : BinaryDataDescription) {G : EffectiveGateSet} (F : EffectiveSourceFamily G)
    (P : SimulatorParameterUniform.ParameterComputations F) :
    LogspaceComputes
      (WordContext (WordContext id (fun x => SourceCircuitSimulation.clockBits (F.circuit x))) (fun _ => 3))
      (fun p => sourceTermInput (⟨F.circuit p.1.1,
        (SelectedFilter.clockIndex (SourceCircuitSimulation.clockBits (F.circuit p.1.1)) p.1.2).val,
        Paper25.selectorIndex3 (uniform3Layout p.2)⟩ : SourceTermRequest G)) := by
  let ell (x : Input) := SourceCircuitSimulation.clockBits (F.circuit x)
  let clockCtx := WordContext id ell
  let termCtx := WordContext clockCtx (fun _ => 3)
  have hs := word_pullback classical clockCtx (fun _ => 3) _
    (word_pullback classical id ell _ F.uniform)
  have hstates : LogspaceComputes id (fun x => encodeNat (2^ell x)) := by
    simpa only [ell,SourceCircuitSimulation.clockBits,SimulationParameters.clockBits,
      clockSize,powerTwoCeil] using P.J
  have hc : LogspaceComputes termCtx (fun p => encodeNat
      (SelectedFilter.clockIndex (ell p.1.1) p.1.2).val) :=
    word_pullback classical clockCtx (fun _ => 3) _
      (word_value classical binary id ell P.ell hstates)
  have hj : LogspaceComputes termCtx (fun p => encodeNat
      (Paper25.selectorIndex3 (uniform3Layout p.2)).val) := by
    simpa only [selector_value] using word_value classical binary clockCtx (fun _ => 3)
      (nat_const classical clockCtx 3) (nat_const classical clockCtx 8)
  exact numeric.pair termCtx _ _ hs (classical.strings.concat termCtx _ _ hc hj)

/-- The history and walk generators are derived from individual source-term
queries. This component lemma is discharged by the original source parser in
`source_nativeWalk_generated`; it assumes no history/walk implementation. -/
theorem source_nativeWalk_generated_of_terms {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (classical : FLListClosure) (numeric : ClassicalDescriptionClosure)
    (grammar : InstructionDescriptionClosure) (primitive : PrimitiveDescriptionConvention conv)
    (arithmetic : NatArithmeticDescription) (binary : BinaryDataDescription)
    (prefixParsing : UnaryPrefixParsing) (parsing : SourceDescriptionParsing G)
    (F : EffectiveSourceFamily G) (P : SimulatorParameterUniform.ParameterComputations F)
    (hTerms : GeneratedCircuit (sourceTermInput (G := G))
      (fun r => SourceTermCompilation.canonicalNativeTerm conv r.1 r.2.1 r.2.2)) :
    GeneratedCircuit id (fun x => FullFilterPlacement.nativeWalk conv (F.circuit x)
      (SourceCircuitSimulation.clockBits (F.circuit x))
      (conv.rotationRep (selectorAngle E (FullPrecisionBudget.sourcePrecision (F.circuit x))))) := by
  let ell (x : Input) := SourceCircuitSimulation.clockBits (F.circuit x)
  let data (x : Input) := SourceHistoryCompilation.DataQubits (F.circuit x)
  have hq := source_qubits_generated classical arithmetic parsing F
  have hd : LogspaceComputes id (fun x => encodeNat (data x)) :=
    nat_add classical arithmetic id _ _ hq hq
  have hqPoly : PolynomialBound (fun x => SourceTermCompilation.sourceQubits (F.circuit x)) :=
    ((logarithmic_work_dimension F.work_logarithmic).mono
      (fun x => Paper25.nat_le_two_pow (F.circuit x).workQubits)).add F.catalyst_polynomial
  have hdPoly : PolynomialBoundOn id data := hqPoly.add hqPoly
  have hstatesPoly : PolynomialBoundOn id (fun x => 2^ell x) :=
    FullCompilationResources.sourceClock_dimension_polynomial F
  have hellPoly : PolynomialBoundOn id ell :=
    poly_mono id (fun x => Paper25.nat_le_two_pow (ell x)) hstatesPoly
  have hstates : LogspaceComputes id (fun x => encodeNat (2^ell x)) := by
    simpa only [ell,SourceCircuitSimulation.clockBits,SimulationParameters.clockBits,
      clockSize,powerTwoCeil] using P.J
  let clockCtx := WordContext id ell
  let termCtx := WordContext clockCtx (fun _ => 3)
  have hK : GeneratedCircuit termCtx (fun p => SourceTermCompilation.canonicalNativeTerm conv
      (F.circuit p.1.1) (SelectedFilter.clockIndex (ell p.1.1) p.1.2).val
      (Paper25.selectorIndex3 (uniform3Layout p.2))) :=
    hTerms.pullback classical termCtx (sourceTermInput (G := G))
      (fun p => ⟨F.circuit p.1.1,(SelectedFilter.clockIndex (ell p.1.1) p.1.2).val,
        Paper25.selectorIndex3 (uniform3Layout p.2)⟩) _
      (source_term_queries classical numeric binary F P)
  have hp := rotationRep_generated classical primitive id _
    (selectorAngle_computes E numeric id _ P.p)
  have hA := nativeHistory_generated classical grammar arithmetic binary primitive
    (clockIndex_of_arithmetic classical arithmetic prefixParsing) id data ell
    (fun x => (SourceCoordinates.expanded (F.circuit x)).length)
    (fun x => SourceHistoryCompilation.dataQubits_pos (F.circuit x))
    (fun x => SourceTermCompilation.canonicalNativeTerm conv (F.circuit x))
    (fun x => conv.rotationRep (selectorAngle E (FullPrecisionBudget.sourcePrecision (F.circuit x))))
    hd P.ell hstates P.duration hdPoly hellPoly hp hK
  exact sourceWalk_of_history_generated classical grammar arithmetic binary primitive id F.circuit ell _
    hd P.ell hdPoly hellPoly hA

/-- The actual complete native walk is logspace generated from the original
source circuit family. Every paper-specific constructor and lookup is proved
above or in the source-term compiler; external fields are generic classical
machines and the original primitive gate-description convention only. -/
theorem source_nativeWalk_generated {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (external : Paper25.ClassicalSimulationInputs G)
    (primitive : PrimitiveDescriptionConvention conv) (F : EffectiveSourceFamily G)
    (P : SimulatorParameterUniform.ParameterComputations F) :
    GeneratedCircuit id (fun x => FullFilterPlacement.nativeWalk conv (F.circuit x)
      (SourceCircuitSimulation.clockBits (F.circuit x))
      (conv.rotationRep (selectorAngle E (FullPrecisionBudget.sourcePrecision (F.circuit x))))) := by
  exact source_nativeWalk_generated_of_terms conv E external.lists external.rational
    external.instructions primitive external.arithmetic external.binary external.unaryPrefix external.source F P
    (canonicalNativeTerm_generated external.lists external.rational external.instructions
      external.arithmetic external.queries external.unaryPrefix external.vectors primitive
      external.source external.sourceOperations)

end Paper25.OperationalModel.SourceHistoryUniformCompilation
