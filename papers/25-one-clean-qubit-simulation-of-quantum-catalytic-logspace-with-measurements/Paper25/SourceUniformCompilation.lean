import Paper25.ClassicalDataCompilation
import Paper25.SourceTermCompilation
import Paper25.ClockUniformCompilation

/-! Source-operation descriptions are parsed as data. Measurement macro
expansion is an own three-member list construction. The native eight-term
circuits are then built from the already proved concrete local templates. -/
noncomputable section
namespace Paper25.OperationalModel.UniformCompilation
open LocalCompilation SourceTermCompilation
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000

inductive SourceView (G : EffectiveGateSet) (q : ℕ) where
  | gate (g : EffectiveLocalGate G q)
  | dephase (p : Placement q 1)
  | reset (p : Placement q 1)
  | outcomeReset (p : Placement q 2)
  | copyBasis (p : Placement q 2)
  | outcomeDephase (p : Placement q 2)
  | padding

def SourceView.tag {G : EffectiveGateSet} {q : ℕ} : SourceView G q → Fin 7
  | .gate _ => 0 | .dephase _ => 1 | .reset _ => 2
  | .outcomeReset _ => 3 | .copyBasis _ => 4 | .outcomeDephase _ => 5 | .padding => 6

def SourceView.encode {G : EffectiveGateSet} {q : ℕ} : SourceView G q → Input
  | .gate g => encodeNat 0 ++ g.encode
  | .dephase p => encodeNat 1 ++ p.encode
  | .reset p => encodeNat 2 ++ p.encode
  | .outcomeReset p => encodeNat 3 ++ p.encode
  | .copyBasis p => encodeNat 4 ++ p.encode
  | .outcomeDephase p => encodeNat 5 ++ p.encode
  | .padding => encodeNat 6 ++ encodeNat q

def SourceView.payload {G : EffectiveGateSet} {q : ℕ} : SourceView G q → Input
  | .gate g => g.encode | .dephase p => p.encode | .reset p => p.encode
  | .outcomeReset p => p.encode | .copyBasis p => p.encode | .outcomeDephase p => p.encode
  | .padding => encodeNat q

lemma SourceView.encode_eq {G : EffectiveGateSet} {q : ℕ} (v : SourceView G q) :
    v.encode = encodeNat v.tag.val ++ v.payload := by cases v <;> rfl

abbrev ViewTermRequest (G : EffectiveGateSet) :=
  Σ q : PositiveWidth, SourceView G q.val × Fin 8

def viewTermInput {G : EffectiveGateSet} (r : ViewTermRequest G) : Input :=
  encodeNat r.1.val ++ encodeNat r.2.2.val ++ r.2.1.encode

abbrev SourceTermRequest (G : EffectiveGateSet) :=
  Σ S : EffectiveSourceComputation G, ℕ × Fin 8

def sourceTermInput {G : EffectiveGateSet} (r : SourceTermRequest G) : Input :=
  elementContext EffectiveSourceComputation.encode
    (fun _ (p : ℕ × Fin 8) => encodeNat p.1 ++ encodeNat p.2.val) r

def expandView {G : EffectiveGateSet} {q : ℕ} : EffectiveSourceOp G q → List (SourceView G q)
  | .gate g => [.gate g]
  | .dephase p => [.dephase p]
  | .reset p => [.reset p]
  | .measurement p => [.outcomeReset p,.copyBasis p,.outcomeDephase p]

def expandedViews {G : EffectiveGateSet} {q : ℕ} (C : EffectiveSourceCircuit G q) : List (SourceView G q) :=
  C.flatMap expandView

def viewAt {G : EffectiveGateSet} {q : ℕ} (C : EffectiveSourceCircuit G q) (t : ℕ) : SourceView G q :=
  (expandedViews C)[t]?.getD .padding

def termViewRequest {G : EffectiveGateSet} (r : SourceTermRequest G) : ViewTermRequest G :=
  ⟨⟨sourceQubits r.1,sourceQubits_pos r.1⟩,viewAt r.1.gates r.2.1,r.2.2⟩

def viewTerm {G : EffectiveGateSet} (conv : GateConvention G) {q : ℕ} (hq : 0<q)
    (v : SourceView G q) (j : Fin 8) : EffectiveCircuit G (q+q) :=
  match v with
  | .gate g => unitaryTermCircuit conv hq [g] j
  | .dephase p => dephasePlacedCircuit conv p j
  | .reset p => resetPlacedCircuit conv p j
  | .outcomeReset p => outcomeResetCircuit conv p j
  | .copyBasis p => copyPlacedCircuit conv p j
  | .outcomeDephase p => outcomeDephaseCircuit conv p j
  | .padding => unitaryTermCircuit conv hq [] j

lemma expandedViews_terms {G : EffectiveGateSet} (conv : GateConvention G) {q : ℕ} (hq : 0<q)
    (C : EffectiveSourceCircuit G q) (j : Fin 8) :
    (expandNativeCircuit conv hq C).map (fun p => p.terms j) =
      (expandedViews C).map (fun v => viewTerm conv hq v j) := by
  induction C with
  | nil => rfl
  | cons op ops ih =>
    simp only [expandNativeCircuit, expandedViews, List.flatMap_cons, List.map_append] at *
    rw [ih]
    congr 1
    cases op <;> rfl

lemma nativeTermAt_eq_view {G : EffectiveGateSet} (conv : GateConvention G) {q : ℕ} (hq : 0<q)
    (C : EffectiveSourceCircuit G q) (t : ℕ) (j : Fin 8) :
    nativeTermAt conv hq C t j = viewTerm conv hq (viewAt C t) j := by
  have h := congrArg (fun xs : List (EffectiveCircuit G (q+q)) => xs[t]?)
    (expandedViews_terms conv hq C j)
  simp only [List.getElem?_map] at h
  unfold nativeTermAt viewAt
  cases hn : (expandNativeCircuit conv hq C)[t]? <;>
    cases hv : (expandedViews C)[t]? <;> simp only [hn,hv,Option.map_none,Option.map_some] at h ⊢
  · rfl
  · contradiction
  · contradiction
  · exact Option.some.inj h

lemma prefixLists_generated (classical : FLListClosure) {α : Type} (encode : α → Input)
    (prefixes : List ℕ) (payload : α → Input) (hp : LogspaceComputes encode payload) :
    LogspaceComputes encode (fun a => delimitedList id (prefixes.map (fun k => encodeNat k ++ payload a))) := by
  induction prefixes with
  | nil => exact classical.strings.constant encode (encodeNat 0)
  | cons k ks ih =>
    have hhead := classical.strings.concat encode _ _ (nat_const classical encode k) hp
    have hsingle := classical.singleton encode (fun _ (b : Input) => b)
      (fun a => encodeNat k ++ payload a) hhead
    simpa only [List.map_cons] using classical.append encode (fun _ (b : Input) => b)
      (fun a => [encodeNat k ++ payload a]) (fun a => ks.map (fun k => encodeNat k ++ payload a))
      hsingle ih

lemma expandView_generated (classical : FLListClosure) (queries : FLDataQueryDescription)
    {G : EffectiveGateSet} (parsing : SourceOperationParsing G) :
    LogspaceComputes (sourceOperationInput (G := G))
      (fun r => delimitedList SourceView.encode (expandView r.2)) := by
  apply queries.finiteCases sourceOperationInput operationTag _ parsing.tag
  intro i
  fin_cases i
  · let enc := fun r : {r : SourceOperation G // operationTag r = 0} => sourceOperationInput r.val
    have hp := classical.strings.compose enc sourceOperationInput Subtype.val _
      (classical.strings.identity enc) parsing.nativeBytes
    have h := prefixLists_generated classical enc [0] (fun r => operationNativeBytes r.val) hp
    have he : (fun r : {r : SourceOperation G // operationTag r = 0} =>
        delimitedList SourceView.encode (expandView r.val.2)) =
        (fun r => delimitedList id ([0].map (fun k => encodeNat k ++ operationNativeBytes r.val))) := by
      funext r
      rcases r with ⟨⟨q,op⟩,hr⟩
      cases op <;> simp [operationTag] at hr
      rfl
    exact Eq.mpr (congrArg (LogspaceComputes enc) he) h
  · let enc := fun r : {r : SourceOperation G // operationTag r = 1} => sourceOperationInput r.val
    have hp := classical.strings.compose enc sourceOperationInput Subtype.val _
      (classical.strings.identity enc) parsing.oneWireBytes
    have h := prefixLists_generated classical enc [1] (fun r => operationOneWireBytes r.val) hp
    have he : (fun r : {r : SourceOperation G // operationTag r = 1} =>
        delimitedList SourceView.encode (expandView r.val.2)) =
        (fun r => delimitedList id ([1].map (fun k => encodeNat k ++ operationOneWireBytes r.val))) := by
      funext r
      rcases r with ⟨⟨q,op⟩,hr⟩
      cases op <;> simp [operationTag] at hr
      rfl
    exact Eq.mpr (congrArg (LogspaceComputes enc) he) h
  · let enc := fun r : {r : SourceOperation G // operationTag r = 2} => sourceOperationInput r.val
    have hp := classical.strings.compose enc sourceOperationInput Subtype.val _
      (classical.strings.identity enc) parsing.oneWireBytes
    have h := prefixLists_generated classical enc [2] (fun r => operationOneWireBytes r.val) hp
    have he : (fun r : {r : SourceOperation G // operationTag r = 2} =>
        delimitedList SourceView.encode (expandView r.val.2)) =
        (fun r => delimitedList id ([2].map (fun k => encodeNat k ++ operationOneWireBytes r.val))) := by
      funext r
      rcases r with ⟨⟨q,op⟩,hr⟩
      cases op <;> simp [operationTag] at hr
      rfl
    exact Eq.mpr (congrArg (LogspaceComputes enc) he) h
  · let enc := fun r : {r : SourceOperation G // operationTag r = 3} => sourceOperationInput r.val
    have hp := classical.strings.compose enc sourceOperationInput Subtype.val _
      (classical.strings.identity enc) parsing.twoWireBytes
    have h := prefixLists_generated classical enc [3,4,5] (fun r => operationTwoWireBytes r.val) hp
    have he : (fun r : {r : SourceOperation G // operationTag r = 3} =>
        delimitedList SourceView.encode (expandView r.val.2)) =
        (fun r => delimitedList id ([3,4,5].map (fun k => encodeNat k ++ operationTwoWireBytes r.val))) := by
      funext r
      rcases r with ⟨⟨q,op⟩,hr⟩
      cases op <;> simp [operationTag] at hr
      rfl
    exact Eq.mpr (congrArg (LogspaceComputes enc) he) h

lemma expandedViews_generated (classical : FLListClosure) (queries : FLDataQueryDescription)
    {G : EffectiveGateSet} (parsing : SourceDescriptionParsing G) (opParsing : SourceOperationParsing G) :
    LogspaceComputes (EffectiveSourceComputation.encode (G := G))
      (fun S => delimitedList SourceView.encode (expandedViews S.gates)) := by
  let ctx := elementContext (EffectiveSourceComputation.encode (G := G))
    (fun S => @EffectiveSourceOp.encode G (S.workQubits+S.catalystQubits))
  have hOp := classical.strings.compose ctx sourceOperationInput
    (fun r : Σ S : EffectiveSourceComputation G, EffectiveSourceOp G (S.workQubits+S.catalystQubits) =>
      ⟨r.1.workQubits+r.1.catalystQubits,r.2⟩) _
    (classical.strings.contextRight _ _) (expandView_generated classical queries opParsing)
  exact classical.flatMap (EffectiveSourceComputation.encode (G := G)) (fun _ => EffectiveSourceOp.encode)
    (fun _ => SourceView.encode) (fun S => S.gates) (fun _ => expandView) parsing.operations hOp

lemma expandedViews_length {G : EffectiveGateSet} {q : ℕ} (C : EffectiveSourceCircuit G q) :
    (expandedViews C).length = (ElementaryEncoding.expandEffectiveSourceCircuit C).length := by
  induction C with
  | nil => rfl
  | cons op ops ih =>
    simp only [expandedViews, ElementaryEncoding.expandEffectiveSourceCircuit,
      List.flatMap_cons, List.length_append] at *
    rw [ih]
    congr 1
    cases op <;> rfl

lemma source_duration_generated (classical : FLListClosure) (queries : FLDataQueryDescription)
    {G : EffectiveGateSet} (parsing : SourceDescriptionParsing G) (opParsing : SourceOperationParsing G)
    (F : EffectiveSourceFamily G) :
    LogspaceComputes id (fun x => encodeNat (expandedViews (F.circuit x).gates).length) := by
  have he := expandedViews_generated classical queries parsing opParsing
  have hl := classical.count (EffectiveSourceComputation.encode (G := G)) (fun _ => SourceView.encode)
    (fun S => expandedViews S.gates) he
  exact classical.strings.compose id EffectiveSourceComputation.encode F.circuit _ F.uniform hl


lemma source_duration_computes (classical : FLListClosure) (queries : FLDataQueryDescription)
    {G : EffectiveGateSet} (parsing : SourceDescriptionParsing G) (opParsing : SourceOperationParsing G)
    (F : EffectiveSourceFamily G) :
    LogspaceComputes id (fun x => encodeNat (SourceCoordinates.duration (F.circuit x))) := by
  simpa only [expandedViews_length, SourceCoordinates.duration, SourceCoordinates.expanded] using
    source_duration_generated classical queries parsing opParsing F

lemma viewAt_generated (classical : FLListClosure) (arithmetic : NatArithmeticDescription)
    (queries : FLDataQueryDescription) {G : EffectiveGateSet}
    (parsing : SourceDescriptionParsing G) (opParsing : SourceOperationParsing G) :
    LogspaceComputes (elementContext (EffectiveSourceComputation.encode (G := G))
      (fun _ (n : ℕ) => encodeNat n))
      (fun r => (viewAt r.1.gates r.2).encode) := by
  have hq := nat_add classical arithmetic (EffectiveSourceComputation.encode (G := G))
    (fun S => S.workQubits) (fun S => S.catalystQubits) parsing.work parsing.catalyst
  have hfallback : LogspaceComputes (EffectiveSourceComputation.encode (G := G))
      (fun S => (SourceView.padding : SourceView G (S.workQubits+S.catalystQubits)).encode) :=
    classical.strings.concat _ _ _ (nat_const classical _ 6) hq
  exact queries.getDefault (EffectiveSourceComputation.encode (G := G))
    (fun _ => SourceView.encode) (fun S => expandedViews S.gates) (fun _ => .padding)
    (expandedViews_generated classical queries parsing opParsing) hfallback

/-- The complete classical source lookup. Only raw widths, raw source metadata,
and a branch index are emitted; native circuit generation happens downstream. -/
lemma termViewRequest_generated (classical : FLListClosure) (numeric : ClassicalDescriptionClosure)
    (arithmetic : NatArithmeticDescription) (queries : FLDataQueryDescription)
    (prefixParsing : UnaryPrefixParsing) {G : EffectiveGateSet}
    (parsing : SourceDescriptionParsing G) (opParsing : SourceOperationParsing G) :
    LogspaceComputes (sourceTermInput (G := G))
      (fun r => viewTermInput (termViewRequest r)) := by
  let enc := sourceTermInput (G := G)
  have hS : LogspaceComputes enc (fun r => r.1.encode) :=
    classical.strings.contextLeft _ _
  have hp : LogspaceComputes enc (fun r => encodeNat r.2.1 ++ encodeNat r.2.2.val) :=
    classical.strings.contextRight _ _
  have ht : LogspaceComputes enc (fun r => encodeNat r.2.1) :=
    classical.strings.compose enc unaryPrefixInput
      (fun r => (r.2.1,encodeNat r.2.2.val)) _ hp prefixParsing.first
  have hj : LogspaceComputes enc (fun r => encodeNat r.2.2.val) :=
    classical.strings.compose enc unaryPrefixInput
      (fun r => (r.2.1,encodeNat r.2.2.val)) _ hp prefixParsing.rest
  have hlookup : LogspaceComputes enc (fun r =>
      elementContext (EffectiveSourceComputation.encode (G := G)) (fun _ (n : ℕ) => encodeNat n)
        (⟨r.1,r.2.1⟩ : Σ _ : EffectiveSourceComputation G, ℕ)) :=
    numeric.pair enc _ _ hS ht
  have hview := classical.strings.compose enc
    (elementContext (EffectiveSourceComputation.encode (G := G)) (fun _ (n : ℕ) => encodeNat n))
    (fun r => ⟨r.1,r.2.1⟩) _ hlookup (viewAt_generated classical arithmetic queries parsing opParsing)
  have hqBase := nat_add classical arithmetic (EffectiveSourceComputation.encode (G := G))
    (fun S => S.workQubits) (fun S => S.catalystQubits) parsing.work parsing.catalyst
  have hq := classical.strings.compose enc (EffectiveSourceComputation.encode (G := G))
    Sigma.fst _ hS hqBase
  exact classical.strings.concat enc _ _ (classical.strings.concat enc _ _ hq hj) hview

lemma canonicalNativeTerm_eq_viewRequest {G : EffectiveGateSet} (conv : GateConvention G)
    (r : SourceTermRequest G) :
    canonicalNativeTerm conv r.1 r.2.1 r.2.2 =
      viewTerm conv (termViewRequest r).1.property (termViewRequest r).2.1 (termViewRequest r).2.2 :=
  nativeTermAt_eq_view conv (sourceQubits_pos r.1) r.1.gates r.2.1 r.2.2

end Paper25.OperationalModel.UniformCompilation
