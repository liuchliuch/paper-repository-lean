import Paper25.ClassicalCounterCompilation

/-! Fixed byte grammars and generic indexed data queries only. These external
interfaces do not mention matrix interpretations or compilation of circuits. -/
noncomputable section
namespace Paper25.OperationalModel.UniformCompilation
open LocalCompilation
attribute [local instance] Classical.propDecidable

def unaryPrefixInput (p : ℕ × Input) : Input := encodeNat p.1 ++ p.2

/-- Generic parsing of one unary natural followed by arbitrary bytes. -/
structure UnaryPrefixParsing : Prop where
  first : LogspaceComputes unaryPrefixInput (fun p => encodeNat p.1)
  rest : LogspaceComputes unaryPrefixInput Prod.snd

/-- Generic finite dispatch and optional indexed access to a delimited list. -/
structure FLDataQueryDescription : Prop where
  finiteCases : ∀ {α : Type} {n : ℕ} (encode : α → Input) (tag : α → Fin n)
    (output : α → Input),
    LogspaceComputes encode (fun a => encodeNat (tag a).val) →
    (∀ i, LogspaceComputes (fun a : {a // tag a = i} => encode a.val)
      (fun a => output a.val)) →
    LogspaceComputes encode output
  getDefault : ∀ {α : Type} {β : α → Type} (encode : α → Input)
    (element : ∀ a, β a → Input) (xs : ∀ a, List (β a)) (fallback : ∀ a, β a),
    LogspaceComputes encode (fun a => delimitedList (element a) (xs a)) →
    LogspaceComputes encode (fun a => element a (fallback a)) →
    LogspaceComputes (elementContext encode (fun (_ : α) (n : ℕ) => encodeNat n))
      (fun p => element p.1 ((xs p.1)[p.2]?.getD (fallback p.1)))

/-- Parsing the original source format. Its only outputs are literal input
fields and the literal input operation list, repacked with member lengths. -/
structure SourceDescriptionParsing (G : EffectiveGateSet) : Prop where
  work : LogspaceComputes (EffectiveSourceComputation.encode (G := G))
    (fun S => encodeNat S.workQubits)
  catalyst : LogspaceComputes (EffectiveSourceComputation.encode (G := G))
    (fun S => encodeNat S.catalystQubits)
  output : LogspaceComputes (EffectiveSourceComputation.encode (G := G))
    (fun S => encodeNat S.outputQubit.val)
  operations : LogspaceComputes (EffectiveSourceComputation.encode (G := G))
    (fun S => delimitedList EffectiveSourceOp.encode S.gates)

abbrev SourceOperation (G : EffectiveGateSet) := Σ q, EffectiveSourceOp G q

def sourceOperationInput {G : EffectiveGateSet} (r : SourceOperation G) : Input := r.2.encode

def operationTag {G : EffectiveGateSet} (r : SourceOperation G) : Fin 4 :=
  match r.2 with
  | .gate _ => 0
  | .dephase _ => 1
  | .reset _ => 2
  | .measurement _ => 3

def operationNativeBytes {G : EffectiveGateSet} (r : SourceOperation G) : Input :=
  match r.2 with | .gate g => g.encode | _ => []

def operationOneWireBytes {G : EffectiveGateSet} (r : SourceOperation G) : Input :=
  match r.2 with | .dephase p => p.encode | .reset p => p.encode | _ => []

def operationTwoWireBytes {G : EffectiveGateSet} (r : SourceOperation G) : Input :=
  match r.2 with | .measurement p => p.encode | _ => []

/-- Literal opcode and payload parsing for the original four source-operation
forms; no measurement expansion or output gate list is an external field. -/
structure SourceOperationParsing (G : EffectiveGateSet) : Prop where
  tag : LogspaceComputes (sourceOperationInput (G := G))
    (fun r => encodeNat (operationTag r).val)
  nativeBytes : LogspaceComputes (sourceOperationInput (G := G)) operationNativeBytes
  oneWireBytes : LogspaceComputes (sourceOperationInput (G := G)) operationOneWireBytes
  twoWireBytes : LogspaceComputes (sourceOperationInput (G := G)) operationTwoWireBytes

lemma source_description_generated (_classical : FLListClosure) {G : EffectiveGateSet}
    (F : EffectiveSourceFamily G) :
    LogspaceComputes id (fun x => (F.circuit x).encode) := F.uniform

lemma source_work_generated (classical : FLListClosure) {G : EffectiveGateSet}
    (parsing : SourceDescriptionParsing G) (F : EffectiveSourceFamily G) :
    LogspaceComputes id (fun x => encodeNat (F.circuit x).workQubits) :=
  classical.strings.compose id EffectiveSourceComputation.encode F.circuit _ F.uniform parsing.work

lemma source_catalyst_generated (classical : FLListClosure) {G : EffectiveGateSet}
    (parsing : SourceDescriptionParsing G) (F : EffectiveSourceFamily G) :
    LogspaceComputes id (fun x => encodeNat (F.circuit x).catalystQubits) :=
  classical.strings.compose id EffectiveSourceComputation.encode F.circuit _ F.uniform parsing.catalyst

lemma source_output_generated (classical : FLListClosure) {G : EffectiveGateSet}
    (parsing : SourceDescriptionParsing G) (F : EffectiveSourceFamily G) :
    LogspaceComputes id (fun x => encodeNat (F.circuit x).outputQubit.val) :=
  classical.strings.compose id EffectiveSourceComputation.encode F.circuit _ F.uniform parsing.output

lemma source_operations_generated (classical : FLListClosure) {G : EffectiveGateSet}
    (parsing : SourceDescriptionParsing G) (F : EffectiveSourceFamily G) :
    LogspaceComputes id (fun x => delimitedList EffectiveSourceOp.encode (F.circuit x).gates) :=
  classical.strings.compose id EffectiveSourceComputation.encode F.circuit _ F.uniform parsing.operations

lemma source_qubits_generated (classical : FLListClosure) (arithmetic : NatArithmeticDescription)
    {G : EffectiveGateSet} (parsing : SourceDescriptionParsing G) (F : EffectiveSourceFamily G) :
    LogspaceComputes id (fun x => encodeNat
      ((F.circuit x).workQubits+(F.circuit x).catalystQubits)) :=
  nat_add classical arithmetic id _ _
    (source_work_generated classical parsing F) (source_catalyst_generated classical parsing F)

lemma finiteFamily_generated (classical : FLListClosure) (queries : FLDataQueryDescription)
    {G : EffectiveGateSet} {α : Type} {q n : ℕ} (encode : α → Input)
    (j : α → Fin n) (C : Fin n → EffectiveCircuit G q)
    (hj : LogspaceComputes encode (fun a => encodeNat (j a).val)) :
    GeneratedCircuit encode (fun a => C (j a)) := by
  apply queries.finiteCases encode j _ hj
  intro i
  have h := constant_generated classical (fun a : {a // j a = i} => encode a.val) (C i)
  have he (a : {a // j a = i}) : C (j a.val) = C i := congrArg C a.property
  simpa only [GeneratedCircuit, he] using h

end Paper25.OperationalModel.UniformCompilation
