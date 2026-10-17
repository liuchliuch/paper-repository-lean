import Paper25.LocalCompilation

/-! # Description generation for actual local-list compilation

The external inputs below are classical FL closure on explicit strings, lists,
and one fixed byte grammar, plus machines for single native primitives. They
are a deliberately exposed use of the standard recomputation/composition
method (Jones, *Computability and Complexity*, §21.6: Proposition 21.6.1,
Lemma 21.6.2 and Theorem 21.6.3, printed pp. 327--329,
https://www.sns.ias.edu/pitp2/2012files/Jonesbook-whole-1.pdf), rather than a claim that
finite-machine closure has been reproved here. No field asserts uniformity of a
quantum circuit transformer or of the paper's simulator.

Rational primitive parameters use the actual unreduced `RationalRep.encode`;
no canonical-rational/gcd computation is assumed. Pattern requests include
unary 2^ell padding, matching the allowed exponential-in-control-width native
primitive cost and the logarithmic clock/selector widths used by the paper.
-/
noncomputable section
namespace Paper25.OperationalModel.UniformCompilation
open LocalCompilation
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1600000

/-- A list grammar with a unary count and an explicit length on every member. -/
def delimitedList {β : Type} (encode : β → Input) (xs : List β) : Input :=
  encodeNat xs.length ++
    (xs.map (fun b => encodeNat (encode b).length ++ encode b)).flatten

/-- Preserve the original input in each list-element context. -/
def elementContext {α : Type} {β : α → Type} (encode : α → Input)
    (element : ∀ a, β a → Input) (p : Σ a, β a) : Input :=
  encodeNat (encode p.1).length ++ encode p.1 ++ element p.1 p.2

/-- Pure string operations only. These are the standard FL recomputation
closures, stated against the project's genuine finite-transducer predicate. -/
structure FLStringClosure : Prop where
  identity : ∀ {α : Type} (encode : α → Input), LogspaceComputes encode encode
  constant : ∀ {α : Type} (encode : α → Input) (output : Input),
    LogspaceComputes encode (fun _ => output)
  concat : ∀ {α : Type} (encode : α → Input) (f g : α → Input),
    LogspaceComputes encode f → LogspaceComputes encode g →
      LogspaceComputes encode (fun a => f a ++ g a)
  compose : ∀ {α β : Type} (encodeA : α → Input) (encodeB : β → Input)
    (f : α → β) (g : β → Input),
    LogspaceComputes encodeA (fun a => encodeB (f a)) →
    LogspaceComputes encodeB g → LogspaceComputes encodeA (fun a => g (f a))
  conditional : ∀ {α : Type} (encode : α → Input) (p : α → Bool) (f g : α → Input),
    LogspaceComputes encode (fun a => encodeBool (p a)) →
    LogspaceComputes encode f → LogspaceComputes encode g →
    LogspaceComputes encode (fun a => if p a then f a else g a)
  contextLeft : ∀ {α : Type} {β : α → Type} (encode : α → Input)
    (element : ∀ a, β a → Input),
    LogspaceComputes (elementContext encode element) (fun p => encode p.1)
  contextRight : ∀ {α : Type} {β : α → Type} (encode : α → Input)
    (element : ∀ a, β a → Input),
    LogspaceComputes (elementContext encode element) (fun p => element p.1 p.2)

/-- Generic polynomial-output list operations. The statements quantify over
arbitrary data and encodings; there are no quantum gates or matrices here. -/
structure FLListClosure : Prop where
  strings : FLStringClosure
  singleton : ∀ {α : Type} {β : α → Type} (encode : α → Input)
    (element : ∀ a, β a → Input) (f : ∀ a, β a),
    LogspaceComputes encode (fun a => element a (f a)) →
    LogspaceComputes encode (fun a => delimitedList (element a) [f a])
  count : ∀ {α : Type} {β : α → Type} (encode : α → Input)
    (element : ∀ a, β a → Input) (xs : ∀ a, List (β a)),
    LogspaceComputes encode (fun a => delimitedList (element a) (xs a)) →
    LogspaceComputes encode (fun a => encodeNat (xs a).length)
  element : ∀ {α : Type} {β : α → Type} (encode : α → Input)
    (element : ∀ a, β a → Input) (xs : ∀ a, List (β a)),
    LogspaceComputes encode (fun a => delimitedList (element a) (xs a)) →
    LogspaceComputes (indexedInput encode (fun a => (xs a).length))
      (fun p => element p.1 ((xs p.1)[p.2.val]))
  append : ∀ {α : Type} {β : α → Type} (encode : α → Input)
    (element : ∀ a, β a → Input) (xs ys : ∀ a, List (β a)),
    LogspaceComputes encode (fun a => delimitedList (element a) (xs a)) →
    LogspaceComputes encode (fun a => delimitedList (element a) (ys a)) →
    LogspaceComputes encode (fun a => delimitedList (element a) (xs a ++ ys a))
  reverse : ∀ {α : Type} {β : α → Type} (encode : α → Input)
    (element : ∀ a, β a → Input) (xs : ∀ a, List (β a)),
    LogspaceComputes encode (fun a => delimitedList (element a) (xs a)) →
    LogspaceComputes encode (fun a => delimitedList (element a) (xs a).reverse)
  flatMap : ∀ {α : Type} {β γ : α → Type} (encode : α → Input)
    (inputElement : ∀ a, β a → Input) (outputElement : ∀ a, γ a → Input)
    (xs : ∀ a, List (β a)) (f : ∀ a, β a → List (γ a)),
    LogspaceComputes encode (fun a => delimitedList (inputElement a) (xs a)) →
    LogspaceComputes (elementContext encode inputElement)
      (fun p => delimitedList (outputElement p.1) (f p.1 p.2)) →
    LogspaceComputes encode (fun a => delimitedList (outputElement a) ((xs a).flatMap (f a)))
  replicateFlatten : ∀ {α : Type} {β : α → Type} (encode : α → Input)
    (element : ∀ a, β a → Input) (xs : ∀ a, List (β a)) (count : α → ℕ),
    LogspaceComputes encode (fun a => delimitedList (element a) (xs a)) →
    LogspaceComputes encode (fun a => encodeNat (count a)) →
    PolynomialBoundOn encode count →
    LogspaceComputes encode (fun a => delimitedList (element a)
      ((List.replicate (count a) (xs a)).flatten))
  dedup : ∀ {α : Type} {β : α → Type} [∀ a, DecidableEq (β a)]
    (encode : α → Input) (element : ∀ a, β a → Input) (xs : ∀ a, List (β a)),
    (∀ a, Function.Injective (element a)) →
    LogspaceComputes encode (fun a => delimitedList (element a) (xs a)) →
    LogspaceComputes encode (fun a => delimitedList (element a) (xs a).dedup)
  bitWords : LogspaceComputes (fun ell : ℕ => encodeNat (2^ell))
    (fun ell => delimitedList List.ofFn (binaryLabels ell))
  tabulate : ∀ {α : Type} {β : α → Type} (encode : α → Input)
    (element : ∀ a, β a → Input) (count : α → ℕ)
    (body : ∀ a : Σ a, Fin (count a), List (β a.1)),
    LogspaceComputes encode (fun a => encodeNat (count a)) →
    PolynomialBoundOn encode count →
    LogspaceComputes (indexedInput encode count)
      (fun a => delimitedList (element a.1) (body a)) →
    LogspaceComputes encode (fun a => delimitedList (element a)
      ((List.ofFn (fun i : Fin (count a) => body ⟨a,i⟩)).flatten))

/-- A completely classical instruction grammar: numeric opcode, literal
payload bytes, ambient width, and an ordered array of wire numbers. -/
structure RawInstruction where
  opcode : ℕ
  payload : Input
  ambient : ℕ
  wires : List ℕ

def RawInstruction.encode (g : RawInstruction) : Input :=
  encodeNat g.opcode ++ encodeNat g.payload.length ++ g.payload ++
    (encodeNat g.ambient ++ encodeNat g.wires.length ++
      (g.wires.map encodeNat).flatten)

def rawGate {G : EffectiveGateSet} {q : ℕ} (g : EffectiveLocalGate G q) : RawInstruction where
  opcode := g.kind.val
  payload := g.payload
  ambient := q
  wires := List.ofFn (fun i => (active g.placement i).val)

lemma rawGate_encode {G : EffectiveGateSet} {q : ℕ} (g : EffectiveLocalGate G q) :
    (rawGate g).encode = g.encode := by
  simp [rawGate, RawInstruction.encode, EffectiveLocalGate.encode, Placement.encode,
    active, List.map_ofFn, Function.comp_def]

/-- A pure natural-number table lookup, independent of quantum semantics. -/
def RawInstruction.substitute (ambient : ℕ) (positions : List ℕ)
    (g : RawInstruction) : RawInstruction :=
  ⟨g.opcode, g.payload, ambient,
    g.wires.map (fun i => (positions[i]?).getD 0)⟩

structure SubstitutionRequest where
  ambient : ℕ
  positions : List ℕ
  instruction : RawInstruction

def SubstitutionRequest.encode (r : SubstitutionRequest) : Input :=
  (encodeNat r.ambient ++ encodeNat r.positions.length ++
    (r.positions.map encodeNat).flatten) ++ r.instruction.encode

/-- Append untouched positions, or add an offset to every active position. -/
def RawInstruction.extend (extra : ℕ) (shift : Bool) (g : RawInstruction) : RawInstruction :=
  ⟨g.opcode, g.payload, g.ambient + extra,
    if shift then g.wires.map (fun i => extra+i) else g.wires⟩

structure ExtensionRequest where
  extra : ℕ
  shift : Bool
  instruction : RawInstruction

def ExtensionRequest.encode (r : ExtensionRequest) : Input :=
  encodeNat r.extra ++ encodeBool r.shift ++ r.instruction.encode

def plainInstructions (header : ℕ) (xs : List RawInstruction) : Input :=
  encodeNat header ++ encodeNat xs.length ++ (xs.map RawInstruction.encode).flatten

/-- These external machines only parse/repack the fixed classical byte grammar
or substitute an explicit array of natural wire numbers. In particular they do
not receive a quantum circuit transformer, a matrix, or an ideal algorithm. -/
structure InstructionDescriptionClosure : Prop where
  pack : ∀ {α : Type} (encode : α → Input) (header : α → ℕ)
    (xs : α → List RawInstruction),
    LogspaceComputes encode (fun a => plainInstructions (header a) (xs a)) →
    LogspaceComputes encode (fun a => delimitedList RawInstruction.encode (xs a))
  unpack : ∀ {α : Type} (encode : α → Input) (header : α → ℕ)
    (xs : α → List RawInstruction),
    LogspaceComputes encode (fun a => encodeNat (header a)) →
    LogspaceComputes encode (fun a => delimitedList RawInstruction.encode (xs a)) →
    LogspaceComputes encode (fun a => plainInstructions (header a) (xs a))
  substitute : LogspaceComputes SubstitutionRequest.encode (fun r =>
    (r.instruction.substitute r.ambient r.positions).encode)
  extend : LogspaceComputes ExtensionRequest.encode (fun r =>
    (r.instruction.extend r.extra r.shift).encode)


/-- Internal form of a genuine gate-description generator. -/
def GeneratedCircuit {G : EffectiveGateSet} {α : Type} {q : α → ℕ}
    (encode : α → Input) (C : ∀ a, EffectiveCircuit G (q a)) : Prop :=
  LogspaceComputes encode (fun a => delimitedList EffectiveLocalGate.encode (C a))

lemma raw_delimited {G : EffectiveGateSet} {q : ℕ} (C : EffectiveCircuit G q) :
    delimitedList RawInstruction.encode (C.map rawGate) =
      delimitedList EffectiveLocalGate.encode C := by
  simp [delimitedList, List.map_map, Function.comp_def, rawGate_encode]

lemma raw_plain {G : EffectiveGateSet} {q : ℕ} (header : ℕ) (C : EffectiveCircuit G q) :
    plainInstructions header (C.map rawGate) = encodeGateList header C := by
  simp [plainInstructions, encodeGateList, List.map_map, Function.comp_def, rawGate_encode]

/-- Repacking has no matrix assumptions and preserves the actual gate list. -/
theorem generated_of_logspace (grammar : InstructionDescriptionClosure)
    {G : EffectiveGateSet} {α : Type} {q : α → ℕ} (encode : α → Input)
    (header : α → ℕ) (C : ∀ a, EffectiveCircuit G (q a))
    (hC : LogspaceComputes encode (fun a => encodeGateList (header a) (C a))) :
    GeneratedCircuit encode C := by
  have h := grammar.pack encode header (fun a => (C a).map rawGate)
  simpa only [raw_delimited, raw_plain] using h (by simpa only [raw_plain] using hC)

theorem generated_logspace (grammar : InstructionDescriptionClosure)
    {G : EffectiveGateSet} {α : Type} {q : α → ℕ} (encode : α → Input)
    (header : α → ℕ) (C : ∀ a, EffectiveCircuit G (q a))
    (hheader : LogspaceComputes encode (fun a => encodeNat (header a)))
    (hC : GeneratedCircuit encode C) :
    LogspaceComputes encode (fun a => encodeGateList (header a) (C a)) := by
  have h := grammar.unpack encode header (fun a => (C a).map rawGate) hheader
  simpa only [raw_plain] using h (by simpa only [raw_delimited] using hC)

abbrev NativeRequest (G : EffectiveGateSet) := Σ q, EffectiveLocalGate G q

def nativeInput {G : EffectiveGateSet} (r : NativeRequest G) : Input := r.2.encode

abbrev PatternRequest (G : EffectiveGateSet) := Σ ell, Basis ell × NativeRequest G

def controlPrefix (ell : ℕ) (label : Basis ell) : Input :=
  encodeNat ell ++ encodeNat (2^ell) ++ List.ofFn label

def patternInput {G : EffectiveGateSet} (r : PatternRequest G) : Input :=
  controlPrefix r.1 r.2.1 ++ nativeInput r.2.2

/-- The original effective elementary-gate assumption, restricted to actual
single-native-gate compilers and elementary one-register emitters. It cannot
accept an arbitrary quantum circuit family or any P25 recipe as an argument. -/
structure PrimitiveDescriptionConvention {G : EffectiveGateSet} (conv : GateConvention G) : Prop where
  hadamard : GeneratedCircuit encodeNat conv.hadamardAt
  phaseRep : GeneratedCircuit RationalRep.encode conv.phaseRep
  rotationRep : GeneratedCircuit RationalRep.encode conv.rotationRep
  phaseCost : PolynomialBoundOn RationalRep.encode (fun a => (conv.phaseRep a).length)
  rotationCost : PolynomialBoundOn RationalRep.encode (fun a => (conv.rotationRep a).length)
  adjoint : GeneratedCircuit (nativeInput (G := G)) (fun r => conv.adjointAtom r.2)
  conjugate : GeneratedCircuit (nativeInput (G := G)) (fun r => conv.conjugateAtom r.2)
  control : GeneratedCircuit (nativeInput (G := G)) (fun r => conv.controlAtom r.2)
  pattern : GeneratedCircuit (patternInput (G := G))
    (fun r => conv.patternAtom r.1 r.2.1 r.2.2.2)

lemma GeneratedCircuit.pullback (classical : FLListClosure)
    {G : EffectiveGateSet} {α β : Type} {q : β → ℕ} (encodeA : α → Input)
    (encodeB : β → Input) (f : α → β) (C : ∀ b, EffectiveCircuit G (q b))
    (hf : LogspaceComputes encodeA (fun a => encodeB (f a)))
    (hC : GeneratedCircuit encodeB C) : GeneratedCircuit encodeA (fun a => C (f a)) :=
  classical.strings.compose encodeA encodeB f _ hf hC

lemma nil_generated (classical : FLListClosure)
    {G : EffectiveGateSet} {α : Type} (encode : α → Input) (q : α → ℕ) :
    GeneratedCircuit encode (fun a => ([] : EffectiveCircuit G (q a))) := by
  exact classical.strings.constant encode (encodeNat 0)

lemma constant_generated (classical : FLListClosure)
    {G : EffectiveGateSet} {α : Type} {q : ℕ} (encode : α → Input) (C : EffectiveCircuit G q) :
    GeneratedCircuit encode (fun _ => C) :=
  classical.strings.constant encode (delimitedList EffectiveLocalGate.encode C)

lemma append_generated (classical : FLListClosure)
    {G : EffectiveGateSet} {α : Type} {q : α → ℕ} (encode : α → Input)
    (C D : ∀ a, EffectiveCircuit G (q a))
    (hC : GeneratedCircuit encode C) (hD : GeneratedCircuit encode D) :
    GeneratedCircuit encode (fun a => C a ++ D a) :=
  classical.append encode (fun _ => EffectiveLocalGate.encode) C D hC hD

lemma hadamard_generated (classical : FLListClosure)
    {G : EffectiveGateSet} {conv : GateConvention G} (primitive : PrimitiveDescriptionConvention conv)
    {α : Type} (encode : α → Input) (q : α → ℕ)
    (hq : LogspaceComputes encode (fun a => encodeNat (q a))) :
    GeneratedCircuit encode (fun a => conv.hadamardAt (q a)) :=
  primitive.hadamard.pullback classical encode encodeNat q _ hq

lemma phaseRep_generated (classical : FLListClosure)
    {G : EffectiveGateSet} {conv : GateConvention G} (primitive : PrimitiveDescriptionConvention conv)
    {α : Type} (encode : α → Input) (angle : α → RationalRep)
    (hangle : LogspaceComputes encode (fun a => (angle a).encode)) :
    GeneratedCircuit encode (fun a => conv.phaseRep (angle a)) :=
  primitive.phaseRep.pullback classical encode RationalRep.encode angle _ hangle

lemma rotationRep_generated (classical : FLListClosure)
    {G : EffectiveGateSet} {conv : GateConvention G} (primitive : PrimitiveDescriptionConvention conv)
    {α : Type} (encode : α → Input) (angle : α → RationalRep)
    (hangle : LogspaceComputes encode (fun a => (angle a).encode)) :
    GeneratedCircuit encode (fun a => conv.rotationRep (angle a)) :=
  primitive.rotationRep.pullback classical encode RationalRep.encode angle _ hangle

lemma conjugate_eq_flatMap {G : EffectiveGateSet} (conv : GateConvention G) {q : ℕ}
    (C : EffectiveCircuit G q) : conjugateCircuit conv C = C.flatMap conv.conjugateAtom := by
  induction C with
  | nil => rfl
  | cons g gs ih => simp [conjugateCircuit, ih]

lemma controlled_eq_flatMap {G : EffectiveGateSet} (conv : GateConvention G) {q : ℕ}
    (C : EffectiveCircuit G q) : controlledCircuit conv C = C.flatMap conv.controlAtom := by
  induction C with
  | nil => rfl
  | cons g gs ih => simp [controlledCircuit, ih]

lemma pattern_eq_flatMap {G : EffectiveGateSet} (conv : GateConvention G) {q : ℕ}
    (ell : ℕ) (label : Basis ell) (C : EffectiveCircuit G q) :
    patternCircuit conv ell label C = C.flatMap (conv.patternAtom ell label) := by
  induction C with
  | nil => rfl
  | cons g gs ih => simp [patternCircuit, ih]

lemma adjoint_eq_flatMap_reverse {G : EffectiveGateSet} (conv : GateConvention G) {q : ℕ}
    (C : EffectiveCircuit G q) : adjointCircuit conv C = C.reverse.flatMap conv.adjointAtom := by
  induction C with
  | nil => rfl
  | cons g gs ih => simp [adjointCircuit, ih]

lemma conjugateCircuit_generated (classical : FLListClosure)
    {G : EffectiveGateSet} {conv : GateConvention G} (primitive : PrimitiveDescriptionConvention conv)
    {α : Type} {q : α → ℕ} (encode : α → Input) (C : ∀ a, EffectiveCircuit G (q a))
    (hC : GeneratedCircuit encode C) :
    GeneratedCircuit encode (fun a => conjugateCircuit conv (C a)) := by
  have hAtom : LogspaceComputes
      (elementContext encode (fun a => @EffectiveLocalGate.encode G (q a)))
      (fun p => delimitedList EffectiveLocalGate.encode (conv.conjugateAtom p.2)) := by
    exact primitive.conjugate.pullback classical _ nativeInput
      (fun p : Σ a, EffectiveLocalGate G (q a) => ⟨q p.1,p.2⟩) _
      (classical.strings.contextRight _ _)
  have h := classical.flatMap encode (fun _ => EffectiveLocalGate.encode)
    (fun _ => EffectiveLocalGate.encode) C (fun _ => conv.conjugateAtom) hC hAtom
  simpa only [conjugate_eq_flatMap] using h

lemma controlledCircuit_generated (classical : FLListClosure)
    {G : EffectiveGateSet} {conv : GateConvention G} (primitive : PrimitiveDescriptionConvention conv)
    {α : Type} {q : α → ℕ} (encode : α → Input) (C : ∀ a, EffectiveCircuit G (q a))
    (hC : GeneratedCircuit encode C) :
    GeneratedCircuit encode (fun a => controlledCircuit conv (C a)) := by
  have hAtom : LogspaceComputes
      (elementContext encode (fun a => @EffectiveLocalGate.encode G (q a)))
      (fun p => delimitedList EffectiveLocalGate.encode (conv.controlAtom p.2)) := by
    exact primitive.control.pullback classical _ nativeInput
      (fun p : Σ a, EffectiveLocalGate G (q a) => ⟨q p.1,p.2⟩) _
      (classical.strings.contextRight _ _)
  have h := classical.flatMap encode (fun _ => EffectiveLocalGate.encode)
    (fun _ => EffectiveLocalGate.encode) C (fun _ => conv.controlAtom) hC hAtom
  simpa only [controlled_eq_flatMap] using h

lemma adjointCircuit_generated (classical : FLListClosure)
    {G : EffectiveGateSet} {conv : GateConvention G} (primitive : PrimitiveDescriptionConvention conv)
    {α : Type} {q : α → ℕ} (encode : α → Input) (C : ∀ a, EffectiveCircuit G (q a))
    (hC : GeneratedCircuit encode C) :
    GeneratedCircuit encode (fun a => adjointCircuit conv (C a)) := by
  have hrev := classical.reverse encode (fun _ => EffectiveLocalGate.encode) C hC
  have hAtom : LogspaceComputes
      (elementContext encode (fun a => @EffectiveLocalGate.encode G (q a)))
      (fun p => delimitedList EffectiveLocalGate.encode (conv.adjointAtom p.2)) := by
    exact primitive.adjoint.pullback classical _ nativeInput
      (fun p : Σ a, EffectiveLocalGate G (q a) => ⟨q p.1,p.2⟩) _
      (classical.strings.contextRight _ _)
  have h := classical.flatMap encode (fun _ => EffectiveLocalGate.encode)
    (fun _ => EffectiveLocalGate.encode) (fun a => (C a).reverse)
    (fun _ => conv.adjointAtom) hrev hAtom
  simpa only [adjoint_eq_flatMap_reverse] using h

lemma patternCircuit_generated (classical : FLListClosure)
    {G : EffectiveGateSet} {conv : GateConvention G} (primitive : PrimitiveDescriptionConvention conv)
    {α : Type} {q ell : α → ℕ} (encode : α → Input)
    (label : ∀ a, Basis (ell a)) (C : ∀ a, EffectiveCircuit G (q a))
    (hprefix : LogspaceComputes encode (fun a => controlPrefix (ell a) (label a)))
    (hC : GeneratedCircuit encode C) :
    GeneratedCircuit encode (fun a => patternCircuit conv (ell a) (label a) (C a)) := by
  let ctx := elementContext encode (fun a => @EffectiveLocalGate.encode G (q a))
  have hL : LogspaceComputes ctx (fun p => controlPrefix (ell p.1) (label p.1)) :=
    classical.strings.compose ctx encode Sigma.fst _
      (classical.strings.contextLeft _ _) hprefix
  have hR := classical.strings.contextRight encode (fun a => @EffectiveLocalGate.encode G (q a))
  have hrequest : LogspaceComputes ctx (fun p =>
      patternInput (⟨ell p.1,label p.1,⟨q p.1,p.2⟩⟩ : PatternRequest G)) :=
    classical.strings.concat ctx _ _ hL hR
  have hAtom := primitive.pattern.pullback classical ctx patternInput
    (fun p => ⟨ell p.1,label p.1,⟨q p.1,p.2⟩⟩) _ hrequest
  have h := classical.flatMap encode (fun _ => EffectiveLocalGate.encode)
    (fun _ => EffectiveLocalGate.encode) C
    (fun a => conv.patternAtom (ell a) (label a)) hC hAtom
  simpa only [pattern_eq_flatMap] using h


lemma rawGate_embed {G : EffectiveGateSet} {q k : ℕ} (p : Placement q k)
    (g : EffectiveLocalGate G k) :
    rawGate (embedGate p g) =
      (rawGate g).substitute q (List.ofFn (fun i => (active p i).val)) := by
  simp only [rawGate, embedGate, active_placementOfEmbedding_eq,
    RawInstruction.substitute, List.map_ofFn, Function.comp_def]
  congr 1
  apply congrArg List.ofFn
  funext i
  simp [(active g.placement i).isLt]

lemma embedGate_encode {G : EffectiveGateSet} {q k : ℕ} (p : Placement q k)
    (g : EffectiveLocalGate G k) :
    (embedGate p g).encode =
      ((rawGate g).substitute q (List.ofFn (fun i => (active p i).val))).encode := by
  rw [← rawGate_embed, rawGate_encode]

lemma substitutionInput_eq {G : EffectiveGateSet} {q k : ℕ} (p : Placement q k)
    (g : EffectiveLocalGate G k) :
    (SubstitutionRequest.mk q (List.ofFn (fun i => (active p i).val)) (rawGate g)).encode =
      p.encode ++ g.encode := by
  simp [SubstitutionRequest.encode, Placement.encode, active, List.map_ofFn,
    Function.comp_def, rawGate_encode]

/-- The embedding generator performs only classical substitution of the
explicit active-position array. It never inspects or computes a matrix. -/
lemma embedCircuit_generated (classical : FLListClosure) (grammar : InstructionDescriptionClosure)
    {G : EffectiveGateSet} {α : Type} {q k : α → ℕ} (encode : α → Input)
    (p : ∀ a, Placement (q a) (k a)) (C : ∀ a, EffectiveCircuit G (k a))
    (hp : LogspaceComputes encode (fun a => (p a).encode))
    (hC : GeneratedCircuit encode C) :
    GeneratedCircuit encode (fun a => embedCircuit (p a) (C a)) := by
  let ctx := elementContext encode (fun a => @EffectiveLocalGate.encode G (k a))
  have hL : LogspaceComputes ctx (fun r => (p r.1).encode) :=
    classical.strings.compose ctx encode Sigma.fst _
      (classical.strings.contextLeft _ _) hp
  have hR := classical.strings.contextRight encode (fun a => @EffectiveLocalGate.encode G (k a))
  let request (r : Σ a, EffectiveLocalGate G (k a)) : SubstitutionRequest :=
    ⟨q r.1, List.ofFn (fun i => (active (p r.1) i).val), rawGate r.2⟩
  have hrequest : LogspaceComputes ctx (fun r => (request r).encode) := by
    simpa only [request, substitutionInput_eq] using classical.strings.concat ctx _ _ hL hR
  have hsub := classical.strings.compose ctx SubstitutionRequest.encode request _
    hrequest grammar.substitute
  have hgate : LogspaceComputes ctx (fun r => (embedGate (p r.1) r.2).encode) := by
    change LogspaceComputes ctx (fun r =>
      ((rawGate r.2).substitute (q r.1)
        (List.ofFn (fun i => (active (p r.1) i).val))).encode) at hsub
    simpa only [← embedGate_encode] using hsub
  have hAtom := classical.singleton ctx (fun r => @EffectiveLocalGate.encode G (q r.1))
    (fun r => embedGate (p r.1) r.2) hgate
  have h := classical.flatMap encode (fun _ => EffectiveLocalGate.encode)
    (fun _ => EffectiveLocalGate.encode) C (fun a g => [embedGate (p a) g]) hC hAtom
  simpa only [embedCircuit, ← List.map_eq_flatMap] using h

lemma repeat_eq_replicate {G : EffectiveGateSet} {q : ℕ} (C : EffectiveCircuit G q) (n : ℕ) :
    repeatCircuit C n = (List.replicate n C).flatten := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [repeatCircuit, ih, List.replicate_succ']
    simp

lemma repeatCircuit_generated (classical : FLListClosure)
    {G : EffectiveGateSet} {α : Type} {q : α → ℕ} (encode : α → Input)
    (C : ∀ a, EffectiveCircuit G (q a)) (count : α → ℕ)
    (hC : GeneratedCircuit encode C)
    (hcount : LogspaceComputes encode (fun a => encodeNat (count a)))
    (hpoly : PolynomialBoundOn encode count) :
    GeneratedCircuit encode (fun a => repeatCircuit (C a) (count a)) := by
  have h := classical.replicateFlatten encode (fun _ => EffectiveLocalGate.encode) C count hC hcount hpoly
  simpa only [repeat_eq_replicate] using h

lemma loop_generated (classical : FLListClosure)
    {G : EffectiveGateSet} {α : Type} {q : α → ℕ} (encode : α → Input) (count : α → ℕ)
    (body : ∀ a : Σ a, Fin (count a), EffectiveCircuit G (q a.1))
    (hcount : LogspaceComputes encode (fun a => encodeNat (count a)))
    (hpoly : PolynomialBoundOn encode count)
    (hbody : GeneratedCircuit (indexedInput encode count) body) :
    GeneratedCircuit encode (fun a =>
      (List.ofFn (fun i : Fin (count a) => body ⟨a,i⟩)).flatten) :=
  classical.tabulate encode (fun _ => EffectiveLocalGate.encode) count body hcount hpoly hbody


/-- A pointwise native-description computation extends to the actual mapped
list using the generic classical flat-map closure. -/
lemma mapCircuit_generated (classical : FLListClosure)
    {G : EffectiveGateSet} {α : Type} {q r : α → ℕ} (encode : α → Input)
    (C : ∀ a, EffectiveCircuit G (q a))
    (f : ∀ a, EffectiveLocalGate G (q a) → EffectiveLocalGate G (r a))
    (hC : GeneratedCircuit encode C)
    (hf : LogspaceComputes (elementContext encode (fun a => @EffectiveLocalGate.encode G (q a)))
      (fun p => (f p.1 p.2).encode)) :
    GeneratedCircuit encode (fun a => (C a).map (f a)) := by
  have hAtom := classical.singleton
    (elementContext encode (fun a => @EffectiveLocalGate.encode G (q a)))
    (fun p => @EffectiveLocalGate.encode G (r p.1))
    (fun p => f p.1 p.2) hf
  have h := classical.flatMap encode (fun _ => EffectiveLocalGate.encode)
    (fun _ => EffectiveLocalGate.encode) C (fun a g => [f a g]) hC hAtom
  simpa only [← List.map_eq_flatMap] using h

lemma rawGate_left {G : EffectiveGateSet} {q : ℕ} (g : EffectiveLocalGate G q) (r : ℕ) :
    rawGate (liftLeft g r) = (rawGate g).extend r false := by
  simp [rawGate, liftLeft, RawInstruction.extend, active_placementOfEmbedding_eq,
    leftEmbedding]

lemma rawGate_right {G : EffectiveGateSet} {r : ℕ} (g : EffectiveLocalGate G r) (q : ℕ) :
    rawGate (liftRight g q) = (rawGate g).extend q true := by
  simp only [rawGate, liftRight, RawInstruction.extend, active_placementOfEmbedding_eq,
    if_true, rightEmbedding, List.map_ofFn, Function.comp_def]
  congr 1
  exact Nat.add_comm _ _

lemma liftLeftCircuit_generated (classical : FLListClosure) (grammar : InstructionDescriptionClosure)
    {G : EffectiveGateSet} {α : Type} {q r : α → ℕ} (encode : α → Input)
    (C : ∀ a, EffectiveCircuit G (q a))
    (hC : GeneratedCircuit encode C)
    (hr : LogspaceComputes encode (fun a => encodeNat (r a))) :
    GeneratedCircuit encode (fun a => (C a).map (fun g => liftLeft g (r a))) := by
  apply mapCircuit_generated classical encode C _ hC
  let ctx := elementContext encode (fun a => @EffectiveLocalGate.encode G (q a))
  have hL : LogspaceComputes ctx (fun p => encodeNat (r p.1)) :=
    classical.strings.compose ctx encode Sigma.fst _
      (classical.strings.contextLeft _ _) hr
  have hB := classical.strings.constant ctx (encodeBool false)
  have hR := classical.strings.contextRight encode (fun a => @EffectiveLocalGate.encode G (q a))
  have hrequest : LogspaceComputes ctx (fun p =>
      (ExtensionRequest.mk (r p.1) false (rawGate p.2)).encode) := by
    simpa only [ExtensionRequest.encode, rawGate_encode] using
      classical.strings.concat ctx _ _ (classical.strings.concat ctx _ _ hL hB) hR
  have h := classical.strings.compose ctx ExtensionRequest.encode
    (fun p : Σ a, EffectiveLocalGate G (q a) => ⟨r p.1,false,rawGate p.2⟩) _
    hrequest grammar.extend
  simpa only [← rawGate_left, rawGate_encode] using h

lemma liftRightCircuit_generated (classical : FLListClosure) (grammar : InstructionDescriptionClosure)
    {G : EffectiveGateSet} {α : Type} {q r : α → ℕ} (encode : α → Input)
    (D : ∀ a, EffectiveCircuit G (r a))
    (hD : GeneratedCircuit encode D)
    (hq : LogspaceComputes encode (fun a => encodeNat (q a))) :
    GeneratedCircuit encode (fun a => (D a).map (fun g => liftRight g (q a))) := by
  apply mapCircuit_generated classical encode D _ hD
  let ctx := elementContext encode (fun a => @EffectiveLocalGate.encode G (r a))
  have hL : LogspaceComputes ctx (fun p => encodeNat (q p.1)) :=
    classical.strings.compose ctx encode Sigma.fst _
      (classical.strings.contextLeft _ _) hq
  have hB := classical.strings.constant ctx (encodeBool true)
  have hR := classical.strings.contextRight encode (fun a => @EffectiveLocalGate.encode G (r a))
  have hrequest : LogspaceComputes ctx (fun p =>
      (ExtensionRequest.mk (q p.1) true (rawGate p.2)).encode) := by
    simpa only [ExtensionRequest.encode, rawGate_encode] using
      classical.strings.concat ctx _ _ (classical.strings.concat ctx _ _ hL hB) hR
  have h := classical.strings.compose ctx ExtensionRequest.encode
    (fun p : Σ a, EffectiveLocalGate G (r a) => ⟨q p.1,true,rawGate p.2⟩) _
    hrequest grammar.extend
  simpa only [← rawGate_right, rawGate_encode] using h

lemma tensorCircuit_generated (classical : FLListClosure) (grammar : InstructionDescriptionClosure)
    {G : EffectiveGateSet} {α : Type} {q r : α → ℕ} (encode : α → Input)
    (C : ∀ a, EffectiveCircuit G (q a)) (D : ∀ a, EffectiveCircuit G (r a))
    (hC : GeneratedCircuit encode C) (hD : GeneratedCircuit encode D)
    (hq : LogspaceComputes encode (fun a => encodeNat (q a)))
    (hr : LogspaceComputes encode (fun a => encodeNat (r a))) :
    GeneratedCircuit encode (fun a => tensorCircuit (C a) (D a)) :=
  append_generated classical encode _ _
    (liftLeftCircuit_generated classical grammar encode C hC hr)
    (liftRightCircuit_generated classical grammar encode D hD hq)

lemma selectList_eq_flatMap {G : EffectiveGateSet} (conv : GateConvention G) {ell q : ℕ}
    (family : Basis ell → EffectiveCircuit G q) (ls : List (Basis ell)) :
    selectListCircuit conv family ls = ls.flatMap (fun b => patternCircuit conv ell b (family b)) := by
  induction ls with
  | nil => rfl
  | cons b bs ih => simp [selectListCircuit, ih]

lemma wordEncoding_injective (ell : ℕ) : Function.Injective (@List.ofFn Bit ell) := by
  intro x y h
  funext i
  have hi := congrArg (fun l : List Bit => l[i.val]?) h
  simpa [List.getElem?_ofFn, i.isLt] using hi

lemma labels_generated (classical : FLListClosure) {α : Type}
    (encode : α → Input) (ell : α → ℕ)
    (hstates : LogspaceComputes encode (fun a => encodeNat (2^(ell a)))) :
    LogspaceComputes encode (fun a => delimitedList List.ofFn (labels (ell a))) := by
  have hwords := classical.strings.compose encode (fun ell : ℕ => encodeNat (2^ell)) ell _
    hstates classical.bitWords
  exact classical.dedup encode (fun _ => List.ofFn) (fun a => binaryLabels (ell a))
    (fun a => wordEncoding_injective (ell a)) hwords

lemma selectCircuit_generated (classical : FLListClosure)
    {G : EffectiveGateSet} {conv : GateConvention G} (primitive : PrimitiveDescriptionConvention conv)
    {α : Type} {q ell : α → ℕ} (encode : α → Input)
    (family : ∀ a, Basis (ell a) → EffectiveCircuit G (q a))
    (hwidth : LogspaceComputes encode (fun a => encodeNat (ell a) ++ encodeNat (2^(ell a))))
    (hstates : LogspaceComputes encode (fun a => encodeNat (2^(ell a))))
    (hfamily : GeneratedCircuit (elementContext encode (fun _ => List.ofFn))
      (fun p => family p.1 p.2)) :
    GeneratedCircuit encode (fun a => selectCircuit conv (family a)) := by
  let ctx := elementContext encode (fun a => @List.ofFn Bit (ell a))
  have hL : LogspaceComputes ctx (fun p => encodeNat (ell p.1) ++ encodeNat (2^(ell p.1))) :=
    classical.strings.compose ctx encode Sigma.fst _
      (classical.strings.contextLeft _ _) hwidth
  have hR := classical.strings.contextRight encode (fun a => @List.ofFn Bit (ell a))
  have hprefix : LogspaceComputes ctx (fun p => controlPrefix (ell p.1) p.2) :=
    classical.strings.concat ctx _ _ hL hR
  have hbody := patternCircuit_generated classical primitive ctx (fun p => p.2)
    (fun p => family p.1 p.2) hprefix hfamily
  have h := classical.flatMap encode (fun _ => List.ofFn) (fun _ => EffectiveLocalGate.encode)
    (fun a => labels (ell a)) (fun a b => patternCircuit conv (ell a) b (family a b))
    (labels_generated classical encode ell hstates) hbody
  simpa only [selectCircuit, selectList_eq_flatMap] using h

lemma coherentFilterCircuit_generated (classical : FLListClosure)
    {G : EffectiveGateSet} {conv : GateConvention G} (primitive : PrimitiveDescriptionConvention conv)
    {α : Type} {q : α → ℕ} (encode : α → Input)
    (PE R : ∀ a, EffectiveCircuit G (q a))
    (hPE : GeneratedCircuit encode PE) (hR : GeneratedCircuit encode R) :
    GeneratedCircuit encode (fun a => coherentFilterCircuit conv (PE a) (R a)) :=
  append_generated classical encode _ _ (append_generated classical encode PE R hPE hR)
    (adjointCircuit_generated classical primitive encode PE hPE)

lemma readoutCircuit_generated (classical : FLListClosure)
    {G : EffectiveGateSet} {conv : GateConvention G} (primitive : PrimitiveDescriptionConvention conv)
    {α : Type} {q : α → ℕ} (encode : α → Input)
    (C : ∀ a, EffectiveCircuit G (q a))
    (hC : GeneratedCircuit encode C)
    (hq : LogspaceComputes encode (fun a => encodeNat (q a))) :
    GeneratedCircuit encode (fun a => (readoutCircuit conv (C a)).gates) := by
  exact append_generated classical encode _ _
    (append_generated classical encode _ _ (hadamard_generated classical primitive encode q hq)
      (controlledCircuit_generated classical primitive encode C hC))
    (hadamard_generated classical primitive encode q hq)

/-- Binary shift is a pure classical raw integer emitter. -/
def powerTwoRep (d : ℕ) : RationalRep := ⟨(2 : ℤ)^d, 1, by decide⟩

structure BinaryShiftDescription : Prop where
  powerTwo : LogspaceComputes encodeNat (fun d => (powerTwoRep d).encode)


/-- Pure classical branching preserves generation of the chosen actual list. -/
lemma conditional_generated (classical : FLListClosure)
    {G : EffectiveGateSet} {α : Type} {q : α → ℕ} (encode : α → Input)
    (p : α → Bool) (C D : ∀ a, EffectiveCircuit G (q a))
    (hp : LogspaceComputes encode (fun a => encodeBool (p a)))
    (hC : GeneratedCircuit encode C) (hD : GeneratedCircuit encode D) :
    GeneratedCircuit encode (fun a => if p a then C a else D a) := by
  have h := classical.strings.conditional encode p
    (fun a => delimitedList EffectiveLocalGate.encode (C a))
    (fun a => delimitedList EffectiveLocalGate.encode (D a)) hp hC hD
  simpa only [GeneratedCircuit, apply_ite] using h

lemma circuit_count_generated (classical : FLListClosure)
    {G : EffectiveGateSet} {α : Type} {q : α → ℕ} (encode : α → Input)
    (C : ∀ a, EffectiveCircuit G (q a)) (hC : GeneratedCircuit encode C) :
    LogspaceComputes encode (fun a => encodeNat (C a).length) :=
  classical.count encode (fun _ => EffectiveLocalGate.encode) C hC

lemma circuit_element_generated (classical : FLListClosure)
    {G : EffectiveGateSet} {α : Type} {q : α → ℕ} (encode : α → Input)
    (C : ∀ a, EffectiveCircuit G (q a)) (hC : GeneratedCircuit encode C) :
    LogspaceComputes (indexedInput encode (fun a => (C a).length))
      (fun p => ((C p.1)[p.2.val]).encode) :=
  classical.element encode (fun _ => EffectiveLocalGate.encode) C hC

lemma indexed_input_generated (classical : FLListClosure) {α : Type}
    (encode : α → Input) (count : α → ℕ) :
    LogspaceComputes (indexedInput encode count) (fun p => encode p.1) :=
  classical.strings.contextLeft encode (fun a (i : Fin (count a)) => encodeNat i.val)

lemma indexed_counter_generated (classical : FLListClosure) {α : Type}
    (encode : α → Input) (count : α → ℕ) :
    LogspaceComputes (indexedInput encode count) (fun p => encodeNat p.2.val) :=
  classical.strings.contextRight encode (fun a (i : Fin (count a)) => encodeNat i.val)

/-- Every real physical wire shuffle is handled by its printed active-position
array. The complement chosen by `placementOfEmbedding` is not printed. This
has exactly the definitional form of HistoryCompilation.rewireCircuit. -/
lemma rewire_generated (classical : FLListClosure) (grammar : InstructionDescriptionClosure)
    {G : EffectiveGateSet} {α : Type} {q r : α → ℕ} (encode : α → Input)
    (e : ∀ a, Fin (q a) ≃ Fin (r a)) (C : ∀ a, EffectiveCircuit G (q a))
    (he : LogspaceComputes encode
      (fun a => (placementOfEmbedding (e a).toEmbedding).encode))
    (hC : GeneratedCircuit encode C) :
    GeneratedCircuit encode
      (fun a => embedCircuit (placementOfEmbedding (e a).toEmbedding) (C a)) :=
  embedCircuit_generated classical grammar encode _ C he hC

/-- Turn a derivation for a constructed actual list into a recipe certificate. -/
lemma generated_uniform_leaf (grammar : InstructionDescriptionClosure)
    {G : EffectiveGateSet} {α : Type} {q : α → ℕ} (encode : α → Input)
    (header : α → ℕ) (C : ∀ a, EffectiveCircuit G (q a))
    (hheader : LogspaceComputes encode (fun a => encodeNat (header a)))
    (hC : GeneratedCircuit encode C) :
    UniformRecipe encode header (.leaf C) :=
  .leaf (generated_logspace grammar encode header C hheader hC)

/-- Actual final target encoding, including its mixed-register header, gate
count, literal native payloads and physical positions. -/
theorem readoutCircuit_logspace (classical : FLListClosure) (grammar : InstructionDescriptionClosure)
    {G : EffectiveGateSet} {conv : GateConvention G} (primitive : PrimitiveDescriptionConvention conv)
    {α : Type} {q : α → ℕ} (encode : α → Input)
    (C : ∀ a, EffectiveCircuit G (q a))
    (hC : GeneratedCircuit encode C)
    (hq : LogspaceComputes encode (fun a => encodeNat (q a))) :
    LogspaceComputes encode (fun a => (readoutCircuit conv (C a)).encode) :=
  generated_logspace grammar encode q _ hq (readoutCircuit_generated classical primitive encode C hC hq)

/-- Existing machine certificates for a source list may be consumed directly;
no certificate for the resulting controlled or adjoint whole family is an input. -/
theorem adjointCircuit_logspace (classical : FLListClosure) (grammar : InstructionDescriptionClosure)
    {G : EffectiveGateSet} {conv : GateConvention G} (primitive : PrimitiveDescriptionConvention conv)
    {α : Type} {q : α → ℕ} (encode : α → Input) (header : α → ℕ)
    (C : ∀ a, EffectiveCircuit G (q a))
    (hheader : LogspaceComputes encode (fun a => encodeNat (header a)))
    (hC : LogspaceComputes encode (fun a => encodeGateList (header a) (C a))) :
    LogspaceComputes encode (fun a => encodeGateList (header a) (adjointCircuit conv (C a))) :=
  generated_logspace grammar encode header _ hheader
    (adjointCircuit_generated classical primitive encode C
      (generated_of_logspace grammar encode header C hC))

theorem controlledCircuit_logspace (classical : FLListClosure) (grammar : InstructionDescriptionClosure)
    {G : EffectiveGateSet} {conv : GateConvention G} (primitive : PrimitiveDescriptionConvention conv)
    {α : Type} {q : α → ℕ} (encode : α → Input) (inputHeader outputHeader : α → ℕ)
    (C : ∀ a, EffectiveCircuit G (q a))
    (hheader : LogspaceComputes encode (fun a => encodeNat (outputHeader a)))
    (hC : LogspaceComputes encode (fun a => encodeGateList (inputHeader a) (C a))) :
    LogspaceComputes encode (fun a => encodeGateList (outputHeader a) (controlledCircuit conv (C a))) :=
  generated_logspace grammar encode outputHeader _ hheader
    (controlledCircuit_generated classical primitive encode C
      (generated_of_logspace grammar encode inputHeader C hC))


lemma powerSelectCircuit_generated (classical : FLListClosure)
    {G : EffectiveGateSet} {conv : GateConvention G} (primitive : PrimitiveDescriptionConvention conv)
    {α : Type} {q ell : α → ℕ} (encode : α → Input)
    (index : ∀ a, Basis (ell a) → ℕ) (C : ∀ a, EffectiveCircuit G (q a))
    (hC : GeneratedCircuit encode C)
    (hwidth : LogspaceComputes encode (fun a => encodeNat (ell a) ++ encodeNat (2^(ell a))))
    (hstates : LogspaceComputes encode (fun a => encodeNat (2^(ell a))))
    (hindex : LogspaceComputes (elementContext encode (fun a => @List.ofFn Bit (ell a)))
      (fun p => encodeNat (index p.1 p.2)))
    (hpoly : PolynomialBoundOn (elementContext encode (fun a => @List.ofFn Bit (ell a)))
      (fun p => index p.1 p.2)) :
    GeneratedCircuit encode (fun a => powerSelectCircuit conv (index a) (C a)) := by
  let ctx := elementContext encode (fun a => @List.ofFn Bit (ell a))
  have hbase : GeneratedCircuit ctx (fun p => C p.1) :=
    hC.pullback classical ctx encode Sigma.fst C (classical.strings.contextLeft _ _)
  have hpowers := repeatCircuit_generated classical ctx (fun p => C p.1)
    (fun p => index p.1 p.2) hbase hindex hpoly
  exact selectCircuit_generated classical primitive encode _ hwidth hstates hpowers

lemma phaseEstimationCircuit_generated (classical : FLListClosure)
    {G : EffectiveGateSet} {conv : GateConvention G} (primitive : PrimitiveDescriptionConvention conv)
    {α : Type} {q ell : α → ℕ} (encode : α → Input)
    (index : ∀ a, Basis (ell a) → ℕ) (walk : ∀ a, EffectiveCircuit G (q a))
    (fourier : ∀ a, EffectiveCircuit G (ell a+q a))
    (hwalk : GeneratedCircuit encode walk) (hfourier : GeneratedCircuit encode fourier)
    (hwidth : LogspaceComputes encode (fun a => encodeNat (ell a) ++ encodeNat (2^(ell a))))
    (hstates : LogspaceComputes encode (fun a => encodeNat (2^(ell a))))
    (hindex : LogspaceComputes (elementContext encode (fun a => @List.ofFn Bit (ell a)))
      (fun p => encodeNat (index p.1 p.2)))
    (hpoly : PolynomialBoundOn (elementContext encode (fun a => @List.ofFn Bit (ell a)))
      (fun p => index p.1 p.2)) :
    GeneratedCircuit encode (fun a => phaseEstimationCircuit conv (index a) (walk a) (fourier a)) :=
  append_generated classical encode _ _
    (append_generated classical encode _ _ hfourier
      (powerSelectCircuit_generated classical primitive encode index walk hwalk hwidth hstates hindex hpoly))
    (adjointCircuit_generated classical primitive encode fourier hfourier)

end Paper25.OperationalModel.UniformCompilation
