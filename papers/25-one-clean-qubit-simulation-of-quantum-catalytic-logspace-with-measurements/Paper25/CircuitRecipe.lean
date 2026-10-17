import Paper25.EffectiveCircuitModel

/-!
# Explicit gate-list recipes and a narrow external FL interface

Recipes below only concatenate actual local gate lists or enumerate finite
indexed bodies. Their interpretation is a concrete list, and target acceptance
continues to be the Born probability of its density semantics.

`RecipeDescriptionClosure` is an explicit external classical-complexity input:
closure of polynomial-time logspace transducers under description concatenation
and a fixed nesting of polynomially bounded indexed loops. It asserts no
quantum matrix equality, approximation theorem, catalytic reduction, spectral
filter, or source-to-target simulation. In particular the paper-specific recipe,
its leaf circuits, its resource bounds and its correctness remain obligations.

The loop input code is fixed here: unary length, original input bytes, unary
loop index. The external interface receives actual machines for the header,
bound, and body descriptions, and a polynomial bound on the loop count.
-/
noncomputable section
namespace Paper25.OperationalModel

/-- Restriction of a genuine finite-transducer computation to an explicitly
encoded domain. At the outermost level the encoding is the identity on input
strings. Indexed contexts use `indexedInput` below. -/
def LogspaceComputes {α : Type} (encode : α → Input) (output : α → Input) : Prop :=
  ∃ (M : Transducer) (spaceConst timeConst degree : ℕ),
    ∀ a, let x := encode a
      let capacity := spaceConst * (Nat.log2 (x.length + 2) + 1)
      let r := M.run (timeConst * (x.length + 1) ^ degree) (M.initial x capacity)
      M.halt r.1.control = true ∧ r.2 = output a

lemma logspaceComputes_id (f : Input → Input) :
    LogspaceComputes id f ↔ LogspaceGenerates f := Iff.rfl

def PolynomialBoundOn {α : Type} (encode : α → Input) (f : α → ℕ) : Prop :=
  ∃ C d : ℕ, ∀ a, f a ≤ C * ((encode a).length + 1) ^ d

/-- A fixed self-delimiting context encoding; there is no user-supplied decoder
or arbitrary compilation certificate at an indexed call. -/
def indexedInput {α : Type} (encode : α → Input) (count : α → ℕ)
    (a : Σ a : α, Fin (count a)) : Input :=
  encodeNat (encode a.1).length ++ encode a.1 ++ encodeNat a.2.val

/-- The caller's register header is followed by an actual gate count and every
explicit gate payload and placement. For target circuits the header is exactly
the number of mixed qubits. -/
def encodeGateList {G : EffectiveGateSet} {q : ℕ} (header : ℕ)
    (gates : EffectiveCircuit G q) : Input :=
  encodeNat header ++ encodeNat gates.length ++ (gates.map EffectiveLocalGate.encode).flatten

/-- A fixed finite template. Polynomially many loop iterations are represented
by `loop`; input-dependent local operations occur in leaf families, whose exact
printed gate descriptions require their own logspace certificates. -/
inductive CircuitRecipe (G : EffectiveGateSet) : (α : Type) → (α → ℕ) → Type 1 where
  | leaf {α : Type} {q : α → ℕ} (gates : ∀ a, EffectiveCircuit G (q a)) :
      CircuitRecipe G α q
  | append {α : Type} {q : α → ℕ} (left right : CircuitRecipe G α q) :
      CircuitRecipe G α q
  | loop {α : Type} {q : α → ℕ} (count : α → ℕ)
      (body : CircuitRecipe G (Σ a : α, Fin (count a)) (fun a => q a.1)) :
      CircuitRecipe G α q

def CircuitRecipe.gates {G : EffectiveGateSet} :
    {α : Type} → {q : α → ℕ} → CircuitRecipe G α q → (a : α) → EffectiveCircuit G (q a)
  | _, _, .leaf gates, a => gates a
  | _, _, .append left right, a => left.gates a ++ right.gates a
  | _, _, .loop count body, a => (List.ofFn (fun i : Fin (count a) => body.gates ⟨a, i⟩)).flatten

lemma CircuitRecipe.gates_append {G : EffectiveGateSet} {α : Type} {q : α → ℕ}
    (left right : CircuitRecipe G α q) (a : α) :
    (CircuitRecipe.append left right).gates a = left.gates a ++ right.gates a := rfl

lemma CircuitRecipe.gates_loop {G : EffectiveGateSet} {α : Type} {q : α → ℕ}
    (count : α → ℕ) (body : CircuitRecipe G (Σ a, Fin (count a)) (fun a => q a.1)) (a : α) :
    (CircuitRecipe.loop count body).gates a =
      (List.ofFn (fun i : Fin (count a) => body.gates ⟨a, i⟩)).flatten := rfl

lemma CircuitRecipe.matrix_append {G : EffectiveGateSet} {α : Type} {q : α → ℕ}
    (left right : CircuitRecipe G α q) (a : α) :
    ((CircuitRecipe.append left right).gates a).matrix =
      (right.gates a).matrix * (left.gates a).matrix :=
  EffectiveCircuit.matrix_append _ _

lemma CircuitRecipe.gateCount_append {G : EffectiveGateSet} {α : Type} {q : α → ℕ}
    (left right : CircuitRecipe G α q) (a : α) :
    ((CircuitRecipe.append left right).gates a).length =
      (left.gates a).length + (right.gates a).length := List.length_append

lemma CircuitRecipe.gateCount_loop {G : EffectiveGateSet} {α : Type} {q : α → ℕ}
    (count : α → ℕ) (body : CircuitRecipe G (Σ a, Fin (count a)) (fun a => q a.1)) (a : α) :
    ((CircuitRecipe.loop count body).gates a).length =
      ((List.ofFn (fun i : Fin (count a) =>
        (show EffectiveCircuit G (q a) from body.gates ⟨a, i⟩))).map
          (fun gates : EffectiveCircuit G (q a) => gates.length)).sum := by
  simp only [CircuitRecipe.gates, List.length_flatten]

/-- The only unformalized generic input in this module. These are standard
classical FL closure statements on explicit strings, not quantum compilation
or semantic correctness assumptions. Each invocation retains its component
machine hypotheses and its polynomial bound on loop iterations. -/
structure RecipeDescriptionClosure : Prop where
  append : ∀ {G : EffectiveGateSet} {α : Type} (encode : α → Input) (header q : α → ℕ)
    (left right : ∀ a, EffectiveCircuit G (q a)),
    LogspaceComputes encode (fun a => encodeGateList (header a) (left a)) →
    LogspaceComputes encode (fun a => encodeGateList (header a) (right a)) →
    LogspaceComputes encode (fun a => encodeGateList (header a) (left a ++ right a))
  loop : ∀ {G : EffectiveGateSet} {α : Type} (encode : α → Input) (header q count : α → ℕ)
    (body : ∀ a : Σ a : α, Fin (count a), EffectiveCircuit G (q a.1)),
    LogspaceComputes encode (fun a => encodeNat (header a)) →
    LogspaceComputes encode (fun a => encodeNat (count a)) →
    PolynomialBoundOn encode count →
    LogspaceComputes (indexedInput encode count)
      (fun a => encodeGateList (header a.1) (body a)) →
    LogspaceComputes encode (fun a => encodeGateList (header a)
      ((List.ofFn (fun i : Fin (count a) => body ⟨a, i⟩)).flatten))

/-- Uniformity derivations mirror the recipe template. There is one constructor
for an already generated actual primitive list, and only the two generic string
operations listed in `RecipeDescriptionClosure`. -/
inductive UniformRecipe {G : EffectiveGateSet} :
    {α : Type} → {q : α → ℕ} → (α → Input) → (α → ℕ) → CircuitRecipe G α q → Prop where
  | leaf {α : Type} {q : α → ℕ} {encode : α → Input} {header : α → ℕ}
      {gates : ∀ a, EffectiveCircuit G (q a)}
      (generated : LogspaceComputes encode (fun a => encodeGateList (header a) (gates a))) :
      UniformRecipe encode header (.leaf gates)
  | append {α : Type} {q : α → ℕ} {encode : α → Input} {header : α → ℕ}
      {left right : CircuitRecipe G α q}
      (leftUniform : UniformRecipe encode header left)
      (rightUniform : UniformRecipe encode header right) :
      UniformRecipe encode header (.append left right)
  | loop {α : Type} {q : α → ℕ} {encode : α → Input} {header count : α → ℕ}
      {body : CircuitRecipe G (Σ a, Fin (count a)) (fun a => q a.1)}
      (headerUniform : LogspaceComputes encode (fun a => encodeNat (header a)))
      (countUniform : LogspaceComputes encode (fun a => encodeNat (count a)))
      (countPolynomial : PolynomialBoundOn encode count)
      (bodyUniform : UniformRecipe (indexedInput encode count) (fun a => header a.1) body) :
      UniformRecipe encode header (.loop count body)

/-- The external input is used only to assemble already specified descriptions;
the resulting object is still the actual interpreted gate list. -/
theorem UniformRecipe.generates (externalClosure : RecipeDescriptionClosure)
    {G : EffectiveGateSet} {α : Type} {q : α → ℕ} {encode : α → Input} {header : α → ℕ}
    {recipe : CircuitRecipe G α q} (uniform : UniformRecipe encode header recipe) :
    LogspaceComputes encode (fun a => encodeGateList (header a) (recipe.gates a)) := by
  induction uniform with
  | leaf generated => exact generated
  | append leftUniform rightUniform leftGenerated rightGenerated =>
    exact externalClosure.append _ _ _ _ _ leftGenerated rightGenerated
  | loop headerUniform countUniform countPolynomial bodyUniform bodyGenerated =>
    exact externalClosure.loop _ _ _ _ _ headerUniform countUniform countPolynomial bodyGenerated

/-- An explicit interface for a *particular* generic primitive implementation.
A published primitive theorem can support its semantic and cost fields only
under its original hypotheses. The separate `generated` field still requires
a genuine description generator; it cannot be inferred from gate counts. This record itself asserts no
existence theorem and is not an interface for the paper's full simulation.
Equality includes scalar phase, and the circuit contains no qubits beyond `q`.
Descriptions and cost refer to the actual returned local gate lists. -/
structure ExactPrimitiveImplementation {G : EffectiveGateSet} {α : Type}
    (encode : α → Input) (header q : α → ℕ) (ideal : ∀ a, Operator (q a)) where
  gates : ∀ a, EffectiveCircuit G (q a)
  matrix_eq : ∀ a, (gates a).matrix = ideal a
  generated : LogspaceComputes encode (fun a => encodeGateList (header a) (gates a))
  gatePolynomial : PolynomialBoundOn encode (fun a => (gates a).length)

def ExactPrimitiveImplementation.recipe {G : EffectiveGateSet} {α : Type}
    {encode : α → Input} {header q : α → ℕ} {ideal : ∀ a, Operator (q a)}
    (implementation : ExactPrimitiveImplementation (G := G) encode header q ideal) : CircuitRecipe G α q :=
  .leaf implementation.gates

lemma ExactPrimitiveImplementation.uniform {G : EffectiveGateSet} {α : Type}
    {encode : α → Input} {header q : α → ℕ} {ideal : ∀ a, Operator (q a)}
    (implementation : ExactPrimitiveImplementation (G := G) encode header q ideal) :
    UniformRecipe encode header implementation.recipe := .leaf implementation.generated

lemma ExactPrimitiveImplementation.recipe_matrix {G : EffectiveGateSet} {α : Type}
    {encode : α → Input} {header q : α → ℕ} {ideal : ∀ a, Operator (q a)}
    (implementation : ExactPrimitiveImplementation (G := G) encode header q ideal) (a : α) :
    (implementation.recipe.gates a).matrix = ideal a := implementation.matrix_eq a

/-- An assembly endpoint for the paper. To use it one must provide the actual
recipe, its leaf/uniformity derivation, and its actual gate/qubit resource bounds.
It does not assume or return any desired bias or matrix equality. -/
def CircuitRecipe.targetFamily {G : EffectiveGateSet} (externalClosure : RecipeDescriptionClosure)
    (mixed : Input → ℕ) (recipe : CircuitRecipe G Input (fun x => mixed x + 1))
    (uniform : UniformRecipe id mixed recipe)
    (mixedPolynomial : PolynomialBound mixed)
    (gatePolynomial : PolynomialBound (fun x => (recipe.gates x).length)) : EffectiveTargetFamily G where
  circuit x := { mixedQubits := mixed x, gates := recipe.gates x }
  uniform := uniform.generates externalClosure
  mixed_polynomial := mixedPolynomial
  gates_polynomial := gatePolynomial

lemma CircuitRecipe.targetFamily_gates {G : EffectiveGateSet}
    (externalClosure : RecipeDescriptionClosure) (mixed : Input → ℕ)
    (recipe : CircuitRecipe G Input (fun x => mixed x + 1))
    (uniform : UniformRecipe id mixed recipe) (hm : PolynomialBound mixed)
    (hg : PolynomialBound (fun x => (recipe.gates x).length)) (x : Input) :
    ((recipe.targetFamily externalClosure mixed uniform hm hg).circuit x).gates = recipe.gates x := rfl


/-- Fixed tuple encodings for the generic classical arithmetic interface. -/
def encodeRationalPair (a : ℚ × ℚ) : Input :=
  encodeNat (encodeRational a.1).length ++ encodeRational a.1 ++ encodeRational a.2

def encodeBool (b : Bool) : Input := [if b then 1 else 0]

/-- Standard external FL closure and rational-arithmetic inputs only. This
record has no paper-specific angle, label, source channel, or matrix operation.
Arithmetic acts on explicit unreduced signed fractions; it never requests
canonicalization or a gcd. Division returns raw zero for a zero divisor;
error applications retain their nonzero-denominator proofs separately. -/
structure ClassicalDescriptionClosure : Prop where
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
  pair : ∀ {α : Type} (encode : α → Input) (f g : α → Input),
    LogspaceComputes encode f → LogspaceComputes encode g →
    LogspaceComputes encode (fun a => encodeNat (f a).length ++ f a ++ g a)
  conditional : ∀ {α : Type} (encode : α → Input) (p : α → Bool) (f g : α → Input),
    LogspaceComputes encode (fun a => encodeBool (p a)) →
    LogspaceComputes encode f → LogspaceComputes encode g →
    LogspaceComputes encode (fun a => if p a then f a else g a)
  rationalAdd : LogspaceComputes encodeRationalRepPair (fun a => (a.1.add a.2).encode)
  rationalSub : LogspaceComputes encodeRationalRepPair (fun a => (a.1.sub a.2).encode)
  rationalMul : LogspaceComputes encodeRationalRepPair (fun a => (a.1.mul a.2).encode)
  rationalDiv : LogspaceComputes encodeRationalRepPair (fun a => (a.1.div a.2).encode)
  rationalLess : LogspaceComputes encodeRationalRepPair (fun a => encodeBool (a.1.less a.2))


end Paper25.OperationalModel
