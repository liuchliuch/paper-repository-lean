import Paper25.OneCleanQubit
import Paper25.SourceChannels

/-!
# Finite local circuits and their operational semantics

The models in this file describe the fixed finite gate alphabet submodel. The
paper's effective parameter gate convention is modeled separately in
`EffectiveCircuitModel`. These models contain gate lists, wire
placements, density operators, and a Born-rule acceptance probability. Inputs
are finite binary strings. The uniformity predicate below uses an actual
finite-control, read-only-input, binary-work-tape transducer. No compilation or
uniformity theorem for the paper's simulator is asserted here.
-/

noncomputable section
open scoped ComplexOrder
open Matrix
namespace Paper25.OperationalModel

abbrev Bit := Fin 2
abbrev Input := List Bit
abbrev Basis (q : ℕ) := Fin q → Bit
abbrev Operator (q : ℕ) := Matrix (Basis q) (Basis q) ℂ

lemma card_basis (q : ℕ) : Fintype.card (Basis q) = 2 ^ q := by simp [Basis]

/-- A fixed finite alphabet. The local dimension and every legal gate matrix are
fixed before the input is supplied. -/
structure GateSet where
  symbols : ℕ
  arity : Fin symbols → ℕ
  locality : ℕ
  arity_le : ∀ a, arity a ≤ locality
  matrix : (a : Fin symbols) → Operator (arity a)
  unitary : ∀ a, OneCleanQubit.Unitary (matrix a)

/-- A placement is a permutation of qubit *positions*. Consequently it cannot
hide an arbitrary unitary change of basis in a supposed local gate. -/
structure Placement (q k : ℕ) where
  enough : k ≤ q
  wires : Fin k ⊕ Fin (q - k) ≃ Fin q

/-- Split a computational-basis string along the specified wire partition. -/
def Placement.split {q k : ℕ} (p : Placement q k) :
    Basis q ≃ (Basis k × Basis (q - k)) where
  toFun f := (fun i => f (p.wires (Sum.inl i)), fun j => f (p.wires (Sum.inr j)))
  invFun f := fun i => Sum.elim f.1 f.2 (p.wires.symm i)
  left_inv f := by
    funext i
    have h := p.wires.apply_symm_apply i
    rcases hsplit : p.wires.symm i with j | j
    · simpa only [hsplit] using congrArg f h
    · simpa only [hsplit] using congrArg f h
  right_inv f := by
    rcases f with ⟨f, g⟩
    apply Prod.ext <;> funext i <;> simp

/-- Extend a k-qubit operator by identity and permute only the wire positions. -/
def Placement.lift {q k : ℕ} (p : Placement q k) (U : Operator k) : Operator q :=
  (Matrix.kronecker U (1 : Operator (q - k))).submatrix p.split p.split

lemma Placement.lift_apply {q k : ℕ} (p : Placement q k) (U : Operator k)
    (i j : Basis q) : p.lift U i j =
    U (p.split i).1 (p.split j).1 *
      (if (p.split i).2 = (p.split j).2 then 1 else 0) := by
  simp [Placement.lift, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply]

lemma unitary_submatrix {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (e : a ≃ b) (U : Matrix b b ℂ)
    (hU : OneCleanQubit.Unitary U) : OneCleanQubit.Unitary (U.submatrix e e) := by
  constructor <;>
    simp only [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  · rw [hU.1, Matrix.submatrix_one_equiv]
  · rw [hU.2, Matrix.submatrix_one_equiv]

lemma trace_submatrix_equiv {a b : Type*} [Fintype a] [Fintype b]
    (e : a ≃ b) (U : Matrix b b ℂ) : Matrix.trace (U.submatrix e e) = Matrix.trace U := by
  exact e.bijective.sum_comp (fun i => U i i)

lemma Placement.lift_unitary {q k : ℕ} (p : Placement q k) (U : Operator k)
    (hU : OneCleanQubit.Unitary U) : OneCleanQubit.Unitary (p.lift U) := by
  apply unitary_submatrix
  constructor <;>
    simp only [Matrix.kronecker, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, one_mul]
  · rw [hU.1, Matrix.one_kronecker_one]
  · rw [hU.2, Matrix.one_kronecker_one]

structure LocalGate (G : GateSet) (q : ℕ) where
  symbol : Fin G.symbols
  placement : Placement q (G.arity symbol)

def LocalGate.matrix {G : GateSet} {q : ℕ} (g : LocalGate G q) : Operator q :=
  g.placement.lift (G.matrix g.symbol)

lemma LocalGate.unitary {G : GateSet} {q : ℕ} (g : LocalGate G q) :
    OneCleanQubit.Unitary g.matrix := g.placement.lift_unitary _ (G.unitary g.symbol)

/-- The list is in chronological order. -/
abbrev Circuit (G : GateSet) (q : ℕ) := List (LocalGate G q)

def Circuit.matrix {G : GateSet} {q : ℕ} : Circuit G q → Operator q
  | [] => 1
  | g :: gs => Circuit.matrix gs * g.matrix

lemma Circuit.unitary {G : GateSet} {q : ℕ} (C : Circuit G q) :
    OneCleanQubit.Unitary C.matrix := by
  induction C with
  | nil => constructor <;> simp [Circuit.matrix]
  | cons g gs ih => exact OneCleanQubit.unitary_mul ih g.unitary

/-- Execution applies every gate to the density, in list order. -/
def Circuit.run {G : GateSet} {q : ℕ} : Circuit G q → Operator q → Operator q
  | [], ρ => ρ
  | g :: gs, ρ => Circuit.run gs (OneCleanQubit.evolve g.matrix ρ)

lemma Circuit.run_eq_evolve {G : GateSet} {q : ℕ} (C : Circuit G q) (ρ : Operator q) :
    C.run ρ = OneCleanQubit.evolve C.matrix ρ := by
  induction C generalizing ρ with
  | nil => simp [Circuit.run, Circuit.matrix, OneCleanQubit.evolve]
  | cons g gs ih =>
    rw [Circuit.run, ih, Circuit.matrix, OneCleanQubit.evolve_comp]

lemma Circuit.run_posSemidef {G : GateSet} {q : ℕ} (C : Circuit G q) (ρ : Operator q)
    (hρ : ρ.PosSemidef) : (C.run ρ).PosSemidef := by
  rw [C.run_eq_evolve]
  exact OneCleanQubit.evolve_posSemidef _ _ hρ

lemma Circuit.run_trace {G : GateSet} {q : ℕ} (C : Circuit G q) (ρ : Operator q) :
    Matrix.trace (C.run ρ) = Matrix.trace ρ := by
  rw [C.run_eq_evolve]
  exact OneCleanQubit.evolve_trace _ _ C.unitary

lemma Circuit.matrix_append {G : GateSet} {q : ℕ} (C D : Circuit G q) :
    (C ++ D).matrix = D.matrix * C.matrix := by
  induction C with
  | nil => simp [Circuit.matrix]
  | cons g gs ih => simp only [List.cons_append, Circuit.matrix, ih, mul_assoc]

lemma evolve_submatrix {a b : Type*} [Fintype a] [Fintype b]
    (e : a ≃ b) (U ρ : Matrix b b ℂ) :
    OneCleanQubit.evolve (U.submatrix e e) (ρ.submatrix e e) =
      (OneCleanQubit.evolve U ρ).submatrix e e := by
  simp only [OneCleanQubit.evolve, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv]

/-- Separate the first physical qubit from the remaining m qubits. -/
def probeTensor (m : ℕ) : Basis (m + 1) ≃ (Bit × Basis m) where
  toFun f := (f 0, fun i => f i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := by funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv p := by rcases p with ⟨i, f⟩; rfl

/-- Identification with the already proved one-clean-qubit density semantics. -/
def probeBasis (m : ℕ) : Basis (m + 1) ≃ (Basis m ⊕ Basis m) :=
  (probeTensor m).trans OneCleanQubit.tensorBasis

/-- A target circuit contains exactly one clean initial qubit. The acceptance
probability is computed from the final density; it is not an independent field. -/
structure TargetCircuit (G : GateSet) where
  mixedQubits : ℕ
  gates : Circuit G (mixedQubits + 1)

def TargetCircuit.matrix {G : GateSet} (C : TargetCircuit G) :
    OneCleanQubit.ProbeMatrix (Basis C.mixedQubits) :=
  C.gates.matrix.submatrix (probeBasis C.mixedQubits).symm (probeBasis C.mixedQubits).symm

lemma TargetCircuit.unitary {G : GateSet} (C : TargetCircuit G) :
    OneCleanQubit.Unitary C.matrix := unitary_submatrix _ _ C.gates.unitary

def TargetCircuit.output {G : GateSet} (C : TargetCircuit G) :
    OneCleanQubit.ProbeMatrix (Basis C.mixedQubits) :=
  OneCleanQubit.evolve C.matrix OneCleanQubit.input

def TargetCircuit.accept {G : GateSet} (C : TargetCircuit G) : ℝ :=
  OneCleanQubit.probZero C.output

def TargetCircuit.gateCount {G : GateSet} (C : TargetCircuit G) : ℕ := C.gates.length

/-- Initial density in the physical qubit-string basis. -/
def TargetCircuit.inputPhysical {G : GateSet} (C : TargetCircuit G) :
    Operator (C.mixedQubits + 1) :=
  (OneCleanQubit.input : OneCleanQubit.ProbeMatrix (Basis C.mixedQubits)).submatrix
    (probeBasis C.mixedQubits) (probeBasis C.mixedQubits)

lemma TargetCircuit.inputPhysical_posSemidef {G : GateSet} (C : TargetCircuit G) :
    C.inputPhysical.PosSemidef :=
  OneCleanQubit.input_posSemidef.submatrix (probeBasis C.mixedQubits)

lemma TargetCircuit.inputPhysical_trace {G : GateSet} (C : TargetCircuit G) :
    Matrix.trace C.inputPhysical = 1 := by
  rw [TargetCircuit.inputPhysical, trace_submatrix_equiv, OneCleanQubit.input_trace]

/-- The readout density is exactly the result of running the actual gate list. -/
lemma TargetCircuit.run_eq_output {G : GateSet} (C : TargetCircuit G) :
    C.gates.run C.inputPhysical = C.output.submatrix
      (probeBasis C.mixedQubits) (probeBasis C.mixedQubits) := by
  rw [C.gates.run_eq_evolve]
  rw [TargetCircuit.output, ← evolve_submatrix]
  congr 1
  ext i j
  simp [TargetCircuit.matrix, Matrix.submatrix_apply]

lemma TargetCircuit.output_posSemidef {G : GateSet} (C : TargetCircuit G) :
    C.output.PosSemidef := OneCleanQubit.evolve_posSemidef _ _ OneCleanQubit.input_posSemidef

lemma TargetCircuit.output_trace {G : GateSet} (C : TargetCircuit G) :
    Matrix.trace C.output = 1 := by
  rw [TargetCircuit.output, OneCleanQubit.evolve_trace _ _ C.unitary,
    OneCleanQubit.input_trace]

lemma TargetCircuit.accept_mem_unitInterval {G : GateSet} (C : TargetCircuit G) :
    0 ≤ C.accept ∧ C.accept ≤ 1 := by
  have h0 := OneCleanQubit.probZero_nonneg C.output C.output_posSemidef
  have h1 := OneCleanQubit.probOne_nonneg C.output C.output_posSemidef
  have hs := OneCleanQubit.measurement_sum C.output
  rw [C.output_trace] at hs
  simp only [Complex.one_re] at hs
  exact ⟨h0, by dsimp [TargetCircuit.accept]; linarith⟩


/-- Relabel every Kraus operator by an honest computational-basis equivalence. -/
def relabelChannel {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (e : a ≃ b) (C : KrausChannel b) : KrausChannel a where
  Outcome := C.Outcome
  outcomes := C.outcomes
  kraus r := (C.kraus r).submatrix e e
  complete := by
    simp only [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
    calc
      (∑ r, ((C.kraus r).conjTranspose * C.kraus r).submatrix e e) =
          (∑ r, (C.kraus r).conjTranspose * C.kraus r).submatrix e e := by
        ext i j
        simp only [Matrix.sum_apply, Matrix.submatrix_apply]
      _ = 1 := by rw [C.complete, Matrix.submatrix_one_equiv]

lemma relabelChannel_act {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (e : a ≃ b) (C : KrausChannel b)
    (X : Matrix b b ℂ) :
    (relabelChannel e C).act (X.submatrix e e) = (C.act X).submatrix e e := by
  simp only [KrausChannel.act, relabelChannel, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv]
  ext i j
  simp only [Matrix.sum_apply, Matrix.submatrix_apply]

/-- Place an arbitrary local channel on specified physical wires. -/
def Placement.liftChannel {q k : ℕ} (p : Placement q k)
    (C : KrausChannel (Basis k)) : KrausChannel (Basis q) :=
  relabelChannel p.split (C.extendRight (Basis (q - k)))

def oneBit : Basis 1 ≃ Bit where
  toFun f := f 0
  invFun b := fun _ => b
  left_inv f := by funext i; fin_cases i; rfl
  right_inv b := rfl

/-- Actual source primitives: a local unitary, computational-basis dephasing,
and reset to zero. A classical measurement transcript can be stored in source
work qubits using the explicit measurement channel in `SourceChannels`. -/
inductive SourceOp (G : GateSet) (q : ℕ) where
  | gate (g : LocalGate G q)
  | dephase (p : Placement q 1)
  | reset (p : Placement q 1)
  | measurement (p : Placement q 2)

def SourceOp.channel {G : GateSet} {q : ℕ} : SourceOp G q → KrausChannel (Basis q)
  | .gate g => KrausChannel.unitary g.matrix g.unitary.1
  | .dephase p => p.liftChannel (relabelChannel oneBit KrausChannel.dephase)
  | .reset p => p.liftChannel (relabelChannel oneBit KrausChannel.reset)
  | .measurement p =>
    p.liftChannel (relabelChannel (finTwoArrowEquiv Bit) KrausChannel.measurement)

abbrev SourceCircuit (G : GateSet) (q : ℕ) := List (SourceOp G q)

def SourceCircuit.channel {G : GateSet} {q : ℕ} :
    SourceCircuit G q → KrausChannel (Basis q)
  | [] => KrausChannel.identity
  | g :: gs => (SourceCircuit.channel gs).comp g.channel

def SourceCircuit.run {G : GateSet} {q : ℕ} : SourceCircuit G q → Operator q → Operator q
  | [], ρ => ρ
  | g :: gs, ρ => SourceCircuit.run gs (g.channel.act ρ)

lemma SourceCircuit.run_eq_channel {G : GateSet} {q : ℕ}
    (C : SourceCircuit G q) (ρ : Operator q) : C.run ρ = C.channel.act ρ := by
  induction C generalizing ρ with
  | nil => simp [SourceCircuit.run, SourceCircuit.channel]
  | cons g gs ih => rw [SourceCircuit.run, ih, SourceCircuit.channel, KrausChannel.comp_act]

lemma SourceCircuit.trace_preserving {G : GateSet} {q : ℕ}
    (C : SourceCircuit G q) (ρ : Operator q) : Matrix.trace (C.run ρ) = Matrix.trace ρ := by
  rw [C.run_eq_channel]
  exact C.channel.trace_preserving ρ

lemma SourceCircuit.run_posSemidef {G : GateSet} {q : ℕ}
    (C : SourceCircuit G q) (ρ : Operator q) (hρ : ρ.PosSemidef) :
    (C.run ρ).PosSemidef := by
  rw [C.run_eq_channel]
  exact C.channel.act_posSemidef ρ hρ

/-- An explicit self-delimiting encoding of natural numbers. -/
def encodeNat (n : ℕ) : List Bit := List.replicate n 1 ++ [0]

/-- A local gate description records the register size, arity, and ordered
active positions. The order chosen for the unused complement is absent: it has
no effect on the embedded operation and must not carry hidden description cost. -/
def Placement.encode {q k : ℕ} (p : Placement q k) : List Bit :=
  encodeNat q ++ encodeNat k ++
    (List.ofFn (fun i : Fin k => encodeNat (p.wires (Sum.inl i)).val)).flatten

lemma Placement.encode_eq_of_active_eq {q k : ℕ} (p r : Placement q k)
    (h : ∀ i, p.wires (Sum.inl i) = r.wires (Sum.inl i)) : p.encode = r.encode := by
  simp only [Placement.encode,h]

def LocalGate.encode {G : GateSet} {q : ℕ} (g : LocalGate G q) : List Bit :=
  encodeNat g.symbol.val ++ g.placement.encode

def TargetCircuit.encode {G : GateSet} (C : TargetCircuit G) : List Bit :=
  encodeNat C.mixedQubits ++ encodeNat C.gateCount ++ (C.gates.map LocalGate.encode).flatten

def SourceOp.encode {G : GateSet} {q : ℕ} : SourceOp G q → List Bit
  | .gate g => encodeNat 0 ++ g.encode
  | .dephase p => encodeNat 1 ++ p.encode
  | .reset p => encodeNat 2 ++ p.encode
  | .measurement p => encodeNat 3 ++ p.encode

/-- The source's work/catalyst partition is part of the circuit data. -/
structure SourceComputation (G : GateSet) where
  workQubits : ℕ
  catalystQubits : ℕ
  outputQubit : Fin workQubits
  gates : SourceCircuit G (workQubits + catalystQubits)

def SourceComputation.encode {G : GateSet} (C : SourceComputation G) : List Bit :=
  encodeNat C.workQubits ++ encodeNat C.catalystQubits ++ encodeNat C.outputQubit.val ++
    encodeNat C.gates.length ++
    (C.gates.map SourceOp.encode).flatten

/-- The all-zero pure state of the source work register. -/
def pureZero (q : ℕ) : Operator q := Matrix.single (fun _ => 0) (fun _ => 0) 1

def registerBasis (s c : ℕ) : Basis (s + c) ≃ (Basis s × Basis c) where
  toFun f := (fun i => f (finSumFinEquiv (Sum.inl i)),
    fun j => f (finSumFinEquiv (Sum.inr j)))
  invFun f := fun i => Sum.elim f.1 f.2 (finSumFinEquiv.symm i)
  left_inv f := by
    funext i
    have h := (finSumFinEquiv : Fin s ⊕ Fin c ≃ Fin (s + c)).apply_symm_apply i
    rcases hs : (finSumFinEquiv.symm i : Fin s ⊕ Fin c) with j | j
    · simpa only [hs] using congrArg f h
    · simpa only [hs] using congrArg f h
  right_inv f := by
    rcases f with ⟨f, g⟩
    apply Prod.ext <;> funext i <;> simp

def SourceComputation.input {G : GateSet} (C : SourceComputation G)
    (σ : Operator C.catalystQubits) : Operator (C.workQubits + C.catalystQubits) :=
  (Matrix.kronecker (pureZero C.workQubits) σ).submatrix
    (registerBasis C.workQubits C.catalystQubits)
    (registerBasis C.workQubits C.catalystQubits)

def SourceComputation.output {G : GateSet} (C : SourceComputation G)
    (σ : Operator C.catalystQubits) : Operator (C.workQubits + C.catalystQubits) :=
  C.gates.run (C.input σ)

/-- Final computational-basis measurement on the specified source work qubit. -/
def SourceComputation.accept {G : GateSet} (C : SourceComputation G)
    (σ : Operator C.catalystQubits) : ℝ :=
  ∑ b : Basis (C.workQubits + C.catalystQubits),
    if b (Fin.castAdd C.catalystQubits C.outputQubit) = 1 then (C.output σ b b).re else 0

/-- Reassociate only the work/catalyst/reference tensor factors. -/
def SourceComputation.referenceBasis {G : GateSet} (C : SourceComputation G) (r : Type*) :
    (Basis (C.workQubits + C.catalystQubits) × r) ≃
      (Basis C.workQubits × (Basis C.catalystQubits × r)) :=
  (Equiv.prodCongr (registerBasis C.workQubits C.catalystQubits) (Equiv.refl r)).trans
    (Equiv.prodAssoc _ _ _)

/-- Exact catalyst restoration includes arbitrary inaccessible finite references.
The initial catalyst may be entangled with that reference. -/
def SourceComputation.Restores {G : GateSet} (C : SourceComputation G) : Prop :=
  ∀ (r : Type) [Fintype r] [DecidableEq r]
    (σ : Matrix (Basis C.catalystQubits × r) (Basis C.catalystQubits × r) ℂ),
    σ.PosSemidef → Matrix.trace σ = 1 →
    let initial := (Matrix.kronecker (pureZero C.workQubits) σ).submatrix
      (C.referenceBasis r) (C.referenceBasis r)
    let final := (C.gates.channel.extendRight r).act initial
    ∀ i j : Basis C.catalystQubits × r,
      (∑ w : Basis C.workQubits,
        final ((C.referenceBasis r).symm (w, i)) ((C.referenceBasis r).symm (w, j))) = σ i j

/-- A head moves at most one cell in a transition. -/
inductive HeadMove where
  | left | stay | right
  deriving DecidableEq

/-- Input endmarkers are distinguishable from data bits. -/
inductive InputSymbol where
  | leftEnd | bit (b : Bit) | rightEnd
  deriving DecidableEq

def moveHead {n : ℕ} (h : Fin (n + 1)) : HeadMove → Fin (n + 1)
  | .left => ⟨h.val - 1, by omega⟩
  | .stay => h
  | .right => ⟨min (h.val + 1) n, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

/-- A transition reads one input symbol and one work bit. Its finite output
alphabet contains only a single optional output bit. -/
structure Transition (states : ℕ) where
  next : Fin states
  inputMove : HeadMove
  workMove : HeadMove
  write : Bit
  emit : Option Bit

/-- A fixed finite transition table; no input-dependent function is hidden in
an emission or a gate instruction. -/
structure Transducer where
  states : ℕ
  start : Fin states
  halt : Fin states → Bool
  table : Fin states → InputSymbol → Bit → Transition states

structure Configuration (M : Transducer) (x : Input) (space : ℕ) where
  control : Fin M.states
  inputHead : Fin (x.length + 2)
  workHead : Fin (space + 1)
  workTape : Fin (space + 1) → Bit

def inputSymbol (x : Input) (head : Fin (x.length + 2)) : InputSymbol :=
  if head.val = 0 then .leftEnd else
    match x[head.val - 1]? with
    | some b => .bit b
    | none => .rightEnd

def Transducer.initial (M : Transducer) (x : Input) (space : ℕ) : Configuration M x space where
  control := M.start
  inputHead := ⟨0, by omega⟩
  workHead := ⟨0, by omega⟩
  workTape := fun _ => 0

/-- The work tape is the only mutable storage; output is write-only. -/
def Transducer.step (M : Transducer) {x : Input} {space : ℕ}
    (c : Configuration M x space) : Configuration M x space × Option Bit :=
  if M.halt c.control then (c, none) else
    let a := M.table c.control (inputSymbol x c.inputHead) (c.workTape c.workHead)
    ({ control := a.next
       inputHead := moveHead c.inputHead a.inputMove
       workHead := moveHead c.workHead a.workMove
       workTape := Function.update c.workTape c.workHead a.write }, a.emit)

/-- Exact replay of a bounded deterministic run, including every output bit. -/
def Transducer.run (M : Transducer) {x : Input} {space : ℕ} :
    ℕ → Configuration M x space → Configuration M x space × List Bit
  | 0, c => (c, [])
  | t + 1, c =>
    let s := M.step c
    let r := M.run t s.1
    (r.1, s.2.toList ++ r.2)

lemma Transducer.run_output_length_le (M : Transducer) {x : Input} {space : ℕ}
    (t : ℕ) (c : Configuration M x space) : (M.run t c).2.length ≤ t := by
  induction t generalizing c with
  | zero => simp [Transducer.run]
  | succ t ih =>
    have hout : (M.step c).2.toList.length ≤ 1 := by cases (M.step c).2 <;> simp
    have hrest := ih (M.step c).1
    simpa only [Transducer.run, List.length_append, Nat.add_comm 1 t] using
      Nat.add_le_add hout hrest

lemma canonical_workCells_logarithmic (C n : ℕ) :
    C * (Nat.log2 (n + 2) + 1) + 1 ≤ (C + 1) * (Nat.log2 (n + 2) + 1) := by
  nlinarith [Nat.zero_le (Nat.log2 (n + 2))]

/-- Uniformity is witnessed by one fixed local transition table, logarithmic
binary work storage, a polynomial step bound, exact output, and halting.
In particular this is not a field asserting the desired target circuit exists. -/
def LogspaceGenerates (encoding : Input → List Bit) : Prop :=
  ∃ (M : Transducer) (spaceConst timeConst degree : ℕ),
    ∀ x, let capacity := spaceConst * (Nat.log2 (x.length + 2) + 1)
      let r := M.run (timeConst * (x.length + 1) ^ degree) (M.initial x capacity)
      M.halt r.1.control = true ∧ r.2 = encoding x

def PolynomialBound (f : Input → ℕ) : Prop :=
  ∃ C d : ℕ, ∀ x, f x ≤ C * (x.length + 1) ^ d

lemma LogspaceGenerates.output_polynomial {encoding : Input → List Bit}
    (h : LogspaceGenerates encoding) : PolynomialBound (fun x => (encoding x).length) := by
  rcases h with ⟨M, C, T, d, h⟩
  refine ⟨T, d, ?_⟩
  intro x
  have hx := h x
  dsimp only at hx
  change (encoding x).length ≤ _
  rw [← hx.2]
  exact M.run_output_length_le _ _

/-- A concrete halting finite machine, useful as the base of constructions. -/
def haltMachine : Transducer where
  states := 1
  start := 0
  halt _ := true
  table _ _ _ :=
    { next := 0
      inputMove := .stay
      workMove := .stay
      write := 0
      emit := none }

lemma logspaceGenerates_empty : LogspaceGenerates (fun _ => []) := by
  refine ⟨haltMachine, 0, 0, 0, ?_⟩
  intro x
  simp [Transducer.run, haltMachine]

def LogarithmicBound (f : Input → ℕ) : Prop :=
  ∃ C : ℕ, ∀ x, f x ≤ C * (Nat.log2 (x.length + 2) + 1)

structure SourceFamily (G : GateSet) where
  circuit : Input → SourceComputation G
  restoration : ∀ x, (circuit x).Restores
  uniform : LogspaceGenerates (fun x => (circuit x).encode)
  work_logarithmic : LogarithmicBound (fun x => (circuit x).workQubits)
  catalyst_polynomial : PolynomialBound (fun x => (circuit x).catalystQubits)
  gates_polynomial : PolynomialBound (fun x => (circuit x).gates.length)

/-- Exact source acceptance for every initially allowed catalyst state. -/
def SourceDecidesExact {G : GateSet} (F : SourceFamily G) (language : Input → Bool) : Prop :=
  ∀ x (σ : Operator (F.circuit x).catalystQubits),
    σ.PosSemidef → Matrix.trace σ = 1 →
    (F.circuit x).accept σ = if language x then 1 else 0

/-- Bounded-error source acceptance, retaining the same circuit family. -/
def SourceDecidesBoundedError {G : GateSet}
    (F : SourceFamily G) (language : Input → Bool) : Prop :=
  ∀ x (σ : Operator (F.circuit x).catalystQubits),
    σ.PosSemidef → Matrix.trace σ = 1 →
    if language x then (2 / 3 : ℝ) ≤ (F.circuit x).accept σ
    else (F.circuit x).accept σ ≤ (1 / 3 : ℝ)

lemma SourceDecidesExact.boundedError {G : GateSet} {F : SourceFamily G}
    {language : Input → Bool} (h : SourceDecidesExact F language) :
    SourceDecidesBoundedError F language := by
  intro x σ hσ ht
  rw [h x σ hσ ht]
  cases language x <;> norm_num

structure TargetFamily (G : GateSet) where
  circuit : Input → TargetCircuit G
  uniform : LogspaceGenerates (fun x => (circuit x).encode)
  mixed_polynomial : PolynomialBound (fun x => (circuit x).mixedQubits)
  gates_polynomial : PolynomialBound (fun x => (circuit x).gateCount)

/-- Acceptance and signed bias retain dependence on the entire input string. -/
def TargetFamily.accept {G : GateSet} (F : TargetFamily G) (x : Input) : ℝ :=
  (F.circuit x).accept

def TargetFamily.signedBias {G : GateSet} (F : TargetFamily G) (x : Input) : ℝ :=
  2 * F.accept x - 1

/-- The paper's signed-bias convention for a language of binary strings. -/
def DecidesWithInversePolynomialBias {G : GateSet}
    (F : TargetFamily G) (language : Input → Bool) : Prop :=
  ∃ (C : ℝ) (d : ℕ), 0 < C ∧ ∀ x,
    if language x then C / ((x.length : ℝ) + 1) ^ d ≤ F.signedBias x
    else F.signedBias x ≤ -(C / ((x.length : ℝ) + 1) ^ d)

end Paper25.OperationalModel
