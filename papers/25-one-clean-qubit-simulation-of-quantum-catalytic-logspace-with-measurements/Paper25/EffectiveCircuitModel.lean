import Paper25.CircuitModel
import Mathlib.Data.Nat.Bits

/-!
# Effective parameter gates

`CircuitModel` is the ideal fixed-finite-alphabet submodel. This file also allows
finite primitive kinds with finite bitstring parameters. A gate interpretation
must carry an actual finite-transducer entry-approximation certificate; arbitrary
complex-valued interpretations alone do not meet this definition.

The approximation query contains unary `2^precision` padding. Thus its certified
space is O(precision + log(parameter length)) and its certified time is polynomial
in inverse accuracy and parameter length. This is the inverse-polynomial
accuracy regime used by the paper. Padding, parameters, wire descriptions and
output bit lengths are all counted explicitly. Concrete rotation/phase instances
and the paper's source-to-target compiler remain separate proof obligations.
-/
noncomputable section
open scoped ComplexOrder
open Matrix
namespace Paper25.OperationalModel

/-- The two integer numerators of a complex dyadic approximation. -/
structure ComplexDyadic where
  realNumerator : ℤ
  imagNumerator : ℤ

def ComplexDyadic.value (a : ComplexDyadic) (precision : ℕ) : ℂ :=
  ((a.realNumerator : ℂ) + Complex.I * (a.imagNumerator : ℂ)) / (2 : ℂ) ^ precision

/-- A length-prefixed binary encoding, so large dyadic numerators do not incur
unary output cost. -/
def encodeBinaryNat (n : ℕ) : Input :=
  encodeNat n.bits.length ++ n.bits.map (fun b => if b then 1 else 0)

def encodeInteger (z : ℤ) : Input :=
  (if z < 0 then [1] else [0]) ++ encodeBinaryNat z.natAbs

/-- Canonical signed numerator and positive-denominator encoding of a rational. -/
def encodeRational (q : ℚ) : Input := encodeInteger q.num ++ encodeBinaryNat q.den

/-- An unreduced binary rational representation. Arithmetic below never
computes a gcd or promises a canonical numerator/denominator pair. -/
structure RationalRep where
  num : ℤ
  den : ℕ
  den_pos : 0 < den

def RationalRep.value (a : RationalRep) : ℚ := (a.num : ℚ) / (a.den : ℚ)
def RationalRep.encode (a : RationalRep) : Input := encodeInteger a.num ++ encodeBinaryNat a.den

/-- Mathematical choice of a representation, used for fixed constants and
semantic statements. No input-dependent computation of this map is asserted. -/
def RationalRep.ofRat (a : ℚ) : RationalRep := ⟨a.num,a.den,a.pos⟩

@[simp] lemma RationalRep.ofRat_value (a : ℚ) : (ofRat a).value = a := by
  simpa only [ofRat,value] using Rat.num_div_den a

lemma RationalRep.den_ne_zero (a : RationalRep) : (a.den : ℚ) ≠ 0 := by
  exact_mod_cast (Nat.ne_of_gt a.den_pos)

def RationalRep.add (a b : RationalRep) : RationalRep :=
  ⟨a.num * (b.den : ℤ) + b.num * (a.den : ℤ),a.den*b.den,Nat.mul_pos a.den_pos b.den_pos⟩
def RationalRep.sub (a b : RationalRep) : RationalRep :=
  ⟨a.num * (b.den : ℤ) - b.num * (a.den : ℤ),a.den*b.den,Nat.mul_pos a.den_pos b.den_pos⟩
def RationalRep.mul (a b : RationalRep) : RationalRep :=
  ⟨a.num*b.num,a.den*b.den,Nat.mul_pos a.den_pos b.den_pos⟩

@[simp] lemma RationalRep.value_add (a b : RationalRep) : (a.add b).value = a.value+b.value := by
  dsimp [add,value]
  push_cast
  have ha := a.den_ne_zero
  have hb := b.den_ne_zero
  field_simp [ha,hb]

@[simp] lemma RationalRep.value_sub (a b : RationalRep) : (a.sub b).value = a.value-b.value := by
  dsimp [sub,value]
  push_cast
  have ha := a.den_ne_zero
  have hb := b.den_ne_zero
  field_simp [ha,hb]

@[simp] lemma RationalRep.value_mul (a b : RationalRep) : (a.mul b).value = a.value*b.value := by
  dsimp [mul,value]
  push_cast
  ring

/-- Sign-normalize an integer fraction without reducing it. Zero denominator
uses the same total value zero as rational division. -/
def RationalRep.ofIntFraction (n d : ℤ) : RationalRep :=
  if hd : d=0 then ofRat 0
  else if hp : 0<d then ⟨n,d.toNat,by omega⟩
  else ⟨-n,(-d).toNat,by omega⟩

@[simp] lemma RationalRep.value_ofIntFraction (n d : ℤ) :
    (ofIntFraction n d).value = (n : ℚ)/(d : ℚ) := by
  unfold ofIntFraction
  split_ifs with hd hp
  · simp [hd]
  · dsimp [value]
    have hc : (d.toNat : ℚ) = (d : ℚ) := by exact_mod_cast Int.toNat_of_nonneg (le_of_lt hp)
    rw [hc]
  · dsimp [value]
    have hc : ((-d).toNat : ℚ) = ((-d : ℤ) : ℚ) := by
      exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ -d)
    rw [hc]
    push_cast
    simp

def RationalRep.div (a b : RationalRep) : RationalRep :=
  ofIntFraction (a.num * (b.den : ℤ)) ((a.den : ℤ) * b.num)

@[simp] lemma RationalRep.value_div (a b : RationalRep) : (a.div b).value = a.value/b.value := by
  rw [div,value_ofIntFraction]
  push_cast
  dsimp [value]
  simp only [div_eq_mul_inv,_root_.mul_inv_rev,inv_inv]
  ring

/-- Exact comparison by signed cross multiplication, with positive denominators. -/
def RationalRep.less (a b : RationalRep) : Bool :=
  decide (a.num * (b.den : ℤ) < b.num * (a.den : ℤ))

@[simp] lemma RationalRep.less_eq_true (a b : RationalRep) :
    a.less b = true ↔ a.value < b.value := by
  simp only [less,decide_eq_true_eq,value]
  rw [div_lt_div_iff₀ (by exact_mod_cast a.den_pos) (by exact_mod_cast b.den_pos)]
  exact_mod_cast Iff.rfl

/-- Clip represented values by comparisons and selection of raw representations. -/
def RationalRep.clip (lo hi a : RationalRep) : RationalRep :=
  if a.less lo then lo else if hi.less a then hi else a

lemma RationalRep.value_clip (lo hi a : RationalRep) (hbounds : lo.value ≤ hi.value) :
    (clip lo hi a).value = max lo.value (min hi.value a.value) := by
  unfold clip
  split_ifs with hlo hhi
  · have h : a.value < lo.value := (less_eq_true a lo).mp hlo
    rw [max_eq_left]
    exact (min_le_right _ _).trans (le_of_lt h)
  · have h : hi.value < a.value := (less_eq_true hi a).mp hhi
    have hn : ¬ a.value < lo.value := by simpa only [less_eq_true] using hlo
    rw [min_eq_left (le_of_lt h),max_eq_right]
    exact hbounds
  · have hn : ¬ a.value < lo.value := by simpa only [less_eq_true] using hlo
    have hm : ¬ hi.value < a.value := by simpa only [less_eq_true] using hhi
    rw [min_eq_right (le_of_not_gt hm),max_eq_right (le_of_not_gt hn)]

def encodeRationalRepPair (a : RationalRep × RationalRep) : Input :=
  encodeNat a.1.encode.length ++ a.1.encode ++ a.2.encode

def ComplexDyadic.encode (a : ComplexDyadic) : Input :=
  encodeInteger a.realNumerator ++ encodeInteger a.imagNumerator

/-- The query encoding is fixed, including its precision and index fields. -/
def entryQuery {k : ℕ} (kind : ℕ) (payload : Input) (precision : ℕ)
    (i j : Basis k) : Input :=
  encodeNat kind ++ encodeNat payload.length ++ payload ++ encodeNat (2 ^ precision) ++
    List.ofFn i ++ List.ofFn j

/-- Finite primitive kinds and explicit parameters, with both unitary semantics
and an effective interpreter at polynomial cost in inverse accuracy. -/
structure EffectiveGateSet where
  kinds : ℕ
  arity : Fin kinds → ℕ
  locality : ℕ
  arity_le : ∀ a, arity a ≤ locality
  matrix : (a : Fin kinds) → Input → Operator (arity a)
  unitary : ∀ a payload, OneCleanQubit.Unitary (matrix a payload)
  approximation : (a : Fin kinds) → Input → ℕ → Basis (arity a) → Basis (arity a) → ComplexDyadic
  approximation_error : ∀ a payload precision i j,
    ‖(approximation a payload precision i j).value precision - matrix a payload i j‖ ≤
      1 / (2 : ℝ) ^ precision
  interpreter : Transducer
  spaceConstant : ℕ
  timeConstant : ℕ
  timeDegree : ℕ
  effective : ∀ a payload precision i j,
    let query := entryQuery a.val payload precision i j
    let capacity := spaceConstant * (Nat.log2 (query.length + 2) + 1)
    let result := interpreter.run (timeConstant * (query.length + 1) ^ timeDegree)
      (interpreter.initial query capacity)
    interpreter.halt result.1.control = true ∧
      result.2 = (approximation a payload precision i j).encode

structure EffectiveLocalGate (G : EffectiveGateSet) (q : ℕ) where
  kind : Fin G.kinds
  payload : Input
  placement : Placement q (G.arity kind)

def EffectiveLocalGate.matrix {G : EffectiveGateSet} {q : ℕ}
    (g : EffectiveLocalGate G q) : Operator q :=
  g.placement.lift (G.matrix g.kind g.payload)

lemma EffectiveLocalGate.unitary {G : EffectiveGateSet} {q : ℕ}
    (g : EffectiveLocalGate G q) : OneCleanQubit.Unitary g.matrix :=
  g.placement.lift_unitary _ (G.unitary g.kind g.payload)

def EffectiveLocalGate.encode {G : EffectiveGateSet} {q : ℕ}
    (g : EffectiveLocalGate G q) : Input :=
  encodeNat g.kind.val ++ encodeNat g.payload.length ++ g.payload ++ g.placement.encode

lemma EffectiveLocalGate.payload_length_le {G : EffectiveGateSet} {q : ℕ}
    (g : EffectiveLocalGate G q) : g.payload.length ≤ g.encode.length := by
  simp only [EffectiveLocalGate.encode, List.length_append]
  omega

abbrev EffectiveCircuit (G : EffectiveGateSet) (q : ℕ) := List (EffectiveLocalGate G q)

def EffectiveCircuit.matrix {G : EffectiveGateSet} {q : ℕ} : EffectiveCircuit G q → Operator q
  | [] => 1
  | g :: gs => EffectiveCircuit.matrix gs * g.matrix

lemma EffectiveCircuit.unitary {G : EffectiveGateSet} {q : ℕ}
    (C : EffectiveCircuit G q) : OneCleanQubit.Unitary C.matrix := by
  induction C with
  | nil => constructor <;> simp [EffectiveCircuit.matrix]
  | cons g gs ih => exact OneCleanQubit.unitary_mul ih g.unitary

def EffectiveCircuit.run {G : EffectiveGateSet} {q : ℕ} :
    EffectiveCircuit G q → Operator q → Operator q
  | [], ρ => ρ
  | g :: gs, ρ => EffectiveCircuit.run gs (OneCleanQubit.evolve g.matrix ρ)

lemma EffectiveCircuit.run_eq_evolve {G : EffectiveGateSet} {q : ℕ}
    (C : EffectiveCircuit G q) (ρ : Operator q) : C.run ρ = OneCleanQubit.evolve C.matrix ρ := by
  induction C generalizing ρ with
  | nil => simp [EffectiveCircuit.run, EffectiveCircuit.matrix, OneCleanQubit.evolve]
  | cons g gs ih =>
    rw [EffectiveCircuit.run, ih, EffectiveCircuit.matrix, OneCleanQubit.evolve_comp]

lemma EffectiveCircuit.matrix_append {G : EffectiveGateSet} {q : ℕ}
    (C D : EffectiveCircuit G q) : (C ++ D).matrix = D.matrix * C.matrix := by
  induction C with
  | nil => simp [EffectiveCircuit.matrix]
  | cons g gs ih => simp only [List.cons_append, EffectiveCircuit.matrix, ih, mul_assoc]

structure EffectiveTargetCircuit (G : EffectiveGateSet) where
  mixedQubits : ℕ
  gates : EffectiveCircuit G (mixedQubits + 1)

def EffectiveTargetCircuit.matrix {G : EffectiveGateSet} (C : EffectiveTargetCircuit G) :
    OneCleanQubit.ProbeMatrix (Basis C.mixedQubits) :=
  C.gates.matrix.submatrix (probeBasis C.mixedQubits).symm (probeBasis C.mixedQubits).symm

lemma EffectiveTargetCircuit.unitary {G : EffectiveGateSet} (C : EffectiveTargetCircuit G) :
    OneCleanQubit.Unitary C.matrix := unitary_submatrix _ _ C.gates.unitary

def EffectiveTargetCircuit.output {G : EffectiveGateSet} (C : EffectiveTargetCircuit G) :
    OneCleanQubit.ProbeMatrix (Basis C.mixedQubits) :=
  OneCleanQubit.evolve C.matrix OneCleanQubit.input

def EffectiveTargetCircuit.accept {G : EffectiveGateSet} (C : EffectiveTargetCircuit G) : ℝ :=
  OneCleanQubit.probZero C.output

def EffectiveTargetCircuit.gateCount {G : EffectiveGateSet} (C : EffectiveTargetCircuit G) : ℕ :=
  C.gates.length

def EffectiveTargetCircuit.encode {G : EffectiveGateSet} (C : EffectiveTargetCircuit G) : Input :=
  encodeNat C.mixedQubits ++ encodeNat C.gateCount ++ (C.gates.map EffectiveLocalGate.encode).flatten

def EffectiveTargetCircuit.inputPhysical {G : EffectiveGateSet} (C : EffectiveTargetCircuit G) :
    Operator (C.mixedQubits + 1) :=
  (OneCleanQubit.input : OneCleanQubit.ProbeMatrix (Basis C.mixedQubits)).submatrix
    (probeBasis C.mixedQubits) (probeBasis C.mixedQubits)

lemma EffectiveTargetCircuit.run_eq_output {G : EffectiveGateSet} (C : EffectiveTargetCircuit G) :
    C.gates.run C.inputPhysical = C.output.submatrix
      (probeBasis C.mixedQubits) (probeBasis C.mixedQubits) := by
  rw [C.gates.run_eq_evolve, EffectiveTargetCircuit.output, ← evolve_submatrix]
  congr 1
  ext i j
  simp [EffectiveTargetCircuit.matrix, Matrix.submatrix_apply]

lemma EffectiveTargetCircuit.output_posSemidef {G : EffectiveGateSet}
    (C : EffectiveTargetCircuit G) : C.output.PosSemidef :=
  OneCleanQubit.evolve_posSemidef _ _ OneCleanQubit.input_posSemidef

lemma EffectiveTargetCircuit.output_trace {G : EffectiveGateSet} (C : EffectiveTargetCircuit G) :
    Matrix.trace C.output = 1 := by
  rw [EffectiveTargetCircuit.output, OneCleanQubit.evolve_trace _ _ C.unitary,
    OneCleanQubit.input_trace]

lemma EffectiveTargetCircuit.accept_mem_unitInterval {G : EffectiveGateSet}
    (C : EffectiveTargetCircuit G) : 0 ≤ C.accept ∧ C.accept ≤ 1 := by
  have h0 := OneCleanQubit.probZero_nonneg C.output C.output_posSemidef
  have h1 := OneCleanQubit.probOne_nonneg C.output C.output_posSemidef
  have hs := OneCleanQubit.measurement_sum C.output
  rw [C.output_trace] at hs
  simp only [Complex.one_re] at hs
  exact ⟨h0, by dsimp [EffectiveTargetCircuit.accept]; linarith⟩

inductive EffectiveSourceOp (G : EffectiveGateSet) (q : ℕ) where
  | gate (g : EffectiveLocalGate G q)
  | dephase (p : Placement q 1)
  | reset (p : Placement q 1)
  | measurement (p : Placement q 2)

def EffectiveSourceOp.channel {G : EffectiveGateSet} {q : ℕ} :
    EffectiveSourceOp G q → KrausChannel (Basis q)
  | .gate g => KrausChannel.unitary g.matrix g.unitary.1
  | .dephase p => p.liftChannel (relabelChannel oneBit KrausChannel.dephase)
  | .reset p => p.liftChannel (relabelChannel oneBit KrausChannel.reset)
  | .measurement p =>
    p.liftChannel (relabelChannel (finTwoArrowEquiv Bit) KrausChannel.measurement)

def EffectiveSourceOp.encode {G : EffectiveGateSet} {q : ℕ} : EffectiveSourceOp G q → Input
  | .gate g => encodeNat 0 ++ g.encode
  | .dephase p => encodeNat 1 ++ p.encode
  | .reset p => encodeNat 2 ++ p.encode
  | .measurement p => encodeNat 3 ++ p.encode

abbrev EffectiveSourceCircuit (G : EffectiveGateSet) (q : ℕ) := List (EffectiveSourceOp G q)

def EffectiveSourceCircuit.channel {G : EffectiveGateSet} {q : ℕ} :
    EffectiveSourceCircuit G q → KrausChannel (Basis q)
  | [] => KrausChannel.identity
  | g :: gs => (EffectiveSourceCircuit.channel gs).comp g.channel

structure EffectiveSourceComputation (G : EffectiveGateSet) where
  workQubits : ℕ
  catalystQubits : ℕ
  outputQubit : Fin workQubits
  gates : EffectiveSourceCircuit G (workQubits + catalystQubits)

def EffectiveSourceComputation.encode {G : EffectiveGateSet} (C : EffectiveSourceComputation G) : Input :=
  encodeNat C.workQubits ++ encodeNat C.catalystQubits ++ encodeNat C.outputQubit.val ++
    encodeNat C.gates.length ++ (C.gates.map EffectiveSourceOp.encode).flatten

def EffectiveSourceComputation.input {G : EffectiveGateSet} (C : EffectiveSourceComputation G)
    (σ : Operator C.catalystQubits) : Operator (C.workQubits + C.catalystQubits) :=
  (Matrix.kronecker (pureZero C.workQubits) σ).submatrix
    (registerBasis C.workQubits C.catalystQubits) (registerBasis C.workQubits C.catalystQubits)

def EffectiveSourceComputation.output {G : EffectiveGateSet} (C : EffectiveSourceComputation G)
    (σ : Operator C.catalystQubits) : Operator (C.workQubits + C.catalystQubits) :=
  C.gates.channel.act (C.input σ)

def EffectiveSourceComputation.accept {G : EffectiveGateSet} (C : EffectiveSourceComputation G)
    (σ : Operator C.catalystQubits) : ℝ :=
  ∑ b : Basis (C.workQubits + C.catalystQubits),
    if b (Fin.castAdd C.catalystQubits C.outputQubit) = 1 then (C.output σ b b).re else 0

def EffectiveSourceComputation.referenceBasis {G : EffectiveGateSet}
    (C : EffectiveSourceComputation G) (r : Type*) :
    (Basis (C.workQubits + C.catalystQubits) × r) ≃
      (Basis C.workQubits × (Basis C.catalystQubits × r)) :=
  (Equiv.prodCongr (registerBasis C.workQubits C.catalystQubits) (Equiv.refl r)).trans
    (Equiv.prodAssoc _ _ _)

def EffectiveSourceComputation.Restores {G : EffectiveGateSet} (C : EffectiveSourceComputation G) : Prop :=
  ∀ (r : Type) [Fintype r] [DecidableEq r]
    (σ : Matrix (Basis C.catalystQubits × r) (Basis C.catalystQubits × r) ℂ),
    σ.PosSemidef → Matrix.trace σ = 1 →
    let initial := (Matrix.kronecker (pureZero C.workQubits) σ).submatrix
      (C.referenceBasis r) (C.referenceBasis r)
    let final := (C.gates.channel.extendRight r).act initial
    ∀ i j : Basis C.catalystQubits × r,
      (∑ w : Basis C.workQubits,
        final ((C.referenceBasis r).symm (w, i)) ((C.referenceBasis r).symm (w, j))) = σ i j

structure EffectiveSourceFamily (G : EffectiveGateSet) where
  circuit : Input → EffectiveSourceComputation G
  restoration : ∀ x, (circuit x).Restores
  uniform : LogspaceGenerates (fun x => (circuit x).encode)
  work_logarithmic : LogarithmicBound (fun x => (circuit x).workQubits)
  catalyst_polynomial : PolynomialBound (fun x => (circuit x).catalystQubits)
  gates_polynomial : PolynomialBound (fun x => (circuit x).gates.length)

structure EffectiveTargetFamily (G : EffectiveGateSet) where
  circuit : Input → EffectiveTargetCircuit G
  uniform : LogspaceGenerates (fun x => (circuit x).encode)
  mixed_polynomial : PolynomialBound (fun x => (circuit x).mixedQubits)
  gates_polynomial : PolynomialBound (fun x => (circuit x).gateCount)

/-- Payload lengths are included in these descriptions, so uniformity also
bounds total parameter output, rather than only the number of gate symbols. -/
lemma EffectiveTargetFamily.description_polynomial {G : EffectiveGateSet}
    (F : EffectiveTargetFamily G) : PolynomialBound (fun x => (F.circuit x).encode.length) :=
  F.uniform.output_polynomial

lemma EffectiveSourceFamily.description_polynomial {G : EffectiveGateSet}
    (F : EffectiveSourceFamily G) : PolynomialBound (fun x => (F.circuit x).encode.length) :=
  F.uniform.output_polynomial

def EffectiveSourceDecidesExact {G : EffectiveGateSet}
    (F : EffectiveSourceFamily G) (language : Input → Bool) : Prop :=
  ∀ x (σ : Operator (F.circuit x).catalystQubits),
    σ.PosSemidef → Matrix.trace σ = 1 →
    (F.circuit x).accept σ = if language x then 1 else 0

def EffectiveSourceDecidesBoundedError {G : EffectiveGateSet}
    (F : EffectiveSourceFamily G) (language : Input → Bool) : Prop :=
  ∀ x (σ : Operator (F.circuit x).catalystQubits),
    σ.PosSemidef → Matrix.trace σ = 1 →
    if language x then (2 / 3 : ℝ) ≤ (F.circuit x).accept σ
    else (F.circuit x).accept σ ≤ (1 / 3 : ℝ)

lemma EffectiveSourceDecidesExact.boundedError {G : EffectiveGateSet} {F : EffectiveSourceFamily G}
    {language : Input → Bool} (h : EffectiveSourceDecidesExact F language) :
    EffectiveSourceDecidesBoundedError F language := by
  intro x σ hσ ht
  rw [h x σ hσ ht]
  cases language x <;> norm_num

def EffectiveTargetFamily.accept {G : EffectiveGateSet} (F : EffectiveTargetFamily G) (x : Input) : ℝ :=
  (F.circuit x).accept

def EffectiveTargetFamily.signedBias {G : EffectiveGateSet} (F : EffectiveTargetFamily G) (x : Input) : ℝ :=
  2 * F.accept x - 1

def EffectiveDecidesWithInversePolynomialBias {G : EffectiveGateSet}
    (F : EffectiveTargetFamily G) (language : Input → Bool) : Prop :=
  ∃ (C : ℝ) (d : ℕ), 0 < C ∧ ∀ x,
    if language x then C / ((x.length : ℝ) + 1) ^ d ≤ F.signedBias x
    else F.signedBias x ≤ -(C / ((x.length : ℝ) + 1) ^ d)

end Paper25.OperationalModel
