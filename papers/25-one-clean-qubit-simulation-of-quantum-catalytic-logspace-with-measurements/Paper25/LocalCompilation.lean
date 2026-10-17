import Paper25.CircuitRecipe
import Paper25.BlockEncoding
import Mathlib.Data.List.Dedup

/-! Physical embeddings and actual list compilation under the paper's explicitly
assumed effective elementary-gate convention. This module does not postulate a
compiler for the paper's complete simulator. -/
noncomputable section
open Matrix
namespace Paper25.OperationalModel.LocalCompilation
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 800000

/-- The selected wires of an already legal placement. -/
def active {q k : ℕ} (p : Placement q k) : Fin k ↪ Fin q where
  toFun i := p.wires (Sum.inl i)
  inj' := by intro i j h; exact Sum.inl_injective (p.wires.injective h)

/-- Equality on all positions outside the selected wires. -/
def Inactive {q k : ℕ} (f : Fin k ↪ Fin q) (x y : Basis q) : Prop :=
  ∀ j, j ∉ Set.range f → x j = y j

lemma rest_eq_iff {q k : ℕ} (p : Placement q k) (x y : Basis q) :
    (p.split x).2 = (p.split y).2 ↔ Inactive (active p) x y := by
  constructor
  · intro h j hj
    have he := p.wires.apply_symm_apply j
    rcases hp : p.wires.symm j with i | i
    · exfalso
      apply hj
      exact ⟨i, by simpa only [active,hp] using he⟩
    · have hi := congrFun h i
      change x (p.wires (Sum.inr i)) = y (p.wires (Sum.inr i)) at hi
      have he' : p.wires (Sum.inr i) = j := by simpa only [hp] using he
      simpa only [he'] using hi
  · intro h
    funext i
    apply h (p.wires (Sum.inr i))
    rintro ⟨j,hj⟩
    have := p.wires.injective hj
    exact Sum.noConfusion this

/-- Any injection of k physical positions can be completed by the untouched
positions; the completion is a permutation of positions alone. -/
def complementEquiv {q k : ℕ} (f : Fin k ↪ Fin q) :
    Fin (q-k) ≃ {j : Fin q // j ∉ Set.range f} := by
  classical
  have hc : Fintype.card {j : Fin q // j ∉ Set.range f} = q-k := by
    rw [Fintype.card_subtype_compl]
    simp only [Fintype.card_fin,Fintype.card_range]
  exact (finCongr hc.symm).trans (Fintype.equivFin _).symm

def placementOfEmbedding {q k : ℕ} (f : Fin k ↪ Fin q) : Placement q k := by
  classical
  exact {
    enough := by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f f.injective
    wires := (Equiv.sumCongr f.toEquivRange (complementEquiv f)).trans
      (Equiv.sumCompl (fun j : Fin q => j ∈ Set.range f)) }

@[simp] lemma active_placementOfEmbedding {q k : ℕ} (f : Fin k ↪ Fin q) (i : Fin k) :
    active (placementOfEmbedding f) i = f i := by
  classical
  rfl

@[simp] lemma active_placementOfEmbedding_eq {q k : ℕ} (f : Fin k ↪ Fin q) :
    active (placementOfEmbedding f) = f := by
  apply Function.Embedding.ext
  intro i
  exact active_placementOfEmbedding f i


lemma lift_apply {q k : ℕ} (p : Placement q k) (U : Operator k) (x y : Basis q) :
    p.lift U x y = U (fun i => x (active p i)) (fun i => y (active p i)) *
      (if Inactive (active p) x y then 1 else 0) := by
  rw [Placement.lift_apply]
  simp only [rest_eq_iff]
  rfl

/-- The unused complement ordering is semantically irrelevant. Consequently
the standard active-wire-only printed description determines the local gate. -/
lemma lift_eq_of_active_eq {q k : ℕ} (p r : Placement q k)
    (h : active p = active r) (U : Operator k) : p.lift U = r.lift U := by
  ext x y
  simp only [lift_apply,h]

lemma inactive_comp {q k a : ℕ} (f : Fin k ↪ Fin q) (g : Fin a ↪ Fin k)
    (x y : Basis q) : Inactive (g.trans f) x y ↔
      Inactive g (fun i => x (f i)) (fun i => y (f i)) ∧ Inactive f x y := by
  constructor
  · intro h
    constructor
    · intro j hj
      apply h (f j)
      rintro ⟨i,hi⟩
      exact hj ⟨i,f.injective hi⟩
    · intro j hj
      apply h j
      rintro ⟨i,hi⟩
      exact hj ⟨g i,hi⟩
  · rintro ⟨hinner,houter⟩ j hj
    by_cases hf : j ∈ Set.range f
    · rcases hf with ⟨i,rfl⟩
      apply hinner i
      rintro ⟨a,rfl⟩
      exact hj ⟨a,rfl⟩
    · exact houter j hf

def embedGate {G : EffectiveGateSet} {q k : ℕ} (p : Placement q k)
    (g : EffectiveLocalGate G k) : EffectiveLocalGate G q where
  kind := g.kind
  payload := g.payload
  placement := placementOfEmbedding ((active g.placement).trans (active p))

lemma embedGate_matrix {G : EffectiveGateSet} {q k : ℕ} (p : Placement q k)
    (g : EffectiveLocalGate G k) : (embedGate p g).matrix = p.lift g.matrix := by
  ext x y
  simp only [embedGate,EffectiveLocalGate.matrix,lift_apply,
    active_placementOfEmbedding_eq,inactive_comp]
  dsimp only [Function.Embedding.trans_apply]
  by_cases hinner : Inactive (active g.placement)
    (fun i => x (active p i)) (fun i => y (active p i)) <;>
    by_cases houter : Inactive (active p) x y <;> simp [hinner,houter,mul_assoc]

lemma lift_one {q k : ℕ} (p : Placement q k) : p.lift (1 : Operator k) = 1 := by
  simp [Placement.lift,Matrix.kronecker,Matrix.one_kronecker_one]

lemma lift_mul {q k : ℕ} (p : Placement q k) (U V : Operator k) :
    p.lift (U*V) = p.lift U * p.lift V := by
  simp only [Placement.lift,Matrix.kronecker,Matrix.submatrix_mul_equiv,
    ← Matrix.mul_kronecker_mul,one_mul]

lemma lift_adjoint {q k : ℕ} (p : Placement q k) (U : Operator k) :
    p.lift U.conjTranspose = (p.lift U).conjTranspose := by
  simp only [Placement.lift,Matrix.kronecker,Matrix.conjTranspose_submatrix,
    Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one]

def embedCircuit {G : EffectiveGateSet} {q k : ℕ} (p : Placement q k)
    (C : EffectiveCircuit G k) : EffectiveCircuit G q := C.map (embedGate p)

lemma embedCircuit_matrix {G : EffectiveGateSet} {q k : ℕ} (p : Placement q k)
    (C : EffectiveCircuit G k) : (embedCircuit p C).matrix = p.lift C.matrix := by
  induction C with
  | nil => simpa [embedCircuit,EffectiveCircuit.matrix] using (lift_one p).symm
  | cons g gs ih =>
    change (embedCircuit p gs).matrix * (embedGate p g).matrix = p.lift (EffectiveCircuit.matrix gs * g.matrix)
    rw [ih,embedGate_matrix,lift_mul]

@[simp] lemma embedCircuit_length {G : EffectiveGateSet} {q k : ℕ}
    (p : Placement q k) (C : EffectiveCircuit G k) : (embedCircuit p C).length = C.length := by
  simp [embedCircuit]

lemma localGate_apply {G : EffectiveGateSet} {q : ℕ}
    (g : EffectiveLocalGate G q) (x y : Basis q) :
    g.matrix x y = G.matrix g.kind g.payload (fun i => x (active g.placement i))
      (fun i => y (active g.placement i)) * (if Inactive (active g.placement) x y then 1 else 0) := by
  rw [EffectiveLocalGate.matrix,lift_apply]

/-- Split a physical register at a position boundary. -/
def tensorBits (q r : ℕ) : Basis (q+r) ≃ (Basis q × Basis r) where
  toFun x := (fun i => x (Fin.castAdd r i),fun j => x (Fin.natAdd q j))
  invFun p := fun i => Sum.elim p.1 p.2 (finSumFinEquiv.symm i)
  left_inv x := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  right_inv p := by apply Prod.ext <;> funext i <;> simp

def leftEmbedding {q k : ℕ} (f : Fin k ↪ Fin q) (r : ℕ) : Fin k ↪ Fin (q+r) where
  toFun i := Fin.castAdd r (f i)
  inj' := by intro i j h; apply f.injective; simpa using h

def rightEmbedding {r k : ℕ} (f : Fin k ↪ Fin r) (q : ℕ) : Fin k ↪ Fin (q+r) where
  toFun i := Fin.natAdd q (f i)
  inj' := by intro i j h; apply f.injective; simpa using h

lemma inactive_left {q k r : ℕ} (f : Fin k ↪ Fin q) (x y : Basis (q+r)) :
    Inactive (leftEmbedding f r) x y ↔
      Inactive f (tensorBits q r x).1 (tensorBits q r y).1 ∧
        (tensorBits q r x).2 = (tensorBits q r y).2 := by
  constructor
  · intro h
    constructor
    · intro j hj
      apply h (Fin.castAdd r j)
      rintro ⟨i,hi⟩
      change Fin.castAdd r (f i) = Fin.castAdd r j at hi
      exact hj ⟨i,by simpa using hi⟩
    · funext j
      apply h (Fin.natAdd q j)
      rintro ⟨i,hi⟩
      have hv := congrArg Fin.val hi
      have hb := (f i).isLt
      simp [leftEmbedding] at hv
      omega
  · rintro ⟨hL,hR⟩ j
    refine Fin.addCases (fun i hi => ?_) (fun i hi => ?_) j
    · apply hL i
      rintro ⟨a,ha⟩
      exact hi ⟨a,congrArg (Fin.castAdd r) ha⟩
    · exact congrFun hR i

lemma inactive_right {q r k : ℕ} (f : Fin k ↪ Fin r) (x y : Basis (q+r)) :
    Inactive (rightEmbedding f q) x y ↔
      (tensorBits q r x).1 = (tensorBits q r y).1 ∧
        Inactive f (tensorBits q r x).2 (tensorBits q r y).2 := by
  constructor
  · intro h
    constructor
    · funext j
      apply h (Fin.castAdd r j)
      rintro ⟨i,hi⟩
      have hv := congrArg Fin.val hi
      have hb := j.isLt
      simp [rightEmbedding] at hv
      omega
    · intro j hj
      apply h (Fin.natAdd q j)
      rintro ⟨i,hi⟩
      change Fin.natAdd q (f i) = Fin.natAdd q j at hi
      exact hj ⟨i,by simpa using hi⟩
  · rintro ⟨hL,hR⟩ j
    refine Fin.addCases (fun i hi => ?_) (fun i hi => ?_) j
    · exact congrFun hL i
    · apply hR i
      rintro ⟨a,ha⟩
      exact hi ⟨a,congrArg (Fin.natAdd q) ha⟩

def liftLeft {G : EffectiveGateSet} {q : ℕ} (g : EffectiveLocalGate G q) (r : ℕ) : EffectiveLocalGate G (q+r) where
  kind := g.kind
  payload := g.payload
  placement := placementOfEmbedding (leftEmbedding (active g.placement) r)

def liftRight {G : EffectiveGateSet} {r : ℕ} (g : EffectiveLocalGate G r) (q : ℕ) : EffectiveLocalGate G (q+r) where
  kind := g.kind
  payload := g.payload
  placement := placementOfEmbedding (rightEmbedding (active g.placement) q)

lemma liftLeft_matrix {G : EffectiveGateSet} {q : ℕ} (g : EffectiveLocalGate G q) (r : ℕ) :
    (liftLeft g r).matrix = (Matrix.kronecker g.matrix (1 : Operator r)).submatrix
      (tensorBits q r) (tensorBits q r) := by
  ext x y
  rw [localGate_apply]
  simp only [liftLeft,active_placementOfEmbedding_eq,Matrix.submatrix_apply,
    Matrix.kronecker,Matrix.kroneckerMap_apply,localGate_apply,Matrix.one_apply,
    inactive_left]
  dsimp only [leftEmbedding,tensorBits]
  by_cases hL : Inactive (active g.placement) (fun i => x (Fin.castAdd r i))
      (fun i => y (Fin.castAdd r i)) <;>
    by_cases hR : (fun i => x (Fin.natAdd q i)) = (fun i => y (Fin.natAdd q i)) <;>
      simp [hL,hR]

lemma liftRight_matrix {G : EffectiveGateSet} {r : ℕ} (g : EffectiveLocalGate G r) (q : ℕ) :
    (liftRight g q).matrix = (Matrix.kronecker (1 : Operator q) g.matrix).submatrix
      (tensorBits q r) (tensorBits q r) := by
  ext x y
  rw [localGate_apply]
  simp only [liftRight,active_placementOfEmbedding_eq,Matrix.submatrix_apply,
    Matrix.kronecker,Matrix.kroneckerMap_apply,localGate_apply,Matrix.one_apply,
    inactive_right]
  dsimp only [rightEmbedding,tensorBits]
  by_cases hL : (fun i => x (Fin.castAdd r i)) = (fun i => y (Fin.castAdd r i)) <;>
    by_cases hR : Inactive (active g.placement) (fun i => x (Fin.natAdd q i))
      (fun i => y (Fin.natAdd q i)) <;> simp [hL,hR]

/-- Disjoint local circuits, represented in the actual physical qubit model. -/
def tensorCircuit {G : EffectiveGateSet} {q r : ℕ} (C : EffectiveCircuit G q) (D : EffectiveCircuit G r) :
    EffectiveCircuit G (q+r) := C.map (fun g => liftLeft g r) ++ D.map (fun g => liftRight g q)

lemma leftCircuit_matrix {G : EffectiveGateSet} {q : ℕ} (C : EffectiveCircuit G q) (r : ℕ) :
    EffectiveCircuit.matrix (C.map (fun g => liftLeft g r)) =
      (Matrix.kronecker C.matrix (1 : Operator r)).submatrix (tensorBits q r) (tensorBits q r) := by
  induction C with
  | nil => simp [EffectiveCircuit.matrix,Matrix.kronecker,Matrix.one_kronecker_one,Matrix.submatrix_one_equiv]
  | cons g gs ih =>
    simp only [List.map_cons,EffectiveCircuit.matrix]
    rw [ih,liftLeft_matrix,Matrix.submatrix_mul_equiv]
    simp only [Matrix.kronecker,←Matrix.mul_kronecker_mul,one_mul]

lemma rightCircuit_matrix {G : EffectiveGateSet} {r : ℕ} (D : EffectiveCircuit G r) (q : ℕ) :
    EffectiveCircuit.matrix (D.map (fun g => liftRight g q)) =
      (Matrix.kronecker (1 : Operator q) D.matrix).submatrix (tensorBits q r) (tensorBits q r) := by
  induction D with
  | nil => simp [EffectiveCircuit.matrix,Matrix.kronecker,Matrix.one_kronecker_one,Matrix.submatrix_one_equiv]
  | cons g gs ih =>
    simp only [List.map_cons,EffectiveCircuit.matrix]
    rw [ih,liftRight_matrix,Matrix.submatrix_mul_equiv]
    simp only [Matrix.kronecker,←Matrix.mul_kronecker_mul,one_mul]

lemma tensorCircuit_matrix {G : EffectiveGateSet} {q r : ℕ} (C : EffectiveCircuit G q) (D : EffectiveCircuit G r) :
    (tensorCircuit C D).matrix = (Matrix.kronecker C.matrix D.matrix).submatrix
      (tensorBits q r) (tensorBits q r) := by
  rw [tensorCircuit,EffectiveCircuit.matrix_append,leftCircuit_matrix,rightCircuit_matrix,
    Matrix.submatrix_mul_equiv]
  simp only [Matrix.kronecker,←Matrix.mul_kronecker_mul,one_mul,mul_one]

@[simp] lemma tensorCircuit_length {G : EffectiveGateSet} {q r : ℕ}
    (C : EffectiveCircuit G q) (D : EffectiveCircuit G r) :
    (tensorCircuit C D).length = C.length + D.length := by simp [tensorCircuit]

/-- Chronological repetition contains no exponentiation oracle. -/
def repeatCircuit {G : EffectiveGateSet} {q : ℕ} (C : EffectiveCircuit G q) : ℕ → EffectiveCircuit G q
  | 0 => []
  | n+1 => repeatCircuit C n ++ C

lemma repeatCircuit_matrix {G : EffectiveGateSet} {q : ℕ} (C : EffectiveCircuit G q) (n : ℕ) :
    (repeatCircuit C n).matrix = C.matrix ^ n := by
  induction n with
  | zero => simp [repeatCircuit,EffectiveCircuit.matrix]
  | succ n ih => rw [repeatCircuit,EffectiveCircuit.matrix_append,ih,pow_succ']

lemma repeatCircuit_length {G : EffectiveGateSet} {q : ℕ} (C : EffectiveCircuit G q) (n : ℕ) :
    (repeatCircuit C n).length = n * C.length := by
  induction n with
  | zero => simp [repeatCircuit]
  | succ n ih => simp only [repeatCircuit,List.length_append,ih,Nat.succ_mul]


/-- A control is the first physical qubit, in exactly the basis used by the
proved one-clean density semantics. -/
def physicalControl {q : ℕ} (U : Operator q) : Operator (q+1) :=
  (OneCleanQubit.controlled U).submatrix (probeBasis q) (probeBasis q)

def physicalHadamard (q : ℕ) : Operator (q+1) :=
  (OneCleanQubit.hadamard : OneCleanQubit.ProbeMatrix (Basis q)).submatrix
    (probeBasis q) (probeBasis q)

lemma physicalControl_one (q : ℕ) : physicalControl (1 : Operator q) = 1 := by
  simp [physicalControl,OneCleanQubit.controlled,OneCleanQubit.block_identity]

lemma physicalControl_mul {q : ℕ} (U V : Operator q) :
    physicalControl (U*V) = physicalControl U * physicalControl V := by
  rw [physicalControl,physicalControl,physicalControl,Matrix.submatrix_mul_equiv]
  congr 1
  simp [OneCleanQubit.controlled,Matrix.fromBlocks_multiply]

/-- Selecting one classical label is a direct sum, including identity on every
other label. This retains all global phases of the selected unitary. -/
def patternBlock {ell q : ℕ} (label : Basis ell) (U : Operator q) :
    Matrix (Basis ell × Basis q) (Basis ell × Basis q) ℂ :=
  Paper25.selectMatrix (fun j => if j = label then U else 1)

def physicalPattern {ell q : ℕ} (label : Basis ell) (U : Operator q) : Operator (ell+q) :=
  (patternBlock label U).submatrix (registerBasis ell q) (registerBasis ell q)

lemma physicalPattern_one {ell q : ℕ} (label : Basis ell) :
    physicalPattern label (1 : Operator q) = 1 := by
  simp [physicalPattern,patternBlock,Paper25.selectMatrix_one]

lemma physicalPattern_mul {ell q : ℕ} (label : Basis ell) (U V : Operator q) :
    physicalPattern label (U*V) = physicalPattern label U * physicalPattern label V := by
  rw [physicalPattern,physicalPattern,physicalPattern,Matrix.submatrix_mul_equiv,
    patternBlock,patternBlock,patternBlock,Paper25.selectMatrix_mul]
  apply congrArg (fun M : Matrix (Basis ell × Basis q) (Basis ell × Basis q) ℂ =>
    M.submatrix (registerBasis ell q) (registerBasis ell q))
  apply congrArg (fun f : Basis ell → Operator q => Paper25.selectMatrix f)
  funext j
  by_cases hj : j = label <;> simp [hj]

def phaseMatrix (a : ℚ) : Operator 1 :=
  Matrix.diagonal (fun i => if i 0 = 0 then 1 else Complex.exp (Complex.I * (a : ℝ)))

def rotationMatrix (a : ℚ) : Operator 1 := fun i j =>
  if i 0 = j 0 then (Real.cos ((a : ℝ)/2) : ℂ)
  else if i 0 = 0 then -(Real.sin ((a : ℝ)/2) : ℂ) else (Real.sin ((a : ℝ)/2) : ℂ)

def pauliX : Operator 1 := fun i j => if i 0 = j 0 then 0 else 1

/-- The paper's elementary gate-description convention, made explicit.
All supplied operations act on a single constant-local primitive, apart from
an explicitly lifted standard Hadamard. The pattern compiler is a generic
multi-control primitive interface (e.g. a phase-sensitive Barenco decomposition),
not an implementation of the paper's spectral filter or catalytic reduction.
Its logspace generation is specified separately below. -/
structure GateConvention (G : EffectiveGateSet) where
  bound : ℕ
  bound_pos : 1 ≤ bound
  hadamardAt : (q : ℕ) → EffectiveCircuit G (q+1)
  hadamard_matrix : ∀ q, (hadamardAt q).matrix = physicalHadamard q
  hadamard_length : ∀ q, (hadamardAt q).length ≤ bound
  X : EffectiveCircuit G 1
  X_matrix : X.matrix = pauliX
  CNOT : EffectiveCircuit G 2
  CNOT_matrix : CNOT.matrix = physicalControl pauliX
  phaseRep : RationalRep → EffectiveCircuit G 1
  phaseRep_matrix : ∀ a, (phaseRep a).matrix = phaseMatrix a.value
  phaseRep_length : ∀ a, (phaseRep a).length ≤ bound
  rotationRep : RationalRep → EffectiveCircuit G 1
  rotationRep_matrix : ∀ a, (rotationRep a).matrix = rotationMatrix a.value
  rotationRep_length : ∀ a, (rotationRep a).length ≤ bound
  adjointAtom : {q : ℕ} → EffectiveLocalGate G q → EffectiveCircuit G q
  adjoint_matrix : ∀ {q} (g : EffectiveLocalGate G q), (adjointAtom g).matrix = g.matrix.conjTranspose
  adjoint_length : ∀ {q} (g : EffectiveLocalGate G q), (adjointAtom g).length ≤ bound
  conjugateAtom : {q : ℕ} → EffectiveLocalGate G q → EffectiveCircuit G q
  conjugate_matrix : ∀ {q} (g : EffectiveLocalGate G q),
    (conjugateAtom g).matrix = g.matrix.map (starRingEnd ℂ)
  conjugate_length : ∀ {q} (g : EffectiveLocalGate G q), (conjugateAtom g).length ≤ bound
  controlAtom : {q : ℕ} → EffectiveLocalGate G q → EffectiveCircuit G (q+1)
  control_matrix : ∀ {q} (g : EffectiveLocalGate G q), (controlAtom g).matrix = physicalControl g.matrix
  control_length : ∀ {q} (g : EffectiveLocalGate G q), (controlAtom g).length ≤ bound
  patternAtom : {q : ℕ} → (ell : ℕ) → Basis ell → EffectiveLocalGate G q → EffectiveCircuit G (ell+q)
  pattern_matrix : ∀ {q} ell label (g : EffectiveLocalGate G q),
    (patternAtom ell label g).matrix = physicalPattern label g.matrix
  pattern_length : ∀ {q} ell label (g : EffectiveLocalGate G q),
    (patternAtom ell label g).length ≤ bound^(ell+1)

/-- Canonical-rational helpers are semantic conveniences. Uniform numerical
compilation uses phaseRep/rotationRep with the actual unreduced output bytes. -/
def GateConvention.phase {G : EffectiveGateSet} (conv : GateConvention G) (a : ℚ) :
    EffectiveCircuit G 1 := conv.phaseRep (RationalRep.ofRat a)
lemma GateConvention.phase_matrix {G : EffectiveGateSet} (conv : GateConvention G) (a : ℚ) :
    (conv.phase a).matrix = phaseMatrix a := by
  simp only [phase,conv.phaseRep_matrix,RationalRep.ofRat_value]

def GateConvention.rotation {G : EffectiveGateSet} (conv : GateConvention G) (a : ℚ) :
    EffectiveCircuit G 1 := conv.rotationRep (RationalRep.ofRat a)
lemma GateConvention.rotation_matrix {G : EffectiveGateSet} (conv : GateConvention G) (a : ℚ) :
    (conv.rotation a).matrix = rotationMatrix a := by
  simp only [rotation,conv.rotationRep_matrix,RationalRep.ofRat_value]

def adjointCircuit {G : EffectiveGateSet} (conv : GateConvention G) {q : ℕ} :
    EffectiveCircuit G q → EffectiveCircuit G q
  | [] => []
  | g :: gs => adjointCircuit conv gs ++ conv.adjointAtom g

lemma adjointCircuit_matrix {G : EffectiveGateSet} (conv : GateConvention G) {q : ℕ}
    (C : EffectiveCircuit G q) : (adjointCircuit conv C).matrix = C.matrix.conjTranspose := by
  induction C with
  | nil => simp [adjointCircuit,EffectiveCircuit.matrix]
  | cons g gs ih =>
    rw [adjointCircuit,EffectiveCircuit.matrix_append,conv.adjoint_matrix,ih,
      EffectiveCircuit.matrix,Matrix.conjTranspose_mul]

lemma adjointCircuit_length {G : EffectiveGateSet} (conv : GateConvention G) {q : ℕ}
    (C : EffectiveCircuit G q) : (adjointCircuit conv C).length ≤ conv.bound*C.length := by
  induction C with
  | nil => simp [adjointCircuit]
  | cons g gs ih =>
    rw [adjointCircuit,List.length_append,List.length_cons,Nat.mul_succ]
    exact Nat.add_le_add ih (conv.adjoint_length g)

def conjugateCircuit {G : EffectiveGateSet} (conv : GateConvention G) {q : ℕ} :
    EffectiveCircuit G q → EffectiveCircuit G q
  | [] => []
  | g :: gs => conv.conjugateAtom g ++ conjugateCircuit conv gs

lemma conjugateCircuit_matrix {G : EffectiveGateSet} (conv : GateConvention G) {q : ℕ}
    (C : EffectiveCircuit G q) :
    (conjugateCircuit conv C).matrix = C.matrix.map (starRingEnd ℂ) := by
  induction C with
  | nil => simp [conjugateCircuit,EffectiveCircuit.matrix]
  | cons g gs ih =>
    rw [conjugateCircuit,EffectiveCircuit.matrix_append,ih,conv.conjugate_matrix,
      EffectiveCircuit.matrix,Matrix.map_mul]

lemma conjugateCircuit_length {G : EffectiveGateSet} (conv : GateConvention G) {q : ℕ}
    (C : EffectiveCircuit G q) : (conjugateCircuit conv C).length ≤ conv.bound*C.length := by
  induction C with
  | nil => simp [conjugateCircuit]
  | cons g gs ih =>
    rw [conjugateCircuit,List.length_append,List.length_cons,Nat.mul_succ]
    exact (Nat.add_le_add (conv.conjugate_length g) ih).trans_eq (Nat.add_comm _ _)

def controlledCircuit {G : EffectiveGateSet} (conv : GateConvention G) {q : ℕ} :
    EffectiveCircuit G q → EffectiveCircuit G (q+1)
  | [] => []
  | g :: gs => conv.controlAtom g ++ controlledCircuit conv gs

lemma controlledCircuit_matrix {G : EffectiveGateSet} (conv : GateConvention G) {q : ℕ}
    (C : EffectiveCircuit G q) : (controlledCircuit conv C).matrix = physicalControl C.matrix := by
  induction C with
  | nil => simp [controlledCircuit,EffectiveCircuit.matrix,physicalControl_one]
  | cons g gs ih =>
    rw [controlledCircuit,EffectiveCircuit.matrix_append,ih,conv.control_matrix,
      EffectiveCircuit.matrix,physicalControl_mul]

lemma controlledCircuit_length {G : EffectiveGateSet} (conv : GateConvention G) {q : ℕ}
    (C : EffectiveCircuit G q) : (controlledCircuit conv C).length ≤ conv.bound*C.length := by
  induction C with
  | nil => simp [controlledCircuit]
  | cons g gs ih =>
    rw [controlledCircuit,List.length_append,List.length_cons,Nat.mul_succ]
    exact (Nat.add_le_add (conv.control_length g) ih).trans_eq (Nat.add_comm _ _)

def patternCircuit {G : EffectiveGateSet} (conv : GateConvention G) {q : ℕ}
    (ell : ℕ) (label : Basis ell) : EffectiveCircuit G q → EffectiveCircuit G (ell+q)
  | [] => []
  | g :: gs => conv.patternAtom ell label g ++ patternCircuit conv ell label gs

lemma patternCircuit_matrix {G : EffectiveGateSet} (conv : GateConvention G) {q : ℕ}
    (ell : ℕ) (label : Basis ell) (C : EffectiveCircuit G q) :
    (patternCircuit conv ell label C).matrix = physicalPattern label C.matrix := by
  induction C with
  | nil => simp [patternCircuit,EffectiveCircuit.matrix,physicalPattern_one]
  | cons g gs ih =>
    rw [patternCircuit,EffectiveCircuit.matrix_append,ih,conv.pattern_matrix,
      EffectiveCircuit.matrix,physicalPattern_mul]

lemma patternCircuit_length {G : EffectiveGateSet} (conv : GateConvention G) {q : ℕ}
    (ell : ℕ) (label : Basis ell) (C : EffectiveCircuit G q) :
    (patternCircuit conv ell label C).length ≤ conv.bound^(ell+1)*C.length := by
  induction C with
  | nil => simp [patternCircuit]
  | cons g gs ih =>
    rw [patternCircuit,List.length_append,List.length_cons,Nat.mul_succ]
    exact (Nat.add_le_add (conv.pattern_length ell label g) ih).trans_eq (Nat.add_comm _ _)


/-- Explicit binary enumeration. It contains no `Fintype.equivFin` choice. -/
def binaryLabels : (ell : ℕ) → List (Basis ell)
  | 0 => [fun i => Fin.elim0 i]
  | ell+1 => (binaryLabels ell).map (Fin.cons 0) ++ (binaryLabels ell).map (Fin.cons 1)

lemma binaryLabels_complete (ell : ℕ) (b : Basis ell) : b ∈ binaryLabels ell := by
  induction ell with
  | zero =>
    have he : b = fun i => Fin.elim0 i := by funext i; exact Fin.elim0 i
    simp [binaryLabels,he]
  | succ ell ih =>
    have he : b = Fin.cons (b 0) (fun i => b i.succ) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    rw [he]
    have hb : b 0 = 0 ∨ b 0 = 1 := by
      have h := (b 0).isLt
      rcases (show (b 0).val = 0 ∨ (b 0).val = 1 by omega) with hb | hb
      · exact Or.inl (Fin.ext hb)
      · exact Or.inr (Fin.ext hb)
    rcases hb with hb | hb
    · rw [hb]
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨_,ih _,rfl⟩
    · rw [hb]
      apply List.mem_append_right
      exact List.mem_map.mpr ⟨_,ih _,rfl⟩

lemma binaryLabels_length (ell : ℕ) : (binaryLabels ell).length = 2^ell := by
  induction ell with
  | zero => simp [binaryLabels]
  | succ ell ih => simp [binaryLabels,ih,pow_succ]; omega

/-- Duplicate removal is an explicit finite equality scan. -/
def labels (ell : ℕ) : List (Basis ell) := (binaryLabels ell).dedup

lemma labels_nodup (ell : ℕ) : (labels ell).Nodup := List.nodup_dedup _

lemma labels_complete (ell : ℕ) (b : Basis ell) : b ∈ labels ell := by
  simpa only [labels,List.mem_dedup] using binaryLabels_complete ell b

lemma labels_length_le (ell : ℕ) : (labels ell).length ≤ 2^ell := by
  simpa only [labels,binaryLabels_length] using (List.dedup_sublist (binaryLabels ell)).length_le

/-- A finite SELECT is compiled by an explicit label scan, then a primitive-gate
scan inside each branch. No matrix entry oracle is used. -/
def selectListCircuit {G : EffectiveGateSet} (conv : GateConvention G) {ell q : ℕ}
    (family : Basis ell → EffectiveCircuit G q) : List (Basis ell) → EffectiveCircuit G (ell+q)
  | [] => []
  | label :: ls => patternCircuit conv ell label (family label) ++ selectListCircuit conv family ls

lemma selectListCircuit_matrix {G : EffectiveGateSet} (conv : GateConvention G) {ell q : ℕ}
    (family : Basis ell → EffectiveCircuit G q) (ls : List (Basis ell)) (hls : ls.Nodup) :
    (selectListCircuit conv family ls).matrix =
      (Paper25.selectMatrix (fun j => if j ∈ ls then (family j).matrix else 1)).submatrix
        (registerBasis ell q) (registerBasis ell q) := by
  induction ls with
  | nil => simp [selectListCircuit,EffectiveCircuit.matrix,Paper25.selectMatrix_one]
  | cons label ls ih =>
    have hn := List.nodup_cons.mp hls
    rw [selectListCircuit,EffectiveCircuit.matrix_append,ih hn.2,patternCircuit_matrix,
      physicalPattern,patternBlock,Matrix.submatrix_mul_equiv,Paper25.selectMatrix_mul]
    apply congrArg (fun M : Matrix (Basis ell × Basis q) (Basis ell × Basis q) ℂ =>
      M.submatrix (registerBasis ell q) (registerBasis ell q))
    apply congrArg (fun f : Basis ell → Operator q => Paper25.selectMatrix f)
    funext j
    by_cases hj : j = label
    · subst j
      simp [hn.1]
    · simp [hj]

def selectCircuit {G : EffectiveGateSet} (conv : GateConvention G) {ell q : ℕ}
    (family : Basis ell → EffectiveCircuit G q) : EffectiveCircuit G (ell+q) :=
  selectListCircuit conv family (labels ell)

lemma selectCircuit_matrix {G : EffectiveGateSet} (conv : GateConvention G) {ell q : ℕ}
    (family : Basis ell → EffectiveCircuit G q) :
    (selectCircuit conv family).matrix =
      (Paper25.selectMatrix (fun j => (family j).matrix)).submatrix
        (registerBasis ell q) (registerBasis ell q) := by
  rw [selectCircuit,selectListCircuit_matrix _ _ _ (labels_nodup ell)]
  simp only [labels_complete,ite_true]

lemma selectListCircuit_length {G : EffectiveGateSet} (conv : GateConvention G) {ell q : ℕ}
    (family : Basis ell → EffectiveCircuit G q) (ls : List (Basis ell)) :
    (selectListCircuit conv family ls).length ≤
      conv.bound^(ell+1) * (ls.map (fun j => (family j).length)).sum := by
  induction ls with
  | nil => simp [selectListCircuit]
  | cons label ls ih =>
    rw [selectListCircuit,List.length_append,List.map_cons,List.sum_cons,Nat.mul_add]
    exact Nat.add_le_add (patternCircuit_length conv ell label _) ih

lemma selectCircuit_length {G : EffectiveGateSet} (conv : GateConvention G) {ell q : ℕ}
    (family : Basis ell → EffectiveCircuit G q) (B : ℕ) (hB : ∀ j, (family j).length ≤ B) :
    (selectCircuit conv family).length ≤ 2^ell * conv.bound^(ell+1) * B := by
  have hs : ∀ ls : List (Basis ell),
      (ls.map (fun j => (family j).length)).sum ≤ ls.length * B := by
    intro ls
    induction ls with
    | nil => simp
    | cons j ls ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul]
      exact (Nat.add_le_add (hB j) ih).trans_eq (Nat.add_comm _ _)
  calc
    _ ≤ conv.bound^(ell+1) * ((labels ell).map (fun j => (family j).length)).sum :=
      selectListCircuit_length conv family _
    _ ≤ conv.bound^(ell+1) * ((labels ell).length * B) := Nat.mul_le_mul_left _ (hs _)
    _ ≤ conv.bound^(ell+1) * (2^ell * B) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (labels_length_le ell))
    _ = _ := by ring

/-- Expanded powers: branch j contains the literal repeated walk gate list. -/
def powerSelectCircuit {G : EffectiveGateSet} (conv : GateConvention G) {ell q : ℕ}
    (index : Basis ell → ℕ) (C : EffectiveCircuit G q) : EffectiveCircuit G (ell+q) :=
  selectCircuit conv (fun label => repeatCircuit C (index label))

lemma powerSelectCircuit_matrix {G : EffectiveGateSet} (conv : GateConvention G) {ell q : ℕ}
    (index : Basis ell → ℕ) (C : EffectiveCircuit G q) :
    (powerSelectCircuit conv index C).matrix =
      (Paper25.selectMatrix (fun label => C.matrix^(index label))).submatrix
        (registerBasis ell q) (registerBasis ell q) := by
  simp only [powerSelectCircuit,selectCircuit_matrix,repeatCircuit_matrix]

/-- The standard PE sandwich is assembled from actual Fourier and power lists.
The supplied Fourier list acts on all declared qubits (identity on the data). -/
def phaseEstimationCircuit {G : EffectiveGateSet} (conv : GateConvention G) {ell q : ℕ}
    (index : Basis ell → ℕ) (walk : EffectiveCircuit G q)
    (fourier : EffectiveCircuit G (ell+q)) : EffectiveCircuit G (ell+q) :=
  fourier ++ powerSelectCircuit conv index walk ++ adjointCircuit conv fourier

lemma phaseEstimationCircuit_matrix {G : EffectiveGateSet} (conv : GateConvention G) {ell q : ℕ}
    (index : Basis ell → ℕ) (walk : EffectiveCircuit G q)
    (fourier : EffectiveCircuit G (ell+q)) :
    (phaseEstimationCircuit conv index walk fourier).matrix =
      fourier.matrix.conjTranspose *
        (Paper25.selectMatrix (fun label => walk.matrix^(index label))).submatrix
          (registerBasis ell q) (registerBasis ell q) * fourier.matrix := by
  simp only [phaseEstimationCircuit,EffectiveCircuit.matrix_append,
    adjointCircuit_matrix,powerSelectCircuit_matrix,mul_assoc]

/-- Equation (16)'s actual unitary circuit: PE, enumerated label rotations,
then the actual inverse PE gate list. -/
def coherentFilterCircuit {G : EffectiveGateSet} (conv : GateConvention G) {q : ℕ}
    (PE labelRotation : EffectiveCircuit G q) : EffectiveCircuit G q :=
  PE ++ labelRotation ++ adjointCircuit conv PE

lemma coherentFilterCircuit_matrix {G : EffectiveGateSet} (conv : GateConvention G) {q : ℕ}
    (PE labelRotation : EffectiveCircuit G q) :
    (coherentFilterCircuit conv PE labelRotation).matrix =
      PE.matrix.conjTranspose * labelRotation.matrix * PE.matrix := by
  simp only [coherentFilterCircuit,EffectiveCircuit.matrix_append,adjointCircuit_matrix,mul_assoc]

/-- Actual final Hadamard/control/Hadamard gate list. -/
def readoutCircuit {G : EffectiveGateSet} (conv : GateConvention G) {q : ℕ}
    (C : EffectiveCircuit G q) : EffectiveTargetCircuit G where
  mixedQubits := q
  gates := conv.hadamardAt q ++ controlledCircuit conv C ++ conv.hadamardAt q

lemma readoutCircuit_matrix {G : EffectiveGateSet} (conv : GateConvention G) {q : ℕ}
    (C : EffectiveCircuit G q) :
    (readoutCircuit conv C).matrix = OneCleanQubit.circuit C.matrix := by
  unfold EffectiveTargetCircuit.matrix readoutCircuit
  simp only [EffectiveCircuit.matrix_append,conv.hadamard_matrix,controlledCircuit_matrix]
  simp only [physicalHadamard,physicalControl,Matrix.submatrix_mul_equiv]
  ext i j
  simp [Matrix.submatrix_apply,OneCleanQubit.circuit,mul_assoc]

lemma readoutCircuit_accept {G : EffectiveGateSet} (conv : GateConvention G) {q : ℕ}
    (C : EffectiveCircuit G q) :
    (readoutCircuit conv C).accept = OneCleanQubit.probZero (OneCleanQubit.output C.matrix) := by
  rw [EffectiveTargetCircuit.accept,EffectiveTargetCircuit.output,readoutCircuit_matrix]
  rfl

lemma readoutCircuit_length {G : EffectiveGateSet} (conv : GateConvention G) {q : ℕ}
    (C : EffectiveCircuit G q) : (readoutCircuit conv C).gateCount ≤ conv.bound*(C.length+2) := by
  dsimp [EffectiveTargetCircuit.gateCount,readoutCircuit]
  simp only [List.length_append]
  have h := controlledCircuit_length conv C
  have hh := conv.hadamard_length q
  nlinarith

end Paper25.OperationalModel.LocalCompilation
