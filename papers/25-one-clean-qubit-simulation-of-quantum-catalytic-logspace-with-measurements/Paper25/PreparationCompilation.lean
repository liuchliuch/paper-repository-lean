import Paper25.SourceTermCompilation
import Paper25.StatePreparationLocal

/-! Compile the proved physical F preparation from the fixed H/X/Z/CNOT
alphabet into the source/simulator's common effective gate convention. -/
noncomputable section
open Matrix
namespace Paper25.OperationalModel.LocalCompilation
open StatePreparation StatePreparationLocal
attribute [local instance] Classical.propDecidable
variable {G : EffectiveGateSet}

lemma hadamard_single_matrix : physicalHadamard 0 = H2.submatrix oneBit oneBit := by
  ext x y
  have ht : (fun i : Fin 0 => x i.succ) = (fun i : Fin 0 => y i.succ) := Subsingleton.elim _ _
  rcases SourceTermCompilation.bit_cases (x 0) with hx | hx <;>
    rcases SourceTermCompilation.bit_cases (y 0) with hy | hy <;>
      simp [physicalHadamard, probeBasis, probeTensor, OneCleanQubit.tensorBasis,
        OneCleanQubit.hadamard, Matrix.submatrix_apply, Matrix.fromBlocks, Matrix.one_apply,
        oneBit, H2_apply, hx,hy,ht]

lemma cnot_single_matrix : physicalControl pauliX = CNOT.submatrix twoBits twoBits := by
  ext x y
  have ht : (fun i : Fin 1 => x i.succ) = (fun i : Fin 1 => y i.succ) ↔ x 1 = y 1 := by
    constructor
    · intro h; exact congrFun h 0
    · intro h; funext i; fin_cases i; exact h
  rcases SourceTermCompilation.bit_cases (x 0) with hx | hx <;>
    rcases SourceTermCompilation.bit_cases (y 0) with hy | hy <;>
      rcases SourceTermCompilation.bit_cases (x 1) with hxx | hxx <;>
        rcases SourceTermCompilation.bit_cases (y 1) with hyy | hyy <;>
          simp [physicalControl, OneCleanQubit.controlled, probeBasis, probeTensor,
            OneCleanQubit.tensorBasis, Matrix.fromBlocks, Matrix.submatrix_apply,
            Matrix.one_apply, pauliX, CNOT, twoBits, hx,hy,hxx,hyy,ht] <;>
          aesop

def elementaryImplementation (conv : GateConvention G) :
    (a : Fin 4) → EffectiveCircuit G (elementaryArity a) :=
  Fin.cases (conv.hadamardAt 0) (Fin.cases conv.X
    (Fin.cases (SourceTermCompilation.zCircuit conv) (fun _ => conv.CNOT)))

theorem elementaryImplementation_matrix (conv : GateConvention G) (a : Fin 4) :
    (elementaryImplementation conv a).matrix = elementaryMatrix a := by
  fin_cases a
  · exact (conv.hadamard_matrix 0).trans hadamard_single_matrix
  · exact SourceTermCompilation.x_matrix conv
  · exact SourceTermCompilation.zCircuit_matrix conv
  · exact conv.CNOT_matrix.trans cnot_single_matrix

def compileElementaryGate (conv : GateConvention G) {q : ℕ}
    (g : LocalGate elementary q) : EffectiveCircuit G q :=
  embedCircuit g.placement (elementaryImplementation conv g.symbol)

theorem compileElementaryGate_matrix (conv : GateConvention G) {q : ℕ}
    (g : LocalGate elementary q) : (compileElementaryGate conv g).matrix = g.matrix := by
  rw [compileElementaryGate, embedCircuit_matrix, elementaryImplementation_matrix]
  rfl

def compileElementary (conv : GateConvention G) {q : ℕ}
    (C : Circuit elementary q) : EffectiveCircuit G q := C.flatMap (compileElementaryGate conv)

theorem compileElementary_matrix (conv : GateConvention G) {q : ℕ}
    (C : Circuit elementary q) : (compileElementary conv C).matrix = C.matrix := by
  induction C with
  | nil => rfl
  | cons g gs ih =>
    change (compileElementaryGate conv g ++ compileElementary conv gs).matrix = _
    rw [EffectiveCircuit.matrix_append, ih, compileElementaryGate_matrix]
    rfl

def preparationCost (conv : GateConvention G) : ℕ :=
  2*conv.bound+conv.X.length+conv.CNOT.length

lemma elementaryImplementation_length (conv : GateConvention G) (a : Fin 4) :
    (elementaryImplementation conv a).length ≤ preparationCost conv := by
  fin_cases a
  · have h := conv.hadamard_length 0
    change (conv.hadamardAt 0).length ≤ preparationCost conv
    unfold preparationCost
    omega
  · change conv.X.length ≤ preparationCost conv
    unfold preparationCost
    omega
  · change (SourceTermCompilation.zCircuit conv).length ≤ preparationCost conv
    simp only [SourceTermCompilation.zCircuit, List.length_append, flipCircuit, embedCircuit_length]
    have h := conv.hadamard_length 0
    unfold preparationCost
    omega
  · change conv.CNOT.length ≤ preparationCost conv
    unfold preparationCost
    omega

theorem compileElementary_length (conv : GateConvention G) {q : ℕ}
    (C : Circuit elementary q) :
    (compileElementary conv C).length ≤ preparationCost conv*C.length := by
  induction C with
  | nil => simp [compileElementary]
  | cons g gs ih =>
    change (compileElementaryGate conv g ++ compileElementary conv gs).length ≤ _
    rw [List.length_append, List.length_cons, Nat.mul_succ]
    have h : (compileElementaryGate conv g).length ≤ preparationCost conv := by
      rw [compileElementaryGate, embedCircuit_length]
      exact elementaryImplementation_length conv g.symbol
    omega

def nativeF (conv : GateConvention G) (ell s r : ℕ) (t : Bits ell) :
    EffectiveCircuit G (physicalSize ell s r) := compileElementary conv (physicalF ell s r t)

theorem nativeF_matrix (conv : GateConvention G) (ell s r : ℕ) (t : Bits ell) :
    (nativeF conv ell s r t).matrix = (F ell s r t).submatrix
      (FLayout ell s r) (FLayout ell s r) := by
  rw [nativeF, compileElementary_matrix, physicalF_matrix]

theorem nativeF_length (conv : GateConvention G) (ell s r : ℕ) (t : Bits ell) :
    (nativeF conv ell s r t).length ≤ preparationCost conv*(ell+2*s+6) :=
  (compileElementary_length conv _).trans
    (Nat.mul_le_mul_left _ (physicalF_length ell s r t))

end Paper25.OperationalModel.LocalCompilation
