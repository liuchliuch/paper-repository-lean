import Paper25.SourceHistoryCompilation
import Paper25.NativeReadoutCompilation
import Paper25.WalkSelectedFilter

/-! Actual compression-walk gates for the compiled source history encoder.
The original four block bits are tested coherently in both h sectors. -/
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
namespace Paper25.SourceWalkCompilation
open OperationalModel OperationalModel.LocalCompilation SourceHistoryCompilation
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1500000
set_option synthInstance.maxSize 512

lemma pairBlocks {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ) :
    (selectMatrix (![A,B] : Fin 2 → Matrix n n ℂ)).submatrix
      OneCleanQubit.tensorBasis.symm OneCleanQubit.tensorBasis.symm = Matrix.fromBlocks A 0 0 B := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [selectMatrix,OneCleanQubit.tensorBasis,Matrix.fromBlocks]

lemma hermitianDilation_error {n : Type*} [Fintype n] [DecidableEq n]
    (U V : Matrix n n ℂ) (τ : ℝ) (hτ : 0 ≤ τ) (hUV : ‖U-V‖ ≤ τ) :
    ‖hermitianDilation U - hermitianDilation V‖ ≤ τ := by
  have hs : ‖selectMatrix (![U.conjTranspose,U] : Fin 2 → Matrix n n ℂ) -
      selectMatrix (![V.conjTranspose,V] : Fin 2 → Matrix n n ℂ)‖ ≤ τ := by
    apply MatrixCompilationNorm.selectMatrix_error _ _ τ hτ
    intro j
    fin_cases j
    · change ‖U.conjTranspose-V.conjTranspose‖ ≤ τ
      rw [MatrixCompilationNorm.adjoint_sub_opNorm]
      exact hUV
    · exact hUV
  have hb : ‖Matrix.fromBlocks U.conjTranspose 0 0 U - Matrix.fromBlocks V.conjTranspose 0 0 V‖ ≤ τ := by
    rw [←pairBlocks,←pairBlocks,MatrixCompilationNorm.submatrix_equiv_error]
    exact hs
  have hu : (probeFlip : OneCleanQubit.ProbeMatrix n) ∈ Matrix.unitaryGroup _ ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    change (probeFlip : OneCleanQubit.ProbeMatrix n).conjTranspose * probeFlip = 1
    simp [probeFlip,Matrix.fromBlocks_conjTranspose,Matrix.fromBlocks_multiply,OneCleanQubit.block_identity]
  have he : hermitianDilation U - hermitianDilation V =
      probeFlip * (Matrix.fromBlocks U.conjTranspose 0 0 U - Matrix.fromBlocks V.conjTranspose 0 0 V) := by
    simp [probeFlip,hermitianDilation,mul_sub,Matrix.fromBlocks_multiply,Matrix.star_eq_conjTranspose]
  rw [he]
  exact (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_right
    (MatrixCompilationNorm.unitary_opNorm_le_one _ hu) (norm_nonneg _)).trans (by simpa using hb))

lemma blockColumn_projector {a n : Type*} [Fintype a] [DecidableEq a]
    [Fintype n] [DecidableEq n] (q : a) :
    isometryProjector (SelectedFilter.blockColumn (ι := n) q) =
      Matrix.fromBlocks
        (OneCleanQubit.ancillaryProjector (n := Fin (Fintype.card n)) a q) 0 0
        (OneCleanQubit.ancillaryProjector (n := Fin (Fintype.card n)) a q) := by
  ext x y
  rcases x with ⟨a,i⟩ | ⟨a,i⟩ <;> rcases y with ⟨b,j⟩ | ⟨b,j⟩ <;>
    by_cases ha : a=q <;> by_cases hb : b=q <;> by_cases hij : i=j <;> by_cases hab : a=b <;>
    simp [isometryProjector,SelectedFilter.blockColumn,SelectedFilter.basisColumn,
      SelectedFilter.blockEmbedding,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Fintype.sum_sum_type,OneCleanQubit.ancillaryProjector,Matrix.diagonal_apply,
      Matrix.fromBlocks,Prod.mk.injEq,apply_ite,ite_and,ha,hb,hij,hab] <;> aesop

/-- The prefix-four form uses only a value-preserving relabeling of wire
numbers. No quantum permutation or initialized workspace is introduced. -/
def prefixWire {G : EffectiveGateSet} (S : EffectiveSourceComputation G) (ell : ℕ) :
    Fin (1+(3+(ell+DataQubits S))) ≃ Fin (4+(ell+DataQubits S)) := finCongr (by omega)

def encoder {G : EffectiveGateSet} (conv : GateConvention G) (S : EffectiveSourceComputation G)
    (ell : ℕ) (prepare : EffectiveCircuit G 1) : EffectiveCircuit G (4+(ell+DataQubits S)) :=
  rewireCircuit (prefixWire S ell) (SourceHistoryCompilation.circuit conv S ell prepare)

def encoderLayout {G : EffectiveGateSet} (S : EffectiveSourceComputation G) (ell : ℕ) :=
  (rewireBasis (prefixWire S ell)).trans (enumeratedLayout S ell)

def ancilla4 : Basis 4 ≃ HistoryEncoding.BlockAncilla :=
  (registerBasis 1 3).trans (oneBit.prodCongr uniform3Layout)

lemma ancilla4_zero : ancilla4 (fun _ => 0) = (0,zeroSelector3) := rfl

lemma encoderLayout_fst {G : EffectiveGateSet} (S : EffectiveSourceComputation G) (ell : ℕ)
    (x : Basis (4+(ell+DataQubits S))) :
    (encoderLayout S ell x).1 = ancilla4 ((registerBasis 4 (ell+DataQubits S) x).1) := by
  dsimp [encoderLayout,enumeratedLayout,SourceHistoryCompilation.layout,historyALayout,
    differenceLayout,historyLayout,HistoryEncoding.encodingIndex,rewireBasis,prefixWire,
    registerBasis,ancilla4]
  apply Prod.ext
  · rfl
  · apply congrArg uniform3Layout
    funext i
    rfl

lemma encoder_error {G : EffectiveGateSet} (conv : GateConvention G)
    (S : EffectiveSourceComputation G) (ell : ℕ) (prepare : EffectiveCircuit G 1)
    (τ : ℝ) (hprepare : ‖prepare.matrix - prepareThird.submatrix oneBit oneBit‖ ≤ τ) :
    ‖(encoder conv S ell prepare).matrix -
      (HistoryEncoding.enumeratedAEncoding (SourceCoordinates.expanded S).length
        (Fintype.card (Basis ell)) (SourceCoordinates.canonicalK S)).submatrix
        (encoderLayout S ell) (encoderLayout S ell)‖ ≤ 2*τ := by
  rw [encoder,rewireCircuit_matrix]
  have h := SourceHistoryCompilation.circuit_error_enumerated conv S ell prepare τ hprepare
  rw [←MatrixCompilationNorm.submatrix_equiv_error (rewireBasis (prefixWire S ell))] at h
  exact h

/-- Reflection on the original block ancillas, using a data bit only as a
phase target; its state is unrestricted. -/
def reflection {G : EffectiveGateSet} (conv : GateConvention G) (S : EffectiveSourceComputation G)
    (ell : ℕ) : EffectiveCircuit G (4+(ell+DataQubits S)) :=
  rewireCircuit (finCongr (show 4+((ell+DataQubits S-1)+1)=4+(ell+DataQubits S) by
    have h := dataQubits_pos S
    omega)) (zeroReflectionCircuit conv 4 (ell+DataQubits S-1))

lemma reflection_matrix {G : EffectiveGateSet} (conv : GateConvention G)
    (S : EffectiveSourceComputation G) (ell : ℕ) :
    (reflection conv S ell).matrix =
      (projectorReflection (OneCleanQubit.ancillaryProjector
        (n := Fin (Fintype.card (Fin (Fintype.card (Basis ell)) × CanonicalData S)))
        HistoryEncoding.BlockAncilla (0,zeroSelector3))).submatrix
        (encoderLayout S ell) (encoderLayout S ell) := by
  rw [reflection,rewireCircuit_matrix,zeroReflectionCircuit_matrix]
  ext x y
  simp only [Matrix.submatrix_apply,projectorReflection,Matrix.sub_apply,Matrix.smul_apply,
    OneCleanQubit.ancillaryProjector,Matrix.diagonal_apply,Matrix.one_apply]
  have hx := encoderLayout_fst S ell x
  have he : (encoderLayout S ell x).1 = (0,zeroSelector3) ↔
      (fun i : Fin 4 => x (Fin.castAdd (ell+DataQubits S) i)) = (fun _ => 0) := by
    rw [hx,←ancilla4_zero,ancilla4.injective.eq_iff]
    rfl
  have hxy := (encoderLayout S ell).injective.eq_iff (a := x) (b := y)
  have hpos : 0 < ell+DataQubits S := by have h := dataQubits_pos S; omega
  let ew := rewireBasis (finCongr (show 4+((ell+DataQubits S-1)+1)=4+(ell+DataQubits S) by omega))
  let er := ew.trans (registerBasis 4 ((ell+DataQubits S-1)+1))
  have heq : er x = er y ↔ x=y := er.injective.eq_iff
  have hpre : (er x).1 = (fun i : Fin 4 => x (Fin.castAdd (ell+DataQubits S) i)) := rfl
  change (2 • (if er x = er y then (if (er x).1 = (fun _ => 0) then (1:ℂ) else 0) else 0) -
    (if er x=er y then 1 else 0)) = _
  simp only [heq,hpre,he,hxy]

def walkLayout {G : EffectiveGateSet} (S : EffectiveSourceComputation G) (ell : ℕ) :=
  (probeBasis (4+(ell+DataQubits S))).trans
    ((encoderLayout S ell).sumCongr (encoderLayout S ell))

def circuit {G : EffectiveGateSet} (conv : GateConvention G) (S : EffectiveSourceComputation G)
    (ell : ℕ) (prepare : EffectiveCircuit G 1) : EffectiveCircuit G ((4+(ell+DataQubits S))+1) :=
  walkCircuit conv (encoder conv S ell prepare) (dataCircuit (reflection conv S ell))

def idealEncoder {G : EffectiveGateSet} (S : EffectiveSourceComputation G) (ell : ℕ) :=
  HistoryEncoding.enumeratedAEncoding (SourceCoordinates.expanded S).length
    (Fintype.card (Basis ell)) (SourceCoordinates.canonicalK S)

def idealWalk {G : EffectiveGateSet} (S : EffectiveSourceComputation G) (ell : ℕ) :=
  (SelectedFilter.blockWalk (idealEncoder S ell) (0,zeroSelector3)).submatrix
    (walkLayout S ell) (walkLayout S ell)

lemma fullReflection_matrix {G : EffectiveGateSet} (conv : GateConvention G)
    (S : EffectiveSourceComputation G) (ell : ℕ) :
    (dataCircuit (reflection conv S ell)).matrix =
      (projectorReflection (isometryProjector (SelectedFilter.blockColumn
        (ι := Fin (Fintype.card (Basis ell)) × CanonicalData S) (0,zeroSelector3)))).submatrix
        (walkLayout S ell) (walkLayout S ell) := by
  rw [dataCircuit_matrix,physicalData,reflection_matrix]
  have hb : Matrix.fromBlocks
      (((projectorReflection (OneCleanQubit.ancillaryProjector
        (n := Fin (Fintype.card (Fin (Fintype.card (Basis ell)) × CanonicalData S)))
        HistoryEncoding.BlockAncilla (0,zeroSelector3))).submatrix (encoderLayout S ell) (encoderLayout S ell)))
      0 0
      (((projectorReflection (OneCleanQubit.ancillaryProjector
        (n := Fin (Fintype.card (Fin (Fintype.card (Basis ell)) × CanonicalData S)))
        HistoryEncoding.BlockAncilla (0,zeroSelector3))).submatrix (encoderLayout S ell) (encoderLayout S ell))) =
      (projectorReflection (isometryProjector (SelectedFilter.blockColumn
        (ι := Fin (Fintype.card (Basis ell)) × CanonicalData S) (0,zeroSelector3)))).submatrix
        ((encoderLayout S ell).sumCongr (encoderLayout S ell))
        ((encoderLayout S ell).sumCongr (encoderLayout S ell)) := by
    rw [blockColumn_projector]
    ext x y
    rcases x with x | x <;> rcases y with y | y <;>
      simp only [projectorReflection,Matrix.submatrix_apply,Matrix.sub_apply,Matrix.smul_apply,
        Equiv.sumCongr_apply,Sum.map_inl,Sum.map_inr,Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,
        Matrix.one_apply,Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl]
    all_goals simp [(encoderLayout S ell).injective.eq_iff]
  rw [hb]
  rfl

lemma dilation_error {G : EffectiveGateSet} (conv : GateConvention G)
    (S : EffectiveSourceComputation G) (ell : ℕ) (prepare : EffectiveCircuit G 1)
    (τ : ℝ) (hprepare : ‖prepare.matrix - prepareThird.submatrix oneBit oneBit‖ ≤ τ) :
    ‖(dilationCircuit conv (encoder conv S ell prepare)).matrix -
      (hermitianDilation (idealEncoder S ell)).submatrix
        (walkLayout S ell) (walkLayout S ell)‖ ≤ 2*τ := by
  have hτ : 0 ≤ τ := (norm_nonneg _).trans hprepare
  have h := hermitianDilation_error (encoder conv S ell prepare).matrix
    ((idealEncoder S ell).submatrix (encoderLayout S ell) (encoderLayout S ell))
    (2*τ) (by positivity) (encoder_error conv S ell prepare τ hprepare)
  rw [←hermitianDilation_submatrix] at h
  rw [←MatrixCompilationNorm.submatrix_equiv_error (probeBasis (4+(ell+DataQubits S)))] at h
  rw [dilationCircuit_matrix]
  exact h

/-- The native walk error is no larger than the encoder error: the doubled
adjoint blocks form a direct sum, and the exact reflection is unitary. -/
theorem circuit_error {G : EffectiveGateSet} (conv : GateConvention G)
    (S : EffectiveSourceComputation G) (ell : ℕ) (prepare : EffectiveCircuit G 1)
    (τ : ℝ) (hprepare : ‖prepare.matrix - prepareThird.submatrix oneBit oneBit‖ ≤ τ) :
    ‖(circuit conv S ell prepare).matrix - idealWalk S ell‖ ≤ 2*τ := by
  let R := (dataCircuit (reflection conv S ell)).matrix
  have hR : R ∈ Matrix.unitaryGroup _ ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    exact (dataCircuit (reflection conv S ell)).unitary.1
  have he : idealWalk S ell = R *
      (hermitianDilation (idealEncoder S ell)).submatrix
        (walkLayout S ell) (walkLayout S ell) := by
    rw [show R = _ from fullReflection_matrix conv S ell,Matrix.submatrix_mul_equiv]
    rfl
  rw [circuit,walkCircuit,EffectiveCircuit.matrix_append,he,←mul_sub]
  exact (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_right
    (MatrixCompilationNorm.unitary_opNorm_le_one _ hR) (norm_nonneg _)).trans
      (by simpa only [one_mul] using dilation_error conv S ell prepare τ hprepare))

lemma idealWalk_unitary {G : EffectiveGateSet} (S : EffectiveSourceComputation G) (ell : ℕ) :
    idealWalk S ell ∈ Matrix.unitaryGroup _ ℂ := by
  have hU : idealEncoder S ell ∈ Matrix.unitaryGroup _ ℂ :=
    HistoryEncoding.enumeratedAEncoding_unitary (SourceCoordinates.canonicalK S)
      (fun t ht j => SourceCoordinates.canonicalK_unitary S t j)
  have hW := compressionWalk_unitary
    (isometryProjector (SelectedFilter.blockColumn (ι := Fin (Fintype.card (Basis ell)) × CanonicalData S)
      (0,zeroSelector3))) (hermitianDilation (idealEncoder S ell))
    (isometryProjector_hermitian _) (isometryProjector_sq _ (SelectedFilter.blockColumn_isometry _))
    (hermitianDilation_unitary _ hU)
  rw [Matrix.mem_unitaryGroup_iff']
  change (idealWalk S ell).conjTranspose * idealWalk S ell = 1
  unfold idealWalk
  have hw' : (SelectedFilter.blockWalk (idealEncoder S ell) (0,zeroSelector3)).conjTranspose *
      SelectedFilter.blockWalk (idealEncoder S ell) (0,zeroSelector3) = 1 := hW.1
  rw [Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv,hw',Matrix.submatrix_one_equiv]

def encoderGateBound {G : EffectiveGateSet} (conv : GateConvention G) (ell prepareLength : ℕ) : ℕ :=
  (conv.bound+1)*prepareLength + 2*conv.bound^2 *
    (2^ell*conv.bound^(ell+1)*((conv.bound+1)*(3*conv.bound)+
      8*conv.bound^4*(SourceTermCompilation.sourceTermBound conv+4*(conv.X.length+conv.bound))) +
      (2^ell)^(conv.bound+1)*conv.X.length + 4*(conv.X.length+conv.bound))

lemma encoder_length {G : EffectiveGateSet} (conv : GateConvention G)
    (S : EffectiveSourceComputation G) (ell : ℕ) (prepare : EffectiveCircuit G 1) :
    (encoder conv S ell prepare).length ≤ encoderGateBound conv ell prepare.length := by
  simpa only [encoder,rewireCircuit_length,encoderGateBound] using
    SourceHistoryCompilation.circuit_length conv S ell prepare

lemma reflection_length {G : EffectiveGateSet} (conv : GateConvention G)
    (S : EffectiveSourceComputation G) (ell : ℕ) :
    (reflection conv S ell).length ≤ 16*conv.bound^5*(4*(conv.X.length+conv.bound)) := by
  simpa only [reflection,rewireCircuit_length] using
    zeroReflectionCircuit_length conv 4 (ell+DataQubits S-1)

lemma circuit_length {G : EffectiveGateSet} (conv : GateConvention G)
    (S : EffectiveSourceComputation G) (ell : ℕ) (prepare : EffectiveCircuit G 1) :
    (circuit conv S ell prepare).length ≤
      3*conv.X.length + (conv.bound^2+conv.bound)*encoderGateBound conv ell prepare.length +
        16*conv.bound^5*(4*(conv.X.length+conv.bound)) := by
  simp only [circuit,walkCircuit,List.length_append,dataCircuit,embedCircuit_length]
  apply Nat.add_le_add
  · exact (dilationCircuit_length conv _).trans (Nat.add_le_add_left
      (Nat.mul_le_mul_left _ (encoder_length conv S ell prepare)) _)
  · exact reflection_length conv S ell

end Paper25.SourceWalkCompilation
