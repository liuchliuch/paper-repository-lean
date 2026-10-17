import Paper25.HistoryCompilation
import Paper25.SourceTermCompilation
import Paper25.MatrixCompilationNorm

/-! The source history encoding is instantiated with actual native circuits for
every expanded source term. There is no externally supplied LCU implementation:
the only remaining numerical component is the one-qubit weighted PREPARE. -/
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
namespace Paper25.SourceHistoryCompilation
open OperationalModel OperationalModel.LocalCompilation SourceTermCompilation
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1500000
set_option synthInstance.maxSize 512

lemma eightLCU_data_reindex {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (e : a ≃ b) (K : Fin 8 → Matrix b b ℂ) :
    eightLCU (fun j => (K j).submatrix e e) =
      (eightLCU K).submatrix ((Equiv.refl Selector3).prodCongr e)
        ((Equiv.refl Selector3).prodCongr e) := by
  have h := lcuMatrix_reindex (Equiv.refl Selector3) e uniformPrepare3
    (fun j => K (selectorIndex3 j))
  exact h

lemma inactiveTerms_reindex {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (e : a ≃ b) (j : Fin 8) :
    (inactiveTerms : Fin 8 → Matrix a a ℂ) j =
      ((inactiveTerms : Fin 8 → Matrix b b ℂ) j).submatrix e e := by
  fin_cases j <;> ext x y <;>
    simp [inactiveTerms,Matrix.submatrix_apply,Matrix.one_apply,e.injective.eq_iff]

lemma clockSelected_data_reindex {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (e : a ≃ b) {T J : ℕ}
    (K : ℕ → Fin 8 → Matrix b b ℂ) (r : Fin J) :
    HistoryEncoding.clockSelected (T := T) (fun t j => (K t j).submatrix e e) r =
      (HistoryEncoding.clockSelected (T := T) K r).submatrix
        ((Equiv.refl Selector3).prodCongr e) ((Equiv.refl Selector3).prodCongr e) := by
  unfold HistoryEncoding.clockSelected
  split_ifs
  · exact eightLCU_data_reindex e _
  · have hi : (inactiveTerms : Fin 8 → Matrix a a ℂ) =
        (fun j => ((inactiveTerms : Fin 8 → Matrix b b ℂ) j).submatrix e e) := by
      funext j
      exact inactiveTerms_reindex e j
    rw [hi,eightLCU_data_reindex]

lemma historyUnitary_data_reindex {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (e : a ≃ b) (T J : ℕ)
    (K : ℕ → Fin 8 → Matrix b b ℂ) :
    HistoryEncoding.historyUnitary T J (fun t j => (K t j).submatrix e e) =
      (HistoryEncoding.historyUnitary T J K).submatrix
        ((Equiv.refl Selector3).prodCongr ((Equiv.refl (Fin J)).prodCongr e))
        ((Equiv.refl Selector3).prodCongr ((Equiv.refl (Fin J)).prodCongr e)) := by
  ext ⟨s,r,i⟩ ⟨t,u,j⟩
  change HistoryEncoding.rawHistoryUnitary T J _ (r,(s,i)) (u,(t,j)) =
    HistoryEncoding.rawHistoryUnitary T J K (r,(s,e i)) (u,(t,e j))
  rw [HistoryEncoding.rawHistoryUnitary_apply,HistoryEncoding.rawHistoryUnitary_apply]
  rw [clockSelected_data_reindex]
  rfl

lemma historyA_data_reindex {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (e : a ≃ b) (T J : ℕ)
    (K : ℕ → Fin 8 → Matrix b b ℂ) (P : Matrix (Fin 2) (Fin 2) ℂ) :
    lcuMatrix P ![1,-(HistoryEncoding.historyUnitary T J (fun t j => (K t j).submatrix e e))] =
      (lcuMatrix P ![1,-(HistoryEncoding.historyUnitary T J K)]).submatrix
        ((Equiv.refl (Fin 2)).prodCongr
          ((Equiv.refl Selector3).prodCongr ((Equiv.refl (Fin J)).prodCongr e)))
        ((Equiv.refl (Fin 2)).prodCongr
          ((Equiv.refl Selector3).prodCongr ((Equiv.refl (Fin J)).prodCongr e))) := by
  rw [historyUnitary_data_reindex]
  have h := lcuMatrix_reindex (Equiv.refl (Fin 2))
    ((Equiv.refl Selector3).prodCongr ((Equiv.refl (Fin J)).prodCongr e)) P
    (![1,-(HistoryEncoding.historyUnitary T J K)])
  let ed := (Equiv.refl Selector3).prodCongr ((Equiv.refl (Fin J)).prodCongr e)
  have hb : (fun j : Fin 2 => ((![1,-(HistoryEncoding.historyUnitary T J K)]) j).submatrix ed ed) =
      ![1,-((HistoryEncoding.historyUnitary T J K).submatrix ed ed)] := by
    funext j
    fin_cases j
    · exact Matrix.submatrix_one_equiv ed
    · rfl
  change lcuMatrix P (fun j : Fin 2 =>
    ((![1,-(HistoryEncoding.historyUnitary T J K)]) j).submatrix ed ed) = _ at h
  rw [hb] at h
  exact h

abbrev DataQubits {G : EffectiveGateSet} (S : EffectiveSourceComputation G) : ℕ :=
  sourceQubits S + sourceQubits S

lemma dataQubits_pos {G : EffectiveGateSet} (S : EffectiveSourceComputation G) :
    0 < DataQubits S := by
  have h := sourceQubits_pos S
  unfold DataQubits
  omega

/-- This is an actual list of effective constant-local gates. The source list
is queried only at individual expanded time/selector indices. -/
def circuit {G : EffectiveGateSet} (conv : GateConvention G) (S : EffectiveSourceComputation G)
    (ell : ℕ) (prepare : EffectiveCircuit G 1) :
    EffectiveCircuit G (1+(3+(ell+DataQubits S))) :=
  nativeHistoryACircuit conv (dataQubits_pos S) (SourceCoordinates.expanded S).length ell
    (canonicalNativeTerm conv S) prepare

def layout {G : EffectiveGateSet} (S : EffectiveSourceComputation G) (ell : ℕ) :
    Basis (1+(3+(ell+DataQubits S))) ≃
      (Fin 2 × (Selector3 × (Fin (Fintype.card (Basis ell)) ×
        (Fin ((Fintype.card (StatePreparation.WorkSpace (SourceCoordinates.restQubits S)))^2) ×
          SourceSimulation.CatalystData S.catalystQubits)))) :=
  (historyALayout (SelectedFilter.clockIndex ell)).trans
    ((Equiv.refl _).prodCongr ((Equiv.refl _).prodCongr
      ((Equiv.refl _).prodCongr (nativeDataIndex S))))

/-- The complete actual source history/A compiler agrees with the canonical
matrices used by the source/filter correctness proof, for any chosen PREPARE. -/
theorem circuit_matrix {G : EffectiveGateSet} (conv : GateConvention G)
    (S : EffectiveSourceComputation G) (ell : ℕ) (prepare : EffectiveCircuit G 1)
    (P : Matrix (Fin 2) (Fin 2) ℂ) (hp : prepare.matrix = P.submatrix oneBit oneBit) :
    (circuit conv S ell prepare).matrix =
      (lcuMatrix P ![1,-(HistoryEncoding.historyUnitary (SourceCoordinates.expanded S).length
        (Fintype.card (Basis ell)) (SourceCoordinates.canonicalK S))]).submatrix
        (layout S ell) (layout S ell) := by
  rw [circuit,nativeHistoryACircuit_matrix conv _ _ _ _ prepare P hp]
  simp only [canonicalNativeTerm_matrix]
  rw [historyA_data_reindex]
  rfl

lemma circuit_length {G : EffectiveGateSet} (conv : GateConvention G)
    (S : EffectiveSourceComputation G) (ell : ℕ) (prepare : EffectiveCircuit G 1) :
    (circuit conv S ell prepare).length ≤
      (conv.bound+1)*prepare.length + 2*conv.bound^2 *
        (2^ell*conv.bound^(ell+1)*((conv.bound+1)*(3*conv.bound)+
          8*conv.bound^4*(sourceTermBound conv+4*(conv.X.length+conv.bound))) +
          (2^ell)^(conv.bound+1)*conv.X.length + 4*(conv.X.length+conv.bound)) := by
  apply nativeHistoryACircuit_length
  · omega
  · intro t ht j
    exact (canonicalNativeTerm_length conv S t j).trans (Nat.le_add_right _ _)

lemma lcuMatrix_prepare_error {s n : Type*} [Fintype s] [Fintype n]
    [DecidableEq s] [DecidableEq n] (P P' : Matrix s s ℂ) (K : s → Matrix n n ℂ)
    (hP : P ∈ Matrix.unitaryGroup s ℂ) (hP' : P' ∈ Matrix.unitaryGroup s ℂ)
    (hK : ∀ j, K j ∈ Matrix.unitaryGroup n ℂ) (τ : ℝ) (hPP : ‖P-P'‖ ≤ τ) :
    ‖lcuMatrix P K - lcuMatrix P' K‖ ≤ 2*τ := by
  apply MatrixCompilationNorm.unitary_sandwich_error_le
    (Matrix.kronecker P (1 : Matrix n n ℂ)) (Matrix.kronecker P' (1 : Matrix n n ℂ))
    (selectMatrix K)
    (Matrix.kronecker_mem_unitary hP (Matrix.unitaryGroup n ℂ).one_mem)
    (Matrix.kronecker_mem_unitary hP' (Matrix.unitaryGroup n ℂ).one_mem)
    (selectMatrix_unitary K hK) τ
  exact (MatrixCompilationNorm.tensor_identity_error P P').trans hPP

lemma prepare_unitary {G : EffectiveGateSet} (prepare : EffectiveCircuit G 1)
    (P : Matrix (Fin 2) (Fin 2) ℂ) (hp : prepare.matrix = P.submatrix oneBit oneBit) :
    P ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have h := prepare.unitary.1
  rw [hp,Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv] at h
  have h' := congrArg (fun M : Operator 1 => M.submatrix oneBit.symm oneBit.symm) h
  simpa only [Matrix.submatrix_submatrix,Equiv.apply_symm_apply,Function.comp_def,
    Matrix.submatrix_one_equiv,Matrix.submatrix_id_id] using h'

lemma difference_unitary {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ) (j : Fin 2) :
    (![1,-U] : Fin 2 → Matrix n n ℂ) j ∈ Matrix.unitaryGroup n ℂ := by
  fin_cases j
  · exact (Matrix.unitaryGroup n ℂ).one_mem
  · simpa only [Matrix.cons_val_one,Matrix.head_cons,neg_one_smul] using
      phase_unitary (-1) U (by norm_num) hU

/-- Approximation of the single one-qubit weighted selector costs at most twice
its error for the complete source history encoding, independently of dimension. -/
theorem circuit_error {G : EffectiveGateSet} (conv : GateConvention G)
    (S : EffectiveSourceComputation G) (ell : ℕ) (prepare : EffectiveCircuit G 1)
    (τ : ℝ)
    (hprepare : ‖prepare.matrix - prepareThird.submatrix oneBit oneBit‖ ≤ τ) :
    ‖(circuit conv S ell prepare).matrix -
      (HistoryEncoding.historyAEncoding (SourceCoordinates.expanded S).length
        (Fintype.card (Basis ell)) (SourceCoordinates.canonicalK S)).submatrix
        (layout S ell) (layout S ell)‖ ≤ 2*τ := by
  let P : Matrix (Fin 2) (Fin 2) ℂ := prepare.matrix.submatrix oneBit.symm oneBit.symm
  have hp : prepare.matrix = P.submatrix oneBit oneBit := by
    ext x y
    simp [P,Matrix.submatrix_apply]
  rw [circuit_matrix conv S ell prepare P hp,HistoryEncoding.historyAEncoding,
    MatrixCompilationNorm.submatrix_equiv_error]
  apply lcuMatrix_prepare_error P prepareThird _ (prepare_unitary prepare P hp) prepareThird_unitary
  · exact difference_unitary _ (HistoryEncoding.historyUnitary_unitary (SourceCoordinates.canonicalK S)
      (fun t ht a => SourceCoordinates.canonicalK_unitary S t a))
  · rw [←MatrixCompilationNorm.submatrix_equiv_error oneBit P prepareThird,←hp]
    exact hprepare

abbrev CanonicalData {G : EffectiveGateSet} (S : EffectiveSourceComputation G) :=
  Fin ((Fintype.card (StatePreparation.WorkSpace (SourceCoordinates.restQubits S)))^2) ×
    SourceSimulation.CatalystData S.catalystQubits

/-- The same physical positions interpreted at the enumerated block-encoding
interface used by the already proved compression-walk theorem. -/
def enumeratedLayout {G : EffectiveGateSet} (S : EffectiveSourceComputation G) (ell : ℕ) :
    Basis (1+(3+(ell+DataQubits S))) ≃
      (HistoryEncoding.BlockAncilla × Fin (Fintype.card (Fin (Fintype.card (Basis ell)) × CanonicalData S))) :=
  (layout S ell).trans (HistoryEncoding.encodingIndex (Fintype.card (Basis ell))).symm

lemma enumerated_encoding_layout {G : EffectiveGateSet} (S : EffectiveSourceComputation G) (ell : ℕ) :
    (HistoryEncoding.enumeratedAEncoding (SourceCoordinates.expanded S).length
      (Fintype.card (Basis ell)) (SourceCoordinates.canonicalK S)).submatrix
        (enumeratedLayout S ell) (enumeratedLayout S ell) =
    (HistoryEncoding.historyAEncoding (SourceCoordinates.expanded S).length
      (Fintype.card (Basis ell)) (SourceCoordinates.canonicalK S)).submatrix
        (layout S ell) (layout S ell) := by
  ext x y
  simp [HistoryEncoding.enumeratedAEncoding,enumeratedLayout,Matrix.submatrix_apply]

theorem circuit_error_enumerated {G : EffectiveGateSet} (conv : GateConvention G)
    (S : EffectiveSourceComputation G) (ell : ℕ) (prepare : EffectiveCircuit G 1)
    (τ : ℝ)
    (hprepare : ‖prepare.matrix - prepareThird.submatrix oneBit oneBit‖ ≤ τ) :
    ‖(circuit conv S ell prepare).matrix -
      (HistoryEncoding.enumeratedAEncoding (SourceCoordinates.expanded S).length
        (Fintype.card (Basis ell)) (SourceCoordinates.canonicalK S)).submatrix
        (enumeratedLayout S ell) (enumeratedLayout S ell)‖ ≤ 2*τ := by
  rw [enumerated_encoding_layout]
  exact circuit_error conv S ell prepare τ hprepare

end Paper25.SourceHistoryCompilation
