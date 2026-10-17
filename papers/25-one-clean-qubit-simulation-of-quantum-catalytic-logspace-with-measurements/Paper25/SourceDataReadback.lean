import Paper25.SourcePreparationPlacement
import Paper25.SourceHistoryCompilation

/-! Readback of the two actual source registers in the final physical layout.
Only explicit wire positions and the output-first work permutation are used. -/
noncomputable section
namespace Paper25.SourceDataReadback
open OperationalModel OperationalModel.LocalCompilation SourcePreparationPlacement
open SourceCoordinates SourceTermCompilation StatePreparation
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 512
variable {G : EffectiveGateSet}

def dataTail (S : EffectiveSourceComputation G) (ell m : ℕ)
    (x : Basis (filterQubits S ell m)) : Basis (sourceQubits S+sourceQubits S) :=
  fun i => x ⟨m+6+ell+i.val,by
    have hi := i.isLt
    dsimp [filterQubits,walkQubits,encoderQubits] at *
    omega⟩

lemma nativeDataIndex_formula (S : EffectiveSourceComputation G)
    (x : Basis (sourceQubits S+sourceQubits S)) :
    nativeDataIndex S x =
      ((SourceBias.operatorIndex (WorkSpace (restQubits S))).symm
        (((canonicalIndex S ((tensorBits _ _ x).1)).1),((canonicalIndex S ((tensorBits _ _ x).2)).1)),
       (SourceBias.operatorIndex (Bits S.catalystQubits)).symm
        (((canonicalIndex S ((tensorBits _ _ x).1)).2),((canonicalIndex S ((tensorBits _ _ x).2)).2))) := rfl

lemma canonical_work_read (S : EffectiveSourceComputation G)
    (f : Basis (S.workQubits+S.catalystQubits)) (i : WPos S) :
    (splitBits (restQubits S)).symm (canonicalIndex S f).1 i =
      f (Fin.castAdd S.catalystQubits (workWire S i)) := by
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

lemma tail_left_work (S : EffectiveSourceComputation G) (ell m : ℕ)
    (x : Basis (filterQubits S ell m)) (i : WPos S) :
    (tensorBits (sourceQubits S) (sourceQubits S) (dataTail S ell m x)).1
      (Fin.castAdd S.catalystQubits (workWire S i)) =
      x (allPositions S ell m (.inl (.inr (.inr (.inl (.inl i)))))) := by
  apply congrArg x
  apply Fin.ext
  simp only [dataTail,tensorBits,Fin.castAdd,Fin.castLE,allPositions_leftWork_val]

lemma tail_right_work (S : EffectiveSourceComputation G) (ell m : ℕ)
    (x : Basis (filterQubits S ell m)) (i : WPos S) :
    (tensorBits (sourceQubits S) (sourceQubits S) (dataTail S ell m x)).2
      (Fin.castAdd S.catalystQubits (workWire S i)) =
      x (allPositions S ell m (.inl (.inr (.inr (.inl (.inr i)))))) := by
  apply congrArg x
  apply Fin.ext
  simp only [dataTail,tensorBits,Fin.castAdd,Fin.castLE,Fin.natAdd,allPositions_rightWork_val]
  omega

lemma tail_left_catalyst (S : EffectiveSourceComputation G) (ell m : ℕ)
    (x : Basis (filterQubits S ell m)) (i : Fin S.catalystQubits) :
    (tensorBits (sourceQubits S) (sourceQubits S) (dataTail S ell m x)).1
      (Fin.natAdd S.workQubits i) =
      x (allPositions S ell m (.inr (.inr (.inr (.inr (.inl i)))))) := by
  apply congrArg x
  apply Fin.ext
  simp only [dataTail,tensorBits,Fin.castAdd,Fin.castLE,Fin.natAdd,allPositions_leftCatalyst_val]
  omega

lemma tail_right_catalyst (S : EffectiveSourceComputation G) (ell m : ℕ)
    (x : Basis (filterQubits S ell m)) (i : Fin S.catalystQubits) :
    (tensorBits (sourceQubits S) (sourceQubits S) (dataTail S ell m x)).2
      (Fin.natAdd S.workQubits i) =
      x (allPositions S ell m (.inr (.inr (.inr (.inr (.inr i)))))) := by
  apply congrArg x
  apply Fin.ext
  simp only [dataTail,tensorBits,Fin.natAdd,allPositions_rightCatalyst_val]
  omega

lemma canonical_left_work (S : EffectiveSourceComputation G) (ell m : ℕ)
    (x : Basis (filterQubits S ell m)) :
    (canonicalIndex S (tensorBits (sourceQubits S) (sourceQubits S) (dataTail S ell m x)).1).1 =
      (logicalLayout S ell m x).1.2.2.1.1 := by
  apply (splitBits (restQubits S)).symm.injective
  funext i
  rw [canonical_work_read,tail_left_work]
  exact (logicalLayout_selected S ell m x (.inr (.inr (.inl (.inl i))))).symm

lemma canonical_right_work (S : EffectiveSourceComputation G) (ell m : ℕ)
    (x : Basis (filterQubits S ell m)) :
    (canonicalIndex S (tensorBits (sourceQubits S) (sourceQubits S) (dataTail S ell m x)).2).1 =
      (logicalLayout S ell m x).1.2.2.1.2 := by
  apply (splitBits (restQubits S)).symm.injective
  funext i
  rw [canonical_work_read,tail_right_work]
  exact (logicalLayout_selected S ell m x (.inr (.inr (.inl (.inr i))))).symm

/-- The final physical doubled-source tail reads exactly the work pair and
catalyst coordinates used in the source/filter mathematical correctness chain. -/
theorem dataTail_readback (S : EffectiveSourceComputation G) (ell m : ℕ)
    (x : Basis (filterQubits S ell m)) :
    nativeDataIndex S (dataTail S ell m x) =
      ((SourceBias.operatorIndex (WorkSpace (restQubits S))).symm
        (logicalLayout S ell m x).1.2.2.1,(filterLayout S ell m x).2) := by
  rw [nativeDataIndex_formula,canonical_left_work,canonical_right_work]
  apply Prod.ext
  · rfl
  · change (SourceBias.operatorIndex (Bits S.catalystQubits)).symm _ =
      (SourceBias.operatorIndex (Bits S.catalystQubits)).symm _
    apply congrArg (SourceBias.operatorIndex (Bits S.catalystQubits)).symm
    apply Prod.ext
    · funext i
      change (canonicalIndex S ((tensorBits (sourceQubits S) (sourceQubits S) (dataTail S ell m x)).1)).2 i =
        (logicalLayout S ell m x).2 (.inr (.inr (.inr (.inl i))))
      rw [canonicalIndex_catalyst_bit,tail_left_catalyst]
      exact (logicalLayout_unused S ell m x (.inr (.inr (.inr (.inl i))))).symm
    · funext i
      change (canonicalIndex S ((tensorBits (sourceQubits S) (sourceQubits S) (dataTail S ell m x)).2)).2 i =
        (logicalLayout S ell m x).2 (.inr (.inr (.inr (.inr i))))
      rw [canonicalIndex_catalyst_bit,tail_right_catalyst]
      exact (logicalLayout_unused S ell m x (.inr (.inr (.inr (.inr i))))).symm

end Paper25.SourceDataReadback
