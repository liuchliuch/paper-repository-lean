import CounterFreeHDA.TargetDeletion
import CounterFreeHDA.PrefixDeletion

namespace CounterFreeHDA.Appendix.Residual
open Cubical Compare
variable {U V : UCube}

theorem deletionFace_status (U : UCube) (D : Finset (Fin U.dim)) (i : Fin U.dim) :
    (deletionFace U D).status i = deletionStatus U D i := Cubical.Face.ofStatuses_status _ _ _

theorem deletionStatus_ne_one (U : UCube) (D : Finset (Fin U.dim)) (i : Fin U.dim) :
    deletionStatus U D i ≠ Status.one := by
  unfold deletionStatus
  split_ifs <;> decide

theorem deletionStatus_star (U : UCube) (D : Finset (Fin U.dim)) (i : Fin U.dim) :
    deletionStatus U D i = Status.star ↔ i ∉ D := by
  unfold deletionStatus
  by_cases h : i ∈ D <;> simp [h,Status.zero,Status.star]

theorem deletion_compatible (B : Arrow U V) (D : Finset (Fin V.dim)) :
    B.Compatible (deletionFace U (B.pullTargetDeletion D)) (deletionFace V D) := by
  intro i j hij
  rw [deletionFace_status,deletionFace_status]
  by_cases hj : j ∈ D
  · have hi := (B.mem_pullTargetDeletion D i).mpr ⟨j,hj,hij⟩
    simp only [deletionStatus,if_pos hj,if_pos hi]
    exact le_refl _
  · have hs := Status.le_star_of_ne_one (deletionStatus U (B.pullTargetDeletion D) i)
      (deletionStatus_ne_one _ _ i)
    simpa only [deletionStatus,if_neg hj] using hs

noncomputable def deletedArrow (B : BoundedArrow U V) (D : Finset (Fin V.dim)) :
    BoundedArrow (Cubical.Face.activeCube U (deletionStatus U (B.toArrow.pullTargetDeletion D)))
      (Cubical.Face.activeCube V (deletionStatus V D)) :=
  B.toArrow.corner B.width (deletionFace U (B.toArrow.pullTargetDeletion D)) (deletionFace V D)
    (deletion_compatible B.toArrow D)

theorem deletedArrow_deleted (B : Arrow U V) (D : Finset (Fin V.dim)) (e : Fin B.pom.n) :
    Corners.Deleted B.pom.val
      (B.sourceFace (deletionFace U (B.pullTargetDeletion D))).status
      (B.targetFace (deletionFace V D)).status e ↔ ∃ i ∈ D, B.targetEvent i = e := by
  refine (B.corner_deleted_iff _ _ e).trans ?_
  constructor
  · rintro (⟨i,_,hi⟩ | ⟨i,he,hi⟩)
    · exact False.elim (deletionStatus_ne_one _ _ i ((deletionFace_status _ _ i).symm.trans hi))
    · exact ⟨i,(deletionStatus_zero _ _ i).mp ((deletionFace_status _ _ i).symm.trans hi),he⟩
  · rintro ⟨i,hi,he⟩
    exact Or.inr ⟨i,he,(deletionFace_status _ _ i).trans ((deletionStatus_zero _ _ i).mpr hi)⟩

noncomputable def deletedArrowIso (B : BoundedArrow U V) (D : Finset (Fin V.dim)) :
    PomsetIso (deletedArrow B D).pom.val (Deletion.data B.pom.val (B.toArrow.keepTargetEvents D)) := by
  apply Corners.asDeletionIso B.pom.property
    (B.toArrow.sourceFace (deletionFace U (B.toArrow.pullTargetDeletion D))).status
    (B.toArrow.targetFace (deletionFace V D)).status
    (B.toArrow.compatible_raw _ _ (deletion_compatible B.toArrow D)) (B.toArrow.keepTargetEvents D)
  · intro e
    exact (deletedArrow_deleted B.toArrow D e).not
  · intro i hi
    let j := Fin.cast B.toArrow.src_len i
    have hj : j ∉ B.toArrow.pullTargetDeletion D := (B.toArrow.keepTarget_source D j).mp
      (by simpa only [j,Arrow.sourceEvent,Fin.cast_cast,Fin.cast_refl,id_eq] using hi)
    exact (deletionFace_status _ _ j).trans ((deletionStatus_star _ _ j).mpr hj)
  · intro i hi
    let j := Fin.cast B.toArrow.tgt_len i
    have hj : j ∉ D := (B.toArrow.keepTarget_target D j).mp
      (by simpa only [j,Arrow.targetEvent,Fin.cast_cast,Fin.cast_refl,id_eq] using hi)
    exact (deletionFace_status _ _ j).trans ((deletionStatus_star _ _ j).mpr hj)

/-- The actual target-deletion update, with exact induced event gluing and
both ordered interfaces, including deletion of the newly started event. -/
noncomputable def deletedPrefix_compIso (P : Prefix U) (B : BoundedArrow U V)
    (D : Finset (Fin V.dim)) :
    PomsetIso ((deletedPrefix P (B.toArrow.pullTargetDeletion D)).comp (deletedArrow B D)).pom.val
      (deletedPrefix (P.comp B) D).pom.val := by
  let plan := P.toArrow.targetDeletionPlan B.toArrow D
  have hA := deletedPrefixIso P (B.toArrow.pullTargetDeletion D)
  have hB := deletedArrowIso B D
  have hG := deletedPrefixIso (P.comp B) D
  exact (PomsetIso.glueIso hA hB _ plan.glueMatch).trans
    ((plan.iso P.pom.property B.pom.property).trans hG.symm)

end CounterFreeHDA.Appendix.Residual
