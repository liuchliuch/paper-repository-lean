import CounterFreeHDA.BoundaryAssignments
import CounterFreeHDA.TypedCornerEvents
import CounterFreeHDA.CornerDeletion

namespace CounterFreeHDA.EndoPom
universe u
open Cubical
variable {Lab : Type u} {k : ℕ} {U A B : Cube Lab k}

private theorem status_deleted_of_one (P : EndoPom (cubeInterface U)) (α : Cubical.Face A U) (β : Cubical.Face B U)
    (i : Fin U.dim) (hi : P.boundaryStatus α β i = Status.one) : i ∈ P.boundaryDeleted α β := by
  classical
  by_contra hn
  have hs := (P.boundaryStatus_star α β i).mpr hn
  exact (by decide : Status.one ≠ Status.star) (hi.symm.trans hs)

private theorem status_deleted_of_zero (P : EndoPom (cubeInterface U)) (α : Cubical.Face A U) (β : Cubical.Face B U)
    (i : Fin U.dim) (hi : P.boundaryStatus α β i = Status.zero) : i ∈ P.boundaryDeleted α β := by
  classical
  by_contra hn
  have hs := (P.boundaryStatus_star α β i).mpr hn
  exact (by decide : Status.zero ≠ Status.star) (hi.symm.trans hs)

private theorem deleted_status_cases (P : EndoPom (cubeInterface U)) (α : Cubical.Face A U) (β : Cubical.Face B U)
    (i : Fin U.dim) (hi : i ∈ P.boundaryDeleted α β) :
    P.boundaryStatus α β i = Status.one ∨ P.boundaryStatus α β i = Status.zero := by
  unfold boundaryStatus
  rw [if_pos hi]
  by_cases hα : α.status i = Status.one
  · exact Or.inl (if_pos hα)
  · exact Or.inr (if_neg hα)

/-- The middle corner deletes exactly R, because every position of R is
persistent through all powers and no other position receives a fixed status. -/
theorem middle_deleted_iff (P : EndoPom (cubeInterface U)) (α : Cubical.Face A U) (β : Cubical.Face B U)
    (hw : P.pom.val.WidthLE k) (n : ℕ) (e : Fin (P.pow n).pom.n) :
    Corners.Deleted (P.pow n).pom.val
      ((P.boundedPower hw n).toArrow.sourceFace (P.boundaryFace α β)).status
      ((P.boundedPower hw n).toArrow.targetFace (P.boundaryFace α β)).status e ↔
    ∃ i ∈ P.boundaryDeleted α β, (P.pow n).pom.src (Fin.cast (P.pow n).src_len.symm i) = e := by
  refine (Arrow.corner_deleted_iff (P.boundedPower hw n).toArrow (P.boundaryFace α β) (P.boundaryFace α β) e).trans ?_
  constructor
  · rintro (⟨i,hi,hσ⟩ | ⟨i,hi,hσ⟩)
    · have hs : P.boundaryStatus α β i = Status.one := by simpa only [boundaryFace,Cubical.Face.ofStatuses_status] using hσ
      exact ⟨i,status_deleted_of_one P α β i hs,hi⟩
    · have hs : P.boundaryStatus α β i = Status.zero := by simpa only [boundaryFace,Cubical.Face.ofStatuses_status] using hσ
      have hr := status_deleted_of_zero P α β i hs
      exact ⟨i,hr,(P.persistent_pow n i (P.boundaryDeleted_persistent α β i hr)).trans hi⟩
  · rintro ⟨i,hi,he⟩
    rcases deleted_status_cases P α β i hi with hσ | hσ
    · exact Or.inl ⟨i,he,(Cubical.Face.ofStatuses_status U (P.boundaryStatus α β) i).trans hσ⟩
    · exact Or.inr ⟨i,(P.persistent_pow n i (P.boundaryDeleted_persistent α β i hi)).symm.trans he,
        (Cubical.Face.ofStatuses_status U (P.boundaryStatus α β) i).trans hσ⟩

noncomputable def middleCornerDeletionIso (P : EndoPom (cubeInterface U)) (α : Cubical.Face A U) (β : Cubical.Face B U)
    (hw : P.pom.val.WidthLE k) (n : ℕ) :
    PomsetIso ((P.boundedPower hw n).toArrow.corner (P.width_pow hw n) (P.boundaryFace α β) (P.boundaryFace α β)
      (P.boundary_middle_compatible α β hw n)).pom.val
      ((P.pow n).deleteData (P.boundaryDeleted α β)) := by
  classical
  let R := P.boundaryDeleted α β
  let γ := P.boundaryFace α β
  let C := (P.boundedPower hw n).toArrow
  have hR : (P.pow n).PersistentSet R := fun i hi => P.persistent_pow n i (P.boundaryDeleted_persistent α β i hi)
  apply Corners.asDeletionIso (P.pow n).pom.property (C.sourceFace γ).status (C.targetFace γ).status
    (C.compatible_raw γ γ (P.boundary_middle_compatible α β hw n)) ((P.pow n).keep R)
  · intro e
    exact (P.middle_deleted_iff α β hw n e).not
  · intro i hi
    let j := Fin.cast (P.pow n).src_len i
    have hj : j ∉ R := ((P.pow n).keep_source_iff R j).mp
      (by simpa only [j,Fin.cast_cast,Fin.cast_refl,id_eq] using hi)
    exact (Cubical.Face.ofStatuses_status U (P.boundaryStatus α β) j).trans ((P.boundaryStatus_star α β j).mpr hj)
  · intro i hi
    let j := Fin.cast (P.pow n).tgt_len i
    have hj : j ∉ R := ((P.pow n).keep_target_iff R hR j).mp
      (by simpa only [j,Fin.cast_cast,Fin.cast_refl,id_eq] using hi)
    exact (Cubical.Face.ofStatuses_status U (P.boundaryStatus α β) j).trans ((P.boundaryStatus_star α β j).mpr hj)

/-- The exact middle-corner replacement by a power of the actual P-R. -/
noncomputable def middlePowerIso (P : EndoPom (cubeInterface U)) (α : Cubical.Face A U) (β : Cubical.Face B U)
    (hw : P.pom.val.WidthLE k) (n : ℕ) :
    PomsetIso ((P.reduced (P.boundaryDeleted α β) (P.boundaryDeleted_persistent α β) hw).pow n).pom.val
      (((P.boundedPower hw n).toArrow.corner (P.width_pow hw n) (P.boundaryFace α β) (P.boundaryFace α β)
        (P.boundary_middle_compatible α β hw n)).pom.val) :=
  (P.deletionPowerIso (P.boundaryDeleted α β) (P.boundaryDeleted_persistent α β) hw n).trans
    (P.middleCornerDeletionIso α β hw n).symm

end CounterFreeHDA.EndoPom
