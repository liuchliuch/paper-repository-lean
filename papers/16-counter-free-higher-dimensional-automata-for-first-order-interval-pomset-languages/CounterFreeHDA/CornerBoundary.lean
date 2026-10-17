import CounterFreeHDA.BoundaryStatus

namespace CounterFreeHDA.Cubical.CornerFaces
universe u
variable {Lab : Type u} {k : ℕ} (P : PomsetData Lab) (hP : IsIntervalPom P)
    (hs : P.srcLen ≤ k) (ht : P.tgtLen ≤ k) {U V : Cube Lab k}
    (α : Face U (sourceCube P hs)) (β : Face V (targetCube P ht))
    (hc : Corners.Compatible P α.status β.status)

/-- The extension sends the corner's source cell to the prescribed actual
source face, including source/target events shared across the boundary. -/
theorem extension_source :
    CornerExtension.cell P hP α.status β.status hc (arrow P hP hs ht α β hc).sourceCell =
      (iota P hP hs).face α := by
  classical
  let A := arrow P hP hs ht α β hc
  apply TrackCell.status_injective
  funext e
  change (CornerExtension.cell P hP α.status β.status hc A.sourceCell).status e = ((iota P hP hs).face α).status e
  by_cases he : P.inSrc e
  · obtain ⟨i,rfl⟩ := he
    rw [iota_face_source]
    by_cases heS : Corners.SourceDeleted P α.status (P.src i)
    · obtain ⟨j,hj,hα⟩ := heS
      have hji := P.src_inj hj
      subst j
      exact (CornerExtension.status_source P α.status β.status hc A.sourceCell _ ⟨i,rfl,hα⟩).trans hα.symm
    by_cases heT : Corners.TargetDeleted P β.status (P.src i)
    · obtain ⟨j,hj,hβ⟩ := heT
      have hle := hc i j hj.symm
      have hα : α.status i = Status.zero := by
        apply Fin.ext
        rw [hβ] at hle
        change (α.status i).val ≤ 0 at hle
        change (α.status i).val = 0
        omega
      exact (CornerExtension.status_target P α.status β.status hc A.sourceCell _ ⟨j,hj,hβ⟩).trans hα.symm
    have hek : ¬ Corners.Deleted P α.status β.status (P.src i) := fun h => h.elim heS heT
    have hinc := Corners.inclusion_retain P α.status β.status hc (P.src i) hek
    apply (CornerExtension.status_kept P α.status β.status hc A.sourceCell _ hek).trans
    by_cases hα : α.status i = Status.star
    · have hm : A.pom.val.inSrc (Corners.retain P α.status β.status hc (P.src i) hek) :=
        (Corners.source_iff P α.status β.status hc _).mpr ⟨i,hinc.symm,hα⟩
      exact (if_pos hm).trans hα.symm
    · have hm : ¬ A.pom.val.inSrc (Corners.retain P α.status β.status hc (P.src i) hek) := by
        intro h
        obtain ⟨j,hj,hjα⟩ := (Corners.source_iff P α.status β.status hc _).mp h
        have hji := P.src_inj (hj.trans hinc)
        subst j
        exact hα hjα
      have hn1 : α.status i ≠ Status.one := fun h => heS ⟨i,rfl,h⟩
      have hv := (α.status i).isLt
      have hα0 : α.status i = Status.zero := by
        apply Fin.ext
        have hn1v : (α.status i).val ≠ 1 := fun h => hα (Fin.ext h)
        have hn2v : (α.status i).val ≠ 2 := fun h => hn1 (Fin.ext h)
        change (α.status i).val = 0
        omega
      exact (if_neg hm).trans hα0.symm
  · have heS : ¬ Corners.SourceDeleted P α.status e := by
      rintro ⟨i,hi,_⟩; exact he ⟨i,hi⟩
    by_cases heT : Corners.TargetDeleted P β.status e
    · exact (CornerExtension.status_target P α.status β.status hc A.sourceCell e heT).trans
        (iota_face_not_source P hP hs α e he).symm
    have hek : ¬ Corners.Deleted P α.status β.status e := fun h => h.elim heS heT
    have hinc := Corners.inclusion_retain P α.status β.status hc e hek
    have hm : ¬ A.pom.val.inSrc (Corners.retain P α.status β.status hc e hek) := by
      intro h
      obtain ⟨i,hi,_⟩ := (Corners.source_iff P α.status β.status hc _).mp h
      exact he ⟨i,hi.trans hinc⟩
    exact (CornerExtension.status_kept P α.status β.status hc A.sourceCell e hek).trans
      ((if_neg hm).trans (iota_face_not_source P hP hs α e he).symm)

/-- The extension sends the corner's target cell to the prescribed target
face of the original characteristic HDA. -/
theorem extension_target :
    CornerExtension.cell P hP α.status β.status hc (arrow P hP hs ht α β hc).targetCell =
      (tau P hP ht).face β := by
  classical
  let A := arrow P hP hs ht α β hc
  apply TrackCell.status_injective
  funext e
  change (CornerExtension.cell P hP α.status β.status hc A.targetCell).status e = ((tau P hP ht).face β).status e
  by_cases he : P.inTgt e
  · obtain ⟨i,rfl⟩ := he
    rw [tau_face_target]
    by_cases heT : Corners.TargetDeleted P β.status (P.tgt i)
    · obtain ⟨j,hj,hβ⟩ := heT
      have hji := P.tgt_inj hj
      subst j
      exact (CornerExtension.status_target P α.status β.status hc A.targetCell _ ⟨i,rfl,hβ⟩).trans hβ.symm
    by_cases heS : Corners.SourceDeleted P α.status (P.tgt i)
    · obtain ⟨j,hj,hα⟩ := heS
      have hle := hc j i hj
      have hβ : β.status i = Status.one := by
        apply Fin.ext
        rw [hα] at hle
        change 2 ≤ (β.status i).val at hle
        have hv := (β.status i).isLt
        change (β.status i).val = 2
        omega
      exact (CornerExtension.status_source P α.status β.status hc A.targetCell _ ⟨j,hj,hα⟩).trans hβ.symm
    have hek : ¬ Corners.Deleted P α.status β.status (P.tgt i) := fun h => h.elim heS heT
    have hinc := Corners.inclusion_retain P α.status β.status hc (P.tgt i) hek
    apply (CornerExtension.status_kept P α.status β.status hc A.targetCell _ hek).trans
    by_cases hβ : β.status i = Status.star
    · have hm : A.pom.val.inTgt (Corners.retain P α.status β.status hc (P.tgt i) hek) :=
        (Corners.target_iff P α.status β.status hc _).mpr ⟨i,hinc.symm,hβ⟩
      exact (if_pos hm).trans hβ.symm
    · have hm : ¬ A.pom.val.inTgt (Corners.retain P α.status β.status hc (P.tgt i) hek) := by
        intro h
        obtain ⟨j,hj,hjβ⟩ := (Corners.target_iff P α.status β.status hc _).mp h
        have hji := P.tgt_inj (hj.trans hinc)
        subst j
        exact hβ hjβ
      have hn0 : β.status i ≠ Status.zero := fun h => heT ⟨i,rfl,h⟩
      have hv := (β.status i).isLt
      have hβ1 : β.status i = Status.one := by
        apply Fin.ext
        have hn1v : (β.status i).val ≠ 1 := fun h => hβ (Fin.ext h)
        have hn0v : (β.status i).val ≠ 0 := fun h => hn0 (Fin.ext h)
        change (β.status i).val = 2
        omega
      exact (if_neg hm).trans hβ1.symm
  · have heT : ¬ Corners.TargetDeleted P β.status e := by
      rintro ⟨i,hi,_⟩; exact he ⟨i,hi⟩
    by_cases heS : Corners.SourceDeleted P α.status e
    · exact (CornerExtension.status_source P α.status β.status hc A.targetCell e heS).trans
        (tau_face_not_target P hP ht β e he).symm
    have hek : ¬ Corners.Deleted P α.status β.status e := fun h => h.elim heS heT
    have hinc := Corners.inclusion_retain P α.status β.status hc e hek
    have hm : ¬ A.pom.val.inTgt (Corners.retain P α.status β.status hc e hek) := by
      intro h
      obtain ⟨i,hi,_⟩ := (Corners.target_iff P α.status β.status hc _).mp h
      exact he ⟨i,hi.trans hinc⟩
    exact (CornerExtension.status_kept P α.status β.status hc A.targetCell e hek).trans
      ((if_neg hm).trans (tau_face_not_target P hP ht β e he).symm)

end CounterFreeHDA.Cubical.CornerFaces
