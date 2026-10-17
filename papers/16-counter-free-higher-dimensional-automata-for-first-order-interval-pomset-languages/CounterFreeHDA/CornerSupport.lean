import CounterFreeHDA.RunRestriction

namespace CounterFreeHDA.Cubical
universe u
variable {Lab : Type u} {k : ℕ} (P : PomsetData Lab) (hP : IsIntervalPom P)
    (hs : P.srcLen ≤ k) (ht : P.tgtLen ≤ k) {U V : Cube Lab k}
    (α : Face U (sourceCube P hs)) (β : Face V (targetCube P ht))

theorem iota_face_one_iff (e : Fin P.n) :
    ((iota P hP hs).face α).status e = Status.one ↔ Corners.SourceDeleted P α.status e := by
  classical
  constructor
  · intro he
    by_cases hs' : P.inSrc e
    · obtain ⟨i,rfl⟩ := hs'
      exact ⟨i,rfl,(iota_face_source P hP hs α i).symm.trans he⟩
    · have hz := iota_face_not_source P hP hs α e hs'
      exact False.elim ((by decide : Status.zero ≠ Status.one) (hz.symm.trans he))
  · rintro ⟨i,hi,hα⟩
    exact (congrArg (((iota P hP hs).face α).status) hi.symm).trans
      ((iota_face_source P hP hs α i).trans hα)

theorem tau_face_zero_iff (e : Fin P.n) :
    ((tau P hP ht).face β).status e = Status.zero ↔ Corners.TargetDeleted P β.status e := by
  classical
  constructor
  · intro he
    by_cases ht' : P.inTgt e
    · obtain ⟨i,rfl⟩ := ht'
      exact ⟨i,rfl,(tau_face_target P hP ht β i).symm.trans he⟩
    · have hz := tau_face_not_target P hP ht β e ht'
      exact False.elim ((by decide : Status.one ≠ Status.zero) (hz.symm.trans he))
  · rintro ⟨i,hi,hβ⟩
    exact (congrArg (((tau P hP ht).face β).status) hi.symm).trans
      ((tau_face_target P hP ht β i).trans hβ)

theorem corner_support (hc : Corners.Compatible P α.status β.status) (e : Fin P.n) :
    (∃ a, Corners.inclusion P α.status β.status hc a = e) ↔
      ((iota P hP hs).face α).status e ≠ Status.one ∧ ((tau P hP ht).face β).status e ≠ Status.zero := by
  classical
  have hkeep : (∃ a, Corners.inclusion P α.status β.status hc a = e) ↔ ¬ Corners.Deleted P α.status β.status e := by
    constructor
    · rintro ⟨a,rfl⟩; exact Corners.inclusion_kept P α.status β.status hc a
    · intro he; exact ⟨Corners.retain P α.status β.status hc e he,Corners.inclusion_retain P α.status β.status hc e he⟩
  exact hkeep.trans (not_or.trans (and_congr
    (iota_face_one_iff P hP hs α e).not.symm (tau_face_zero_iff P hP ht β e).not.symm))

end CounterFreeHDA.Cubical
