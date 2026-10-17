import CounterFreeHDA.CornerInterfaces

namespace CounterFreeHDA.Cubical
universe u
variable {Lab : Type u} {k : ℕ} (P : PomsetData Lab) (hP : IsIntervalPom P)
    (hs : P.srcLen ≤ k) (ht : P.tgtLen ≤ k) {U V : Cube Lab k}

theorem iota_face_source (α : Face U (sourceCube P hs)) (i : Fin P.srcLen) :
    ((iota P hP hs).face α).status (P.src i) = α.status i :=
  TrackCell.face_status_occ α (iota P hP hs) i

theorem tau_face_target (β : Face V (targetCube P ht)) (i : Fin P.tgtLen) :
    ((tau P hP ht).face β).status (P.tgt i) = β.status i :=
  TrackCell.face_status_occ β (tau P hP ht) i

theorem iota_face_not_source (α : Face U (sourceCube P hs)) (e : Fin P.n) (he : ¬ P.inSrc e) :
    ((iota P hP hs).face α).status e = Status.zero := by
  classical
  have hz : (iota P hP hs).status e = Status.zero := if_neg he
  exact (TrackCell.face_status_inactive α _ (by rw [hz]; decide)).trans hz

theorem tau_face_not_target (β : Face V (targetCube P ht)) (e : Fin P.n) (he : ¬ P.inTgt e) :
    ((tau P hP ht).face β).status e = Status.one := by
  classical
  have hz : (tau P hP ht).status e = Status.one := if_neg he
  exact (TrackCell.face_status_inactive β _ (by rw [hz]; decide)).trans hz

end CounterFreeHDA.Cubical
