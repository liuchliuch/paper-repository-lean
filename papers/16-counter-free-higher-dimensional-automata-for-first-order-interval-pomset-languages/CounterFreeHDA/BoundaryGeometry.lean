import CounterFreeHDA.TrackCube

namespace CounterFreeHDA.Cubical
universe u
variable {Lab : Type u} {k : ℕ} (P : PomsetData Lab) (hP : IsIntervalPom P)
    (hs : P.srcLen ≤ k) (ht : P.tgtLen ≤ k)

/-- An interior event separates the two entire actual boundary cubes. -/
theorem boundary_cubes_disjoint (e : Fin P.n) (heS : ¬ P.inSrc e) (heT : ¬ P.inTgt e)
    {U : Cube Lab k} (c : TrackCell P U)
    (hl : TrackCell.InCube (iota P hP hs) c) (hr : TrackCell.InCube (tau P hP ht) c) : False := by
  classical
  have h0 : (iota P hP hs).status e = Status.zero := if_neg heS
  have h1 : (tau P hP ht).status e = Status.one := if_neg heT
  have hc0 := (hl e (by rw [h0]; decide)).trans h0
  have hc1 := (hr e (by rw [h1]; decide)).trans h1
  exact (by decide : Status.zero ≠ Status.one) (hc0.symm.trans hc1)

/-- No path goes from any face of the final cube back to any face of the
initial cube when an actual interior event is present. -/
theorem no_reverse_boundary_run (e : Fin P.n) (heS : ¬ P.inSrc e) (heT : ¬ P.inTgt e)
    {U V : Cube Lab k} (x : TrackCell P U) (y : TrackCell P V)
    (hx : TrackCell.InCube (tau P hP ht) x) (hy : TrackCell.InCube (iota P hP hs) y)
    (p : Word U V) : ¬ (track P).Run p x y := by
  classical
  intro hr
  have h0 : (iota P hP hs).status e = Status.zero := if_neg heS
  have h1 : (tau P hP ht).status e = Status.one := if_neg heT
  have hxe := (hx e (by rw [h1]; decide)).trans h1
  have hye := (hy e (by rw [h0]; decide)).trans h0
  have hm := TrackCell.run_status_mono hr e
  rw [hxe,hye] at hm
  exact (by decide : ¬ Status.one ≤ Status.zero) hm

/-- Any forward boundary run forces precisely the actual compatibility
condition on shared source/target events. -/
theorem compatible_of_boundary_run {U V : Cube Lab k}
    (α : Face U (sourceCube P hs)) (β : Face V (targetCube P ht))
    (p : Word U V) (hr : (track P).Run p ((iota P hP hs).face α) ((tau P hP ht).face β)) :
    Corners.Compatible P α.status β.status := by
  intro i j hij
  calc
    α.status i = ((iota P hP hs).face α).status (P.src i) := (iota_face_source P hP hs α i).symm
    _ ≤ ((tau P hP ht).face β).status (P.src i) := TrackCell.run_status_mono hr _
    _ = β.status j := (congrArg (((tau P hP ht).face β).status) hij).trans (tau_face_target P hP ht β j)

end CounterFreeHDA.Cubical
