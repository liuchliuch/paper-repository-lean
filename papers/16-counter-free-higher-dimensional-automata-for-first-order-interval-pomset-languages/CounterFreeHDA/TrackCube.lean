import CounterFreeHDA.CornerPaths
import CounterFreeHDA.Patch

/-! Every characteristic cube is convex for directed runs: a run between
its faces stays in that cube and can be followed between the corresponding
faces of any cell in any precubical set. -/
namespace CounterFreeHDA.Cubical.TrackCell
universe u v
variable {Lab : Type u} {k : ℕ} {P : PomsetData Lab} {D U V W : Cube Lab k}

def InCube (d : TrackCell P D) {U : Cube Lab k} (c : TrackCell P U) : Prop :=
  ∀ e, d.status e ≠ Status.star → c.status e = d.status e

theorem inCube_self (d : TrackCell P D) : InCube d d := fun _ _ => rfl

theorem InCube.face {d : TrackCell P D} {c : TrackCell P V} (hc : InCube d c) (f : Face U V) :
    InCube d (c.face f) := by
  intro e he
  have hn : c.status e ≠ Status.star := by rw [hc e he]; exact he
  exact (face_status_inactive f c hn).trans (hc e he)

theorem inCube_between {d : TrackCell P D} {x : TrackCell P U} {z : TrackCell P V} {y : TrackCell P W}
    (hx : InCube d x) (hy : InCube d y)
    (hxz : ∀ e, x.status e ≤ z.status e) (hzy : ∀ e, z.status e ≤ y.status e) : InCube d z := by
  intro e he
  apply le_antisymm
  · exact (hzy e).trans_eq (hy e he)
  · exact (hx e he) ▸ hxz e

/-- Face recovery commutes with the actual face maps on the whole cube. -/
theorem faceFrom_natural (d : TrackCell P D) (c : TrackCell P V) (hc : InCube d c) (f : Face U V) :
    faceFrom (c.face f) d (hc.face f) = f.comp (faceFrom c d hc) := by
  apply face_injective d
  change d.face (faceFrom (c.face f) d (hc.face f)) = d.face (f.comp (faceFrom c d hc))
  rw [faceFrom_face,← face_comp,faceFrom_face]

theorem faceFrom_of_face (d : TrackCell P D) (f : Face U D) :
    faceFrom (d.face f) d ((inCube_self d).face f) = f := by
  apply face_injective d
  exact faceFrom_face _ _ _

/-- A path whose endpoints are faces of d lifts to d's standard cube. -/
theorem run_inCube (d : TrackCell P D) {p : Word U V} {x : TrackCell P U} {y : TrackCell P V}
    (hr : (track P).Run p x y) (hx : InCube d x) (hy : InCube d y) :
    (standardCube D).Run p (faceFrom x d hx) (faceFrom y d hy) := by
  induction p with
  | nil U =>
    have he := ((track P).run_nil_iff x y).mp hr
    subst y
    exact .nil _
  | cons s p ih =>
    cases s with
    | start f hl hd =>
      obtain ⟨z,hxz,hr'⟩ := ((track P).run_start_iff f hl hd p x y).mp hr
      subst x
      have hz : InCube d z := inCube_between hx hy (lower_status_le f hl z) (run_status_mono hr')
      have hrun := ih hr' hz hy
      have he := faceFrom_natural d z hz f
      change (standardCube D).Run (.cons (.start f hl hd) p) (faceFrom (z.face f) d hx) (faceFrom y d hy)
      rw [he]
      exact .start f hl hd hrun
    | stop f hu hd =>
      have hr' := ((track P).run_stop_iff f hu hd p x y).mp hr
      have hrun := ih hr' (hx.face f) hy
      have he := faceFrom_natural d x hx f
      change (standardCube D).Run p (faceFrom (x.face f) d (hx.face f)) (faceFrom y d hy) at hrun
      rw [he] at hrun
      exact .stop f hu hd hrun

/-- Every run between faces of an actual characteristic cube is already
forced by the precubical identities of any target cell of that type. -/
theorem run_faces (d : TrackCell P D) (α : Face U D) (β : Face V D)
    {p : Word U V} (hr : (track P).Run p (d.face α) (d.face β))
    {Y : Precubical.{u,v} Lab k} (z : Y.Cell D) : Y.Run p (Y.face α z) (Y.face β z) := by
  have hrun := run_inCube d hr ((inCube_self d).face α) ((inCube_self d).face β)
  rw [faceFrom_of_face,faceFrom_of_face] at hrun
  exact (cubeMap z).map_run hrun

end CounterFreeHDA.Cubical.TrackCell
