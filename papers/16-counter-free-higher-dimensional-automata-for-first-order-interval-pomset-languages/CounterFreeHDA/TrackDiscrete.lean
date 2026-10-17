import CounterFreeHDA.TrackFaces
import CounterFreeHDA.PomsetPaths
import Mathlib.Order.WellFounded

namespace CounterFreeHDA.Cubical
universe u v
variable {Lab : Type u} {k : ℕ}

namespace Face

theorem dim_le {U V : Cube Lab k} (f : Face U V) : U.dim ≤ V.dim := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f.position f.position_injective

theorem self_eq_ident {U : Cube Lab k} (f : Face U U) : f = ident U := by
  apply Face.ext
  funext i
  have hi : f.position i = i := le_antisymm (f.position_strictMono.le_id i) (f.position_strictMono.id_le i)
  have h := f.position_spec i
  simpa only [hi,ident] using h

theorem type_eq_of_dim_eq {U V : Cube Lab k} (f : Face U V) (h : U.dim = V.dim) : U = V := by
  rcases U with ⟨n,lu⟩
  rcases V with ⟨m,lv⟩
  have hn : n = m := Fin.ext h
  subst m
  have hp : ∀ i, f.position i = i := by
    intro i
    exact le_antisymm (f.position_strictMono.le_id i) (f.position_strictMono.id_le i)
  have hl : lu = lv := by
    funext i
    have hi := f.labels (f.position_spec i)
    rw [hp] at hi
    exact hi.symm
  cases hl
  rfl

end Face

namespace TrackCell
variable {P : PomsetData Lab}

theorem status_injective {U : Cube Lab k} : Function.Injective (fun c : TrackCell P U => c.status) := by
  intro c d h
  have hd : ∀ e, d.status e ≠ Status.star → c.status e = d.status e := fun e _ => congrFun h e
  have hf := faceFrom_face c d hd
  rw [Face.self_eq_ident (faceFrom c d hd),face_ident] at hf
  exact hf.symm

/-- The status function recovers the active type, labels, order and cell. -/
theorem total_status_injective :
    Function.Injective (fun c : Σ U : Cube Lab k, TrackCell P U => c.2.status) := by
  rintro ⟨U,c⟩ ⟨V,d⟩ h
  have hd : ∀ e, d.status e ≠ Status.star → c.status e = d.status e := fun e _ => congrFun h e
  have hc : ∀ e, c.status e ≠ Status.star → d.status e = c.status e := fun e _ => (congrFun h e).symm
  have hdim : U.dim = V.dim := le_antisymm (faceFrom c d hd).dim_le (faceFrom d c hc).dim_le
  have ht := (faceFrom c d hd).type_eq_of_dim_eq hdim
  subst V
  have hcd : c = d := status_injective h
  cases hcd
  rfl

end TrackCell

/-- A completely active characteristic cell identifies its entire track with
a standard cube, so it maps to any chosen target cell of the same type. -/
noncomputable def mapFromFull {P : PomsetData Lab} {Y : Precubical.{u,v} Lab k}
    {V : Cube Lab k} (d : TrackCell P V) (full : ∀ e, d.status e = Status.star) (y : Y.Cell V) :
    Map (track P) Y := by
  let hc : ∀ {T : Cube Lab k} (c : TrackCell P T),
      ∀ e, d.status e ≠ Status.star → c.status e = d.status e :=
    fun _ e he => False.elim (he (full e))
  exact {
    app c := Y.face (TrackCell.faceFrom c d (hc c)) y
    natural f c := by
      have hf : TrackCell.faceFrom (c.face f) d (hc _) = f.comp (TrackCell.faceFrom c d (hc c)) := by
        apply TrackCell.face_injective d
        change d.face (TrackCell.faceFrom (c.face f) d (hc _)) =
          d.face (f.comp (TrackCell.faceFrom c d (hc c)))
        rw [TrackCell.faceFrom_face,← TrackCell.face_comp,TrackCell.faceFrom_face]
      change Y.face (TrackCell.faceFrom (c.face f) d (hc _)) y = _
      rw [hf]
      exact (Y.face_comp f _ y).symm }

@[simp] theorem mapFromFull_top {P : PomsetData Lab} {Y : Precubical.{u,v} Lab k}
    {V : Cube Lab k} (d : TrackCell P V) (full : ∀ e, d.status e = Status.star) (y : Y.Cell V) :
    (mapFromFull d full y).app d = y := by
  change Y.face (TrackCell.faceFrom d d (fun e he => False.elim (he (full e)))) y = y
  rw [Face.self_eq_ident (TrackCell.faceFrom d d (fun e he => False.elim (he (full e)))),Y.face_ident]

def discreteTop (V : Cube Lab k) {r s : ℕ} (src : Fin r ↪o Fin V.dim) (tgt : Fin s ↪o Fin V.dim) :
    TrackCell (discretePom V.lab src tgt).val V where
  status _ := Status.star
  config _ _ h _ := False.elim h
  occ := id
  inj := Function.injective_id
  active _ := rfl
  covers e _ := ⟨e,rfl⟩
  labels _ := rfl
  ordered _ _ := Iff.rfl

end CounterFreeHDA.Cubical
