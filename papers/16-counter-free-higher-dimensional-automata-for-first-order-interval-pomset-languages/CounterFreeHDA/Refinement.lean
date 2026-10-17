import CounterFreeHDA.TrackIso

/-! A genuine subsumption induces a map of characteristic HDAs. Active-event
orders agree because simultaneously active events are incomparable. -/
namespace CounterFreeHDA
universe u
variable {Lab : Type u}
namespace Refinement

structure Witness (P Q : IntervalPom Lab) where
  event : Fin P.n ≃ Fin Q.n
  source_len : P.srcLen = Q.srcLen
  target_len : P.tgtLen = Q.tgtLen
  labels : ∀ e, P.lab e = Q.lab (event e)
  source : ∀ i, event (P.src i) = Q.src (Fin.cast source_len i)
  target : ∀ i, event (P.tgt i) = Q.tgt (Fin.cast target_len i)
  precedence : ∀ e f, Q.prec (event e) (event f) → P.prec e f
  order : ∀ e f, ¬ P.prec e f → ¬ P.prec f e → (P.eord e f ↔ Q.eord (event e) (event f))

noncomputable def witness {P Q : IntervalPom Lab} (h : P ⊑ₛ Q) : Witness P Q :=
  Classical.choice (by
    obtain ⟨e,hs,ht,hl,hsrc,htgt,hp,ho⟩ := h
    exact ⟨⟨e,hs,ht,hl,hsrc,htgt,hp,ho⟩⟩)

variable {P Q : IntervalPom Lab} (R : Witness P Q)

theorem source_image (e : Fin P.n) : Q.val.inSrc (R.event e) ↔ P.val.inSrc e := by
  constructor
  · rintro ⟨j,hj⟩
    refine ⟨Fin.cast R.source_len.symm j,R.event.injective ?_⟩
    exact (R.source _).trans (by simpa only [Fin.cast_cast,Fin.cast_refl,id_eq] using hj)
  · rintro ⟨i,hi⟩
    exact ⟨Fin.cast R.source_len i,(R.source i).symm.trans (congrArg R.event hi)⟩

theorem target_image (e : Fin P.n) : Q.val.inTgt (R.event e) ↔ P.val.inTgt e := by
  constructor
  · rintro ⟨j,hj⟩
    refine ⟨Fin.cast R.target_len.symm j,R.event.injective ?_⟩
    exact (R.target _).trans (by simpa only [Fin.cast_cast,Fin.cast_refl,id_eq] using hj)
  · rintro ⟨i,hi⟩
    exact ⟨Fin.cast R.target_len i,(R.target i).symm.trans (congrArg R.event hi)⟩

open Cubical
variable {k : ℕ}

private theorem active_incomparable {U : Cube Lab k} (c : TrackCell P.val U) (i j : Fin U.dim) :
    ¬ P.prec (c.occ i) (c.occ j) := by
  intro h
  have hn : c.status (c.occ j) ≠ Status.zero := by rw [c.active]; decide
  have hs := c.config _ _ h hn
  rw [c.active] at hs
  exact (by decide : Status.star ≠ Status.one) hs

def transport {U : Cube Lab k} (c : TrackCell P.val U) : TrackCell Q.val U where
  status e := c.status (R.event.symm e)
  config e f hef hf := by
    have hp : P.prec (R.event.symm e) (R.event.symm f) := R.precedence _ _
      (by simpa only [Equiv.apply_symm_apply] using hef)
    exact c.config _ _ hp hf
  occ i := R.event (c.occ i)
  inj := R.event.injective.comp c.inj
  active i := by simpa only [Equiv.symm_apply_apply] using c.active i
  covers e he := by
    obtain ⟨i,hi⟩ := c.covers (R.event.symm e) he
    exact ⟨i,(congrArg R.event hi).trans (R.event.apply_symm_apply e)⟩
  labels i := (R.labels _).symm.trans (c.labels i)
  ordered i j := (R.order _ _ (active_incomparable c i j) (active_incomparable c j i)).symm.trans (c.ordered i j)

@[simp] theorem transport_status {U : Cube Lab k} (c : TrackCell P.val U) (e : Fin P.n) :
    (transport R c).status (R.event e) = c.status e := by
  change c.status (R.event.symm (R.event e)) = _
  rw [Equiv.symm_apply_apply]

@[simp] theorem transport_face {U V : Cube Lab k} (f : Cubical.Face U V) (c : TrackCell P.val V) :
    transport R (c.face f) = (transport R c).face f := by
  apply TrackCell.status_injective
  funext a
  obtain ⟨e,rfl⟩ := R.event.surjective a
  change (transport R (c.face f)).status (R.event e) = ((transport R c).face f).status (R.event e)
  rw [transport_status]
  by_cases he : c.status e = Status.star
  · obtain ⟨i,rfl⟩ := c.covers e he
    have h := TrackCell.face_status_occ f (transport R c) i
    change ((transport R c).face f).status (R.event (c.occ i)) = f.status i at h
    rw [TrackCell.face_status_occ,h]
  · have hn : (transport R c).status (R.event e) ≠ Status.star := by simpa only [transport_status] using he
    rw [TrackCell.face_status_inactive f c he,TrackCell.face_status_inactive f (transport R c) hn,transport_status]

def map : Map (track (k := k) P.val) (track Q.val) where
  app := transport R
  natural := transport_face R

end Refinement
end CounterFreeHDA
