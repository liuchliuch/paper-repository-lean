import CounterFreeHDA.Cubical
import CounterFreeHDA.Pomset

/-! The characteristic HDA B(P), built from actual interval-pomset events.
Cells retain the ordered active-event identification, so repeated labels do
not collapse positions. -/

namespace CounterFreeHDA.Cubical

universe u

namespace Face
variable {Lab : Type u} {k : ℕ} {U V W : Cube Lab k}

noncomputable def position (f : Face U V) (i : Fin U.dim) : Fin V.dim :=
  Classical.choose (f.vars i)

theorem position_spec (f : Face U V) (i : Fin U.dim) :
    f.sub (f.position i) = Sum.inl i := (Classical.choose_spec (f.vars i)).1

theorem position_unique (f : Face U V) {i : Fin U.dim} {j : Fin V.dim}
    (h : f.sub j = Sum.inl i) : j = f.position i := (Classical.choose_spec (f.vars i)).2 j h

theorem position_injective (f : Face U V) : Function.Injective f.position := by
  intro i j h
  have hh := congrArg f.sub h
  simpa only [position_spec, Sum.inl.injEq] using hh

theorem position_strictMono (f : Face U V) : StrictMono f.position := by
  intro i j hij
  by_contra h
  rcases lt_or_eq_of_le (le_of_not_gt h) with hlt | heq
  · have hji := f.ordered hlt (f.position_spec j) (f.position_spec i)
    exact (not_lt_of_ge (le_of_lt hij)) hji
  · exact (ne_of_lt hij) (f.position_injective heq.symm)

@[simp] theorem position_ident (U : Cube Lab k) (i : Fin U.dim) : (ident U).position i = i :=
  ((ident U).position_unique rfl).symm

@[simp] theorem position_comp (f : Face U V) (g : Face V W) (i : Fin U.dim) :
    (f.comp g).position i = g.position (f.position i) := by
  apply Eq.symm
  apply (f.comp g).position_unique
  simp only [comp_sub, g.position_spec, Sum.elim_inl, f.position_spec]

end Face

variable {Lab : Type u} {k : ℕ} (P : PomsetData Lab)

@[ext] structure TrackCell (U : Cube Lab k) where
  status : Fin P.n → Status
  config : ∀ e f, P.prec e f → status f ≠ Status.zero → status e = Status.one
  occ : Fin U.dim → Fin P.n
  inj : Function.Injective occ
  active : ∀ i, status (occ i) = Status.star
  covers : ∀ e, status e = Status.star → ∃ i, occ i = e
  labels : ∀ i, P.lab (occ i) = U.lab i
  ordered : ∀ i j, P.eord (occ i) (occ j) ↔ i < j

namespace TrackCell
variable {P} {U V W : Cube Lab k}

noncomputable def oldPosition (c : TrackCell P V) (e : Fin P.n) (h : c.status e = Status.star) :
    Fin V.dim := Classical.choose (c.covers e h)

theorem oldPosition_spec (c : TrackCell P V) (e : Fin P.n) (h : c.status e = Status.star) :
    c.occ (c.oldPosition e h) = e := Classical.choose_spec (c.covers e h)

@[simp] theorem oldPosition_occ (c : TrackCell P V) (i : Fin V.dim)
    (h : c.status (c.occ i) = Status.star) : c.oldPosition (c.occ i) h = i :=
  c.inj (c.oldPosition_spec _ h)

noncomputable def faceStatus (f : Face U V) (c : TrackCell P V) (e : Fin P.n) : Status := by
  classical
  exact if h : c.status e = Status.star then f.status (c.oldPosition e h) else c.status e

@[simp] theorem faceStatus_occ (f : Face U V) (c : TrackCell P V) (i : Fin V.dim) :
    faceStatus f c (c.occ i) = f.status i := by
  classical
  simp only [faceStatus, dif_pos (c.active i), oldPosition_occ]

theorem faceStatus_inactive (f : Face U V) (c : TrackCell P V) {e : Fin P.n}
    (h : c.status e ≠ Status.star) : faceStatus f c e = c.status e := by
  classical
  simp only [faceStatus, dif_neg h]

noncomputable def face (f : Face U V) (c : TrackCell P V) : TrackCell P U where
  status := faceStatus f c
  config e g heg hg := by
    have hc : c.status g ≠ Status.zero := by
      intro hz
      have hns : c.status g ≠ Status.star := by rw [hz]; decide
      exact hg ((faceStatus_inactive f c hns).trans hz)
    have he := c.config e g heg hc
    rw [faceStatus_inactive f c (by rw [he]; decide), he]
  occ i := c.occ (f.position i)
  inj := c.inj.comp f.position_injective
  active i := by
    rw [faceStatus_occ]
    simp only [Face.status, f.position_spec]
  covers e he := by
    have hc : c.status e = Status.star := by
      by_contra h
      exact h ((faceStatus_inactive f c h).symm.trans he)
    let j := c.oldPosition e hc
    have hj : f.status j = Status.star := by
      simpa only [faceStatus, dif_pos hc, j] using he
    cases hs : f.sub j with
    | inr b =>
      cases b <;> simp only [Face.status, hs] at hj <;>
        have hval := congrArg Fin.val hj <;> norm_num at hval
    | inl i =>
      refine ⟨i, ?_⟩
      rw [← f.position_unique hs]
      exact c.oldPosition_spec e hc
  labels i := (c.labels _).trans (f.labels (f.position_spec i))
  ordered i j := by
    rw [c.ordered]
    exact f.position_strictMono.lt_iff_lt

@[simp] theorem face_occ (f : Face U V) (c : TrackCell P V) (i : Fin U.dim) :
    (face f c).occ i = c.occ (f.position i) := rfl

@[simp] theorem face_status_occ (f : Face U V) (c : TrackCell P V) (i : Fin V.dim) :
    (face f c).status (c.occ i) = f.status i := faceStatus_occ f c i

theorem face_status_inactive (f : Face U V) (c : TrackCell P V) {e : Fin P.n}
    (h : c.status e ≠ Status.star) : (face f c).status e = c.status e :=
  faceStatus_inactive f c h

@[simp] theorem face_ident (c : TrackCell P U) : face (Face.ident U) c = c := by
  apply TrackCell.ext
  · funext e
    by_cases he : c.status e = Status.star
    · obtain ⟨i,rfl⟩ := c.covers e he
      rw [face_status_occ, c.active]
      rfl
    · exact face_status_inactive _ _ he
  · funext i
    simp

@[simp] theorem face_comp (f : Face U V) (g : Face V W) (c : TrackCell P W) :
    face f (face g c) = face (f.comp g) c := by
  apply TrackCell.ext
  · funext e
    by_cases he : c.status e = Status.star
    · obtain ⟨j,rfl⟩ := c.covers e he
      cases hg : g.sub j with
      | inl i =>
        have hj : j = g.position i := g.position_unique hg
        rw [hj, ← face_occ g c i, face_status_occ, face_occ, face_status_occ]
        simp only [Face.status, Face.comp_sub, g.position_spec, Sum.elim_inl]
      | inr b =>
        have hns : (face g c).status (c.occ j) ≠ Status.star := by
          rw [face_status_occ]
          cases b <;> simp only [Face.status, hg] <;> decide
        rw [face_status_inactive f _ hns, face_status_occ, face_status_occ]
        cases b <;> simp only [Face.status, Face.comp_sub, hg, Sum.elim_inr] <;> rfl
    · have hg : (face g c).status e ≠ Status.star := by
        rwa [face_status_inactive g c he]
      rw [face_status_inactive f _ hg, face_status_inactive g c he,
        face_status_inactive (f.comp g) c he]
  · funext i
    simp

noncomputable instance (U : Cube Lab k) : Fintype (TrackCell P U) := by
  letI : Finite (TrackCell P U) := Finite.of_injective
    (fun c : TrackCell P U => (c.status,c.occ)) (by
      intro c d h
      exact TrackCell.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  exact Fintype.ofFinite _

end TrackCell

/-- The actual characteristic precubical set B(P), bounded by the chosen
interface dimensions. Its cells use exactly condition (8) and active order. -/
noncomputable def track : Precubical Lab k where
  Cell := TrackCell P
  face := TrackCell.face
  face_ident := TrackCell.face_ident
  face_comp := TrackCell.face_comp

end CounterFreeHDA.Cubical
