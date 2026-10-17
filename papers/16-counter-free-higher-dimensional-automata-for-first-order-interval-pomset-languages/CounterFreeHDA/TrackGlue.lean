import CounterFreeHDA.TrackFaces
import CounterFreeHDA.TrackBoundary
import CounterFreeHDA.GluingCount

/-! The concrete two-factor atlas of the characteristic HDA of a gluing. -/

namespace CounterFreeHDA.Cubical.TrackGlue
universe u
variable {Lab : Type u} {k : ℕ} {P Q : PomsetData Lab}

noncomputable def index (m : GlueMatch P Q) : GluedE P Q ≃ Fin (glueData P Q m).n :=
  Fintype.equivFin _

noncomputable def leftEvent (m : GlueMatch P Q) (e : Fin P.n) : Fin (glueData P Q m).n :=
  index m (GluedE.leftMap P Q e)
noncomputable def rightEvent (m : GlueMatch P Q) (e : Fin Q.n) : Fin (glueData P Q m).n :=
  index m (GluedE.rightMap P Q m.len_eq e)

def leftRaw {U : Cube Lab k} (c : TrackCell P U) : GluedE P Q → Status
  | .left e => c.status e.val
  | .right _ => Status.zero
  | .mid i => c.status (P.tgt i)

def rightRaw (m : GlueMatch P Q) {U : Cube Lab k} (c : TrackCell Q U) : GluedE P Q → Status
  | .left _ => Status.one
  | .right e => c.status e.val
  | .mid i => c.status (Q.src (Fin.cast m.len_eq i))

theorem leftRaw_map {U : Cube Lab k} (c : TrackCell P U) (e : Fin P.n) :
    leftRaw (Q := Q) c (GluedE.leftMap P Q e) = c.status e := by
  classical
  unfold GluedE.leftMap
  split_ifs with h
  · exact congrArg c.status (Classical.choose_spec h)
  · rfl

theorem rightRaw_map (m : GlueMatch P Q) {U : Cube Lab k} (c : TrackCell Q U) (e : Fin Q.n) :
    rightRaw m c (GluedE.rightMap P Q m.len_eq e) = c.status e := by
  classical
  unfold GluedE.rightMap
  split_ifs with h
  · simpa only [rightRaw,Fin.cast_cast,Fin.cast_refl,id_eq] using
      congrArg c.status (Classical.choose_spec h)
  · rfl

variable (m : GlueMatch P Q) (hP : IsIntervalPom P) (hQ : IsIntervalPom Q)

noncomputable def leftCell {U : Cube Lab k} (c : TrackCell P U) : TrackCell (glueData P Q m) U where
  status e := leftRaw c ((index m).symm e)
  config := by
    intro e f hef hf
    change gluePrec m.len_eq ((index m).symm e) ((index m).symm f) at hef
    change leftRaw c ((index m).symm e) = _
    change leftRaw c ((index m).symm f) ≠ Status.zero at hf
    cases he : (index m).symm e <;> cases hg : (index m).symm f <;>
      simp only [he,hg,gluePrec,leftRaw] at hef hf ⊢ <;>
      first | contradiction | rfl | exact c.config _ _ hef hf
  occ i := leftEvent m (c.occ i)
  inj := (index m).injective.comp ((GluedE.leftMap_inj P Q).comp c.inj)
  active i := by
    change leftRaw c ((index m).symm (index m (GluedE.leftMap P Q (c.occ i)))) = _
    rw [Equiv.symm_apply_apply,leftRaw_map]
    exact c.active i
  covers e he := by
    obtain ⟨a,rfl⟩ := (index m).surjective e
    change leftRaw c ((index m).symm (index m a)) = Status.star at he
    rw [Equiv.symm_apply_apply] at he
    cases a with
    | left a =>
      obtain ⟨i,hi⟩ := c.covers a.val he
      refine ⟨i,?_⟩
      change index m (GluedE.leftMap P Q (c.occ i)) = _
      rw [hi]
      apply congrArg (index m)
      unfold GluedE.leftMap
      exact dif_neg a.property
    | right a => exact False.elim ((by decide : Status.zero ≠ Status.star) he)
    | mid j =>
      obtain ⟨i,hi⟩ := c.covers (P.tgt j) he
      refine ⟨i,?_⟩
      change index m (GluedE.leftMap P Q (c.occ i)) = _
      rw [hi,GluedE.leftMap_tgt]
  labels i := by
    change glueLab m ((index m).symm (index m (GluedE.leftMap P Q (c.occ i)))) = _
    rw [Equiv.symm_apply_apply,glueLab_left]
    exact c.labels i
  ordered i j := by
    change glueEord m.len_eq ((index m).symm (index m _)) ((index m).symm (index m _)) ↔ _
    rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply,glueEord_left m hP]
    exact c.ordered i j

noncomputable def rightCell {U : Cube Lab k} (c : TrackCell Q U) : TrackCell (glueData P Q m) U where
  status e := rightRaw m c ((index m).symm e)
  config := by
    intro e f hef hf
    change gluePrec m.len_eq ((index m).symm e) ((index m).symm f) at hef
    change rightRaw m c ((index m).symm e) = _
    change rightRaw m c ((index m).symm f) ≠ Status.zero at hf
    cases he : (index m).symm e <;> cases hg : (index m).symm f <;>
      simp only [he,hg,gluePrec,rightRaw] at hef hf ⊢ <;>
      first | contradiction | rfl | exact c.config _ _ hef hf
  occ i := rightEvent m (c.occ i)
  inj := (index m).injective.comp ((GluedE.rightMap_inj P Q m.len_eq).comp c.inj)
  active i := by
    change rightRaw m c ((index m).symm (index m (GluedE.rightMap P Q m.len_eq (c.occ i)))) = _
    rw [Equiv.symm_apply_apply,rightRaw_map]
    exact c.active i
  covers e he := by
    obtain ⟨a,rfl⟩ := (index m).surjective e
    change rightRaw m c ((index m).symm (index m a)) = Status.star at he
    rw [Equiv.symm_apply_apply] at he
    cases a with
    | left a => exact False.elim ((by decide : Status.one ≠ Status.star) he)
    | right a =>
      obtain ⟨i,hi⟩ := c.covers a.val he
      refine ⟨i,?_⟩
      change index m (GluedE.rightMap P Q m.len_eq (c.occ i)) = _
      rw [hi]
      apply congrArg (index m)
      unfold GluedE.rightMap
      exact dif_neg a.property
    | mid j =>
      obtain ⟨i,hi⟩ := c.covers (Q.src (Fin.cast m.len_eq j)) he
      refine ⟨i,?_⟩
      change index m (GluedE.rightMap P Q m.len_eq (c.occ i)) = _
      rw [hi,GluedE.rightMap_src]
      simp
  labels i := by
    change glueLab m ((index m).symm (index m (GluedE.rightMap P Q m.len_eq (c.occ i)))) = _
    rw [Equiv.symm_apply_apply,glueLab_right]
    exact c.labels i
  ordered i j := by
    change glueEord m.len_eq ((index m).symm (index m _)) ((index m).symm (index m _)) ↔ _
    rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply,glueEord_right m hP hQ]
    exact c.ordered i j

@[simp] theorem leftCell_status {U : Cube Lab k} (c : TrackCell P U) (e : Fin P.n) :
    (leftCell m hP c).status (leftEvent m e) = c.status e := by
  change leftRaw c ((index m).symm (index m _)) = _
  rw [Equiv.symm_apply_apply,leftRaw_map]

@[simp] theorem rightCell_status {U : Cube Lab k} (c : TrackCell Q U) (e : Fin Q.n) :
    (rightCell m hP hQ c).status (rightEvent m e) = c.status e := by
  change rightRaw m c ((index m).symm (index m _)) = _
  rw [Equiv.symm_apply_apply,rightRaw_map]

@[simp] theorem leftCell_raw {U : Cube Lab k} (c : TrackCell P U) (e : GluedE P Q) :
    (leftCell m hP c).status (index m e) = leftRaw c e := by
  change leftRaw c ((index m).symm (index m e)) = _
  rw [Equiv.symm_apply_apply]

@[simp] theorem rightCell_raw {U : Cube Lab k} (c : TrackCell Q U) (e : GluedE P Q) :
    (rightCell m hP hQ c).status (index m e) = rightRaw m c e := by
  change rightRaw m c ((index m).symm (index m e)) = _
  rw [Equiv.symm_apply_apply]

/-- Configurations whose noninterface events of Q have not started. -/
def LeftPart {U : Cube Lab k} (c : TrackCell (glueData P Q m) U) : Prop :=
  ∀ e : {e : Fin Q.n // ¬ Q.inSrc e}, c.status (index m (.right e)) = Status.zero

/-- Configurations whose noninterface events of P have all completed. -/
def RightPart {U : Cube Lab k} (c : TrackCell (glueData P Q m) U) : Prop :=
  ∀ e : {e : Fin P.n // ¬ P.inTgt e}, c.status (index m (.left e)) = Status.one

/-- Every actual glued configuration lies in one of the two factor pieces.
This uses the actual cross-factor precedence, not an assumed atlas cover. -/
theorem parts_cover {U : Cube Lab k} (c : TrackCell (glueData P Q m) U) :
    LeftPart m c ∨ RightPart m c := by
  classical
  by_cases hl : LeftPart m c
  · exact Or.inl hl
  · right
    obtain ⟨q,hq⟩ := not_forall.mp hl
    intro p
    apply c.config _ (index m (.right q)) _ hq
    change gluePrec m.len_eq ((index m).symm (index m (.left p)))
      ((index m).symm (index m (.right q)))
    rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]
    trivial

theorem leftPart_face {U V : Cube Lab k} (f : Face U V)
    (c : TrackCell (glueData P Q m) V) (hc : LeftPart m c) : LeftPart m (c.face f) := by
  intro e
  rw [TrackCell.face_status_inactive f c (by rw [hc e]; decide),hc e]

theorem rightPart_face {U V : Cube Lab k} (f : Face U V)
    (c : TrackCell (glueData P Q m) V) (hc : RightPart m c) : RightPart m (c.face f) := by
  intro e
  rw [TrackCell.face_status_inactive f c (by rw [hc e]; decide),hc e]

end CounterFreeHDA.Cubical.TrackGlue
