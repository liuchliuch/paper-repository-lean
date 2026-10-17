import CounterFreeHDA.TrackGlue

namespace CounterFreeHDA.Cubical.TrackGlue
universe u
variable {Lab : Type u} {k : ℕ} {P Q : PomsetData Lab}
variable (m : GlueMatch P Q) (hP : IsIntervalPom P) (hQ : IsIntervalPom Q)

include hP in
theorem leftEvent_prec (e f : Fin P.n) :
    (glueData P Q m).prec (leftEvent m e) (leftEvent m f) ↔ P.prec e f := by
  classical
  change gluePrec m.len_eq ((index m).symm (index m _)) ((index m).symm (index m _)) ↔ _
  rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]
  unfold GluedE.leftMap
  split_ifs with he hf hf
  · exact iff_of_false not_false (hP.tgt_maximal e he f)
  · exact iff_of_false not_false (hP.tgt_maximal e he f)
  · simp only [gluePrec,Classical.choose_spec hf]
  · rfl

include hQ in
theorem rightEvent_prec (e f : Fin Q.n) :
    (glueData P Q m).prec (rightEvent m e) (rightEvent m f) ↔ Q.prec e f := by
  classical
  change gluePrec m.len_eq ((index m).symm (index m _)) ((index m).symm (index m _)) ↔ _
  rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]
  unfold GluedE.rightMap
  split_ifs with he hf hf
  · exact iff_of_false not_false (hQ.src_minimal f hf e)
  · simp only [gluePrec,Fin.cast_cast,Fin.cast_refl,id_eq,Classical.choose_spec he]
  · exact iff_of_false not_false (hQ.src_minimal f hf e)
  · rfl

theorem left_face_status {U V : Cube Lab k} (f : Face U V) (c : TrackCell P V) (e : Fin P.n) :
    ((leftCell m hP c).face f).status (leftEvent m e) = (c.face f).status e := by
  by_cases he : c.status e = Status.star
  · obtain ⟨i,rfl⟩ := c.covers e he
    have h := TrackCell.face_status_occ f (leftCell m hP c) i
    change ((leftCell m hP c).face f).status (leftEvent m (c.occ i)) = _ at h
    rw [h,TrackCell.face_status_occ]
  · rw [TrackCell.face_status_inactive f _ (by rwa [leftCell_status]),
      leftCell_status,TrackCell.face_status_inactive f c he]

theorem right_face_status {U V : Cube Lab k} (f : Face U V) (c : TrackCell Q V) (e : Fin Q.n) :
    ((rightCell m hP hQ c).face f).status (rightEvent m e) = (c.face f).status e := by
  by_cases he : c.status e = Status.star
  · obtain ⟨i,rfl⟩ := c.covers e he
    have h := TrackCell.face_status_occ f (rightCell m hP hQ c) i
    change ((rightCell m hP hQ c).face f).status (rightEvent m (c.occ i)) = _ at h
    rw [h,TrackCell.face_status_occ]
  · rw [TrackCell.face_status_inactive f _ (by rwa [rightCell_status]),
      rightCell_status,TrackCell.face_status_inactive f c he]

@[simp] theorem leftCell_face {U V : Cube Lab k} (f : Face U V) (c : TrackCell P V) :
    leftCell m hP (c.face f) = (leftCell m hP c).face f := by
  apply TrackCell.ext
  · funext e
    obtain ⟨a,rfl⟩ := (index m).surjective e
    cases a with
    | left a =>
      have ha : leftEvent m a.val = index m (.left a) := by
        apply congrArg (index m)
        unfold GluedE.leftMap
        exact dif_neg a.property
      rw [← ha,leftCell_status,left_face_status]
    | mid i =>
      have ha : leftEvent m (P.tgt i) = index m (.mid i) := congrArg (index m) (GluedE.leftMap_tgt P Q i)
      rw [← ha,leftCell_status,left_face_status]
    | right a =>
      rw [leftCell_raw,TrackCell.face_status_inactive f _ (by rw [leftCell_raw]; change Status.zero ≠ Status.star; decide),leftCell_raw]
      rfl
  · funext i; rfl

@[simp] theorem rightCell_face {U V : Cube Lab k} (f : Face U V) (c : TrackCell Q V) :
    rightCell m hP hQ (c.face f) = (rightCell m hP hQ c).face f := by
  apply TrackCell.ext
  · funext e
    obtain ⟨a,rfl⟩ := (index m).surjective e
    cases a with
    | right a =>
      have ha : rightEvent m a.val = index m (.right a) := by
        apply congrArg (index m)
        unfold GluedE.rightMap
        exact dif_neg a.property
      rw [← ha,rightCell_status,right_face_status]
    | mid i =>
      have ha : rightEvent m (Q.src (Fin.cast m.len_eq i)) = index m (.mid i) := by
        unfold rightEvent
        rw [GluedE.rightMap_src]
        simp
      rw [← ha,rightCell_status,right_face_status]
    | left a =>
      rw [rightCell_raw,TrackCell.face_status_inactive f _ (by rw [rightCell_raw]; change Status.one ≠ Status.star; decide),rightCell_raw]
      rfl
  · funext i; rfl

noncomputable def leftMap : Map (track (k := k) P) (track (glueData P Q m)) where
  app := leftCell m hP
  natural := leftCell_face m hP
noncomputable def rightMap : Map (track (k := k) Q) (track (glueData P Q m)) where
  app := rightCell m hP hQ
  natural := rightCell_face m hP hQ

theorem leftCell_injective (U : Cube Lab k) : Function.Injective (leftCell m hP (U := U)) := by
  intro c d h
  apply TrackCell.ext
  · funext e
    have he := congrArg (fun z : TrackCell (glueData P Q m) U => z.status (leftEvent m e)) h
    simpa only [leftCell_status] using he
  · funext i
    have hi := congrArg (fun z : TrackCell (glueData P Q m) U => z.occ i) h
    exact GluedE.leftMap_inj P Q ((index m).injective hi)

theorem rightCell_injective (U : Cube Lab k) : Function.Injective (rightCell m hP hQ (U := U)) := by
  intro c d h
  apply TrackCell.ext
  · funext e
    have he := congrArg (fun z : TrackCell (glueData P Q m) U => z.status (rightEvent m e)) h
    simpa only [rightCell_status] using he
  · funext i
    have hi := congrArg (fun z : TrackCell (glueData P Q m) U => z.occ i) h
    exact GluedE.rightMap_inj P Q m.len_eq ((index m).injective hi)

theorem left_active_preimage {U : Cube Lab k} (c : TrackCell (glueData P Q m) U)
    (hc : LeftPart m c) (i : Fin U.dim) : ∃ e, leftEvent m e = c.occ i := by
  have he : c.occ i = index m ((index m).symm (c.occ i)) := ((index m).apply_symm_apply _).symm
  cases hr : (index m).symm (c.occ i) with
  | left e =>
    refine ⟨e.val,?_⟩
    rw [he,hr]
    apply congrArg (index m)
    unfold GluedE.leftMap
    exact dif_neg e.property
  | mid j =>
    refine ⟨P.tgt j,?_⟩
    rw [he,hr]
    exact congrArg (index m) (GluedE.leftMap_tgt P Q j)
  | right e =>
    have h := c.active i
    rw [he,hr,hc e] at h
    exact False.elim ((by decide : Status.zero ≠ Status.star) h)

theorem right_active_preimage {U : Cube Lab k} (c : TrackCell (glueData P Q m) U)
    (hc : RightPart m c) (i : Fin U.dim) : ∃ e, rightEvent m e = c.occ i := by
  have he : c.occ i = index m ((index m).symm (c.occ i)) := ((index m).apply_symm_apply _).symm
  cases hr : (index m).symm (c.occ i) with
  | right e =>
    refine ⟨e.val,?_⟩
    rw [he,hr]
    apply congrArg (index m)
    unfold GluedE.rightMap
    exact dif_neg e.property
  | mid j =>
    refine ⟨Q.src (Fin.cast m.len_eq j),?_⟩
    rw [he,hr]
    unfold rightEvent
    rw [GluedE.rightMap_src]
    simp
  | left e =>
    have h := c.active i
    rw [he,hr,hc e] at h
    exact False.elim ((by decide : Status.one ≠ Status.star) h)

noncomputable def leftOcc {U : Cube Lab k} (c : TrackCell (glueData P Q m) U)
    (hc : LeftPart m c) (i : Fin U.dim) : Fin P.n := Classical.choose (left_active_preimage m c hc i)
noncomputable def rightOcc {U : Cube Lab k} (c : TrackCell (glueData P Q m) U)
    (hc : RightPart m c) (i : Fin U.dim) : Fin Q.n := Classical.choose (right_active_preimage m c hc i)

@[simp] theorem leftOcc_spec {U : Cube Lab k} (c : TrackCell (glueData P Q m) U)
    (hc : LeftPart m c) (i : Fin U.dim) : leftEvent m (leftOcc m c hc i) = c.occ i :=
  Classical.choose_spec (left_active_preimage m c hc i)
@[simp] theorem rightOcc_spec {U : Cube Lab k} (c : TrackCell (glueData P Q m) U)
    (hc : RightPart m c) (i : Fin U.dim) : rightEvent m (rightOcc m c hc i) = c.occ i :=
  Classical.choose_spec (right_active_preimage m c hc i)

noncomputable def restrictLeft {U : Cube Lab k} (c : TrackCell (glueData P Q m) U)
    (hc : LeftPart m c) : TrackCell P U where
  status e := c.status (leftEvent m e)
  config e f hef hf := c.config _ _ ((leftEvent_prec m hP e f).mpr hef) hf
  occ := leftOcc m c hc
  inj := by
    intro i j hij
    apply c.inj
    rw [← leftOcc_spec m c hc i,← leftOcc_spec m c hc j,hij]
  active i := by rw [leftOcc_spec]; exact c.active i
  covers e he := by
    obtain ⟨i,hi⟩ := c.covers (leftEvent m e) he
    refine ⟨i,?_⟩
    apply GluedE.leftMap_inj P Q
    apply (index m).injective
    exact (leftOcc_spec m c hc i).trans hi
  labels i := by
    have h := c.labels i
    rw [← leftOcc_spec m c hc i] at h
    change glueLab m ((index m).symm (index m _)) = _ at h
    simpa only [Equiv.symm_apply_apply,glueLab_left] using h
  ordered i j := by
    have h := c.ordered i j
    rw [← leftOcc_spec m c hc i,← leftOcc_spec m c hc j] at h
    change glueEord m.len_eq ((index m).symm (index m _)) ((index m).symm (index m _)) ↔ _ at h
    simpa only [Equiv.symm_apply_apply,glueEord_left m hP] using h

noncomputable def restrictRight {U : Cube Lab k} (c : TrackCell (glueData P Q m) U)
    (hc : RightPart m c) : TrackCell Q U where
  status e := c.status (rightEvent m e)
  config e f hef hf := c.config _ _ ((rightEvent_prec m hQ e f).mpr hef) hf
  occ := rightOcc m c hc
  inj := by
    intro i j hij
    apply c.inj
    rw [← rightOcc_spec m c hc i,← rightOcc_spec m c hc j,hij]
  active i := by rw [rightOcc_spec]; exact c.active i
  covers e he := by
    obtain ⟨i,hi⟩ := c.covers (rightEvent m e) he
    refine ⟨i,?_⟩
    apply GluedE.rightMap_inj P Q m.len_eq
    apply (index m).injective
    exact (rightOcc_spec m c hc i).trans hi
  labels i := by
    have h := c.labels i
    rw [← rightOcc_spec m c hc i] at h
    change glueLab m ((index m).symm (index m _)) = _ at h
    simpa only [Equiv.symm_apply_apply,glueLab_right] using h
  ordered i j := by
    have h := c.ordered i j
    rw [← rightOcc_spec m c hc i,← rightOcc_spec m c hc j] at h
    change glueEord m.len_eq ((index m).symm (index m _)) ((index m).symm (index m _)) ↔ _ at h
    simpa only [Equiv.symm_apply_apply,glueEord_right m hP hQ] using h

end CounterFreeHDA.Cubical.TrackGlue
