import CounterFreeHDA.TrackGlueAtlas

namespace CounterFreeHDA.Cubical.TrackGlue
universe u v
variable {Lab : Type u} {k : ℕ} {P Q : PomsetData Lab}
variable (m : GlueMatch P Q) (hP : IsIntervalPom P) (hQ : IsIntervalPom Q)

/-- Q's initial cube, transported to the actual ordered interface of P. -/
noncomputable def rightBoundary (ht : P.tgtLen ≤ k) : TrackCell Q (targetCube P ht) := by
  classical
  exact {
    status e := if Q.inSrc e then Status.star else Status.zero
    config e f hef hf := by
      have hf' : Q.inSrc f := by by_contra h; exact hf (if_neg h)
      exact False.elim (hQ.src_minimal f hf' e hef)
    occ i := Q.src (Fin.cast m.len_eq i)
    inj := by
      intro i j hij
      have h := Q.src_inj hij
      exact Fin.ext (congrArg (fun t : Fin Q.srcLen => t.val) h)
    active i := if_pos ⟨Fin.cast m.len_eq i,rfl⟩
    covers e he := by
      by_cases h : Q.inSrc e
      · obtain ⟨j,hj⟩ := h
        exact ⟨Fin.cast m.len_eq.symm j,by simpa only [Fin.cast_cast,Fin.cast_refl,id_eq] using hj⟩
      · rw [if_neg h] at he
        exact False.elim ((by decide : Status.zero ≠ Status.star) he)
    labels i := (m.lab_eq i).symm
    ordered i j := hQ.src_eord _ _ }

noncomputable def middleCell (ht : P.tgtLen ≤ k) : TrackCell (glueData P Q m) (targetCube P ht) :=
  leftCell m hP (tau P hP ht)

def middleStatus : GluedE P Q → Status
  | .left _ => Status.one
  | .right _ => Status.zero
  | .mid _ => Status.star

@[simp] theorem middleCell_status (ht : P.tgtLen ≤ k) (e : GluedE P Q) :
    (middleCell m hP ht).status (index m e) = middleStatus e := by
  unfold middleCell
  rw [leftCell_raw]
  cases e with
  | left e => exact if_neg e.property
  | right e => rfl
  | mid i => exact if_pos ⟨i,rfl⟩

theorem middleCell_eq_right (ht : P.tgtLen ≤ k) :
    middleCell m hP ht = rightCell m hP hQ (rightBoundary m hQ ht) := by
  apply TrackCell.ext
  · funext e
    obtain ⟨a,rfl⟩ := (index m).surjective e
    rw [middleCell_status,rightCell_raw]
    cases a with
    | left e => rfl
    | right e => exact (if_neg e.property).symm
    | mid i => exact (if_pos ⟨Fin.cast m.len_eq i,rfl⟩).symm
  · funext i
    exact congrArg (index m) (GluedE.identified P Q m.len_eq i)

/-- The overlap of the two factor pieces is exactly the full interface cube,
including all of its lower, upper and mixed faces. -/
theorem intersection_face (ht : P.tgtLen ≤ k) {U : Cube Lab k}
    (c : TrackCell (glueData P Q m) U) (hl : LeftPart m c) (hr : RightPart m c) :
    ∃ f : Face U (targetCube P ht), (middleCell m hP ht).face f = c := by
  apply (TrackCell.exists_face_iff c (middleCell m hP ht)).mpr
  intro e he
  obtain ⟨a,rfl⟩ := (index m).surjective e
  rw [middleCell_status] at he ⊢
  cases a with
  | left e => exact hr e
  | right e => exact hl e
  | mid i => exact False.elim (he rfl)

variable {Y : Precubical.{u,v} Lab k}

noncomputable def leftPatch (p : Map (track P) Y) : Patch (track (glueData P Q m)) Y where
  pred := LeftPart m
  closed f c hc := leftPart_face m f c hc
  app c hc := p.app (restrictLeft m hP c hc)
  natural f c hc := by
    change p.app (restrictLeft m hP (c.face f) _) = _
    rw [restrictLeft_face]
    exact p.natural f _

noncomputable def rightPatch (q : Map (track Q) Y) : Patch (track (glueData P Q m)) Y where
  pred := RightPart m
  closed f c hc := rightPart_face m f c hc
  app c hc := q.app (restrictRight m hP hQ c hc)
  natural f c hc := by
    change q.app (restrictRight m hP hQ (c.face f) _) = _
    rw [restrictRight_face]
    exact q.natural f _

include hQ in
theorem patch_agreement (ht : P.tgtLen ≤ k) (p : Map (track P) Y) (q : Map (track Q) Y)
    (seam : p.app (tau P hP ht) = q.app (rightBoundary m hQ ht))
    (U : Cube Lab k) (c : TrackCell (glueData P Q m) U) (hl : LeftPart m c) (hr : RightPart m c) :
    (leftPatch m hP p).app c hl = (rightPatch m hP hQ q).app c hr := by
  obtain ⟨f,hf⟩ := intersection_face m hP ht c hl hr
  have hleft : restrictLeft m hP c hl = (tau P hP ht).face f := by
    apply leftCell_injective m hP U
    rw [leftCell_restrict,leftCell_face]
    exact hf.symm
  have hright : restrictRight m hP hQ c hr = (rightBoundary m hQ ht).face f := by
    apply rightCell_injective m hP hQ U
    rw [rightCell_restrict,rightCell_face,← middleCell_eq_right m hP hQ ht]
    exact hf.symm
  change p.app (restrictLeft m hP c hl) = q.app (restrictRight m hP hQ c hr)
  rw [hleft,hright]
  exact (p.natural f _).trans ((congrArg (Y.face f) seam).trans (q.natural f _).symm)

/-- The concrete characteristic gluing construction: compatible maps on both
factors extend to the whole actual glued characteristic HDA. -/
noncomputable def glueMap (ht : P.tgtLen ≤ k) (p : Map (track P) Y) (q : Map (track Q) Y)
    (seam : p.app (tau P hP ht) = q.app (rightBoundary m hQ ht)) :
    Map (track (glueData P Q m)) Y :=
  gluePatches (leftPatch m hP p) (rightPatch m hP hQ q)
    (fun _ c => parts_cover m c) (patch_agreement m hP hQ ht p q seam)

@[simp] theorem glueMap_left (ht : P.tgtLen ≤ k) (p : Map (track P) Y) (q : Map (track Q) Y)
    (seam : p.app (tau P hP ht) = q.app (rightBoundary m hQ ht))
    {U} (c : TrackCell P U) :
    (glueMap m hP hQ ht p q seam).app (leftCell m hP c) = p.app c := by
  have h := gluePatches_left (leftPatch m hP p) (rightPatch m hP hQ q)
    (fun _ c => parts_cover m c) (patch_agreement m hP hQ ht p q seam)
    (leftCell m hP c) (leftPart_leftCell m hP c)
  simpa only [glueMap,leftPatch,restrictLeft_leftCell] using h

@[simp] theorem glueMap_right (ht : P.tgtLen ≤ k) (p : Map (track P) Y) (q : Map (track Q) Y)
    (seam : p.app (tau P hP ht) = q.app (rightBoundary m hQ ht))
    {U} (c : TrackCell Q U) :
    (glueMap m hP hQ ht p q seam).app (rightCell m hP hQ c) = q.app c := by
  have h := gluePatches_right (leftPatch m hP p) (rightPatch m hP hQ q)
    (fun _ c => parts_cover m c) (patch_agreement m hP hQ ht p q seam)
    (rightCell m hP hQ c) (rightPart_rightCell m hP hQ c)
  simpa only [glueMap,rightPatch,restrictRight_rightCell] using h

/-- Agreement on the actual two factor inclusions determines a glued map. -/
theorem glued_map_unique (a b : Map (track (glueData P Q m)) Y)
    (hl : ∀ U (c : TrackCell P U), a.app (leftCell m hP c) = b.app (leftCell m hP c))
    (hr : ∀ U (c : TrackCell Q U), a.app (rightCell m hP hQ c) = b.app (rightCell m hP hQ c)) : a = b := by
  apply Map.ext
  funext U c
  rcases parts_cover m c with hc | hc
  · rw [← leftCell_restrict m hP c hc]
    exact hl U _
  · rw [← rightCell_restrict m hP hQ c hc]
    exact hr U _

end CounterFreeHDA.Cubical.TrackGlue
