import CounterFreeHDA.TrackGlueMaps
import CounterFreeHDA.Patch

namespace CounterFreeHDA.Cubical.TrackGlue
universe u
variable {Lab : Type u} {k : ℕ} {P Q : PomsetData Lab}
variable (m : GlueMatch P Q) (hP : IsIntervalPom P) (hQ : IsIntervalPom Q)

@[simp] theorem leftEvent_left (e : {e : Fin P.n // ¬ P.inTgt e}) :
    leftEvent m e.val = index m (.left e) := by
  apply congrArg (index m)
  unfold GluedE.leftMap
  exact dif_neg e.property
@[simp] theorem rightEvent_right (e : {e : Fin Q.n // ¬ Q.inSrc e}) :
    rightEvent m e.val = index m (.right e) := by
  apply congrArg (index m)
  unfold GluedE.rightMap
  exact dif_neg e.property
@[simp] theorem leftEvent_tgt (i : Fin P.tgtLen) :
    leftEvent m (P.tgt i) = index m (.mid i) := congrArg (index m) (GluedE.leftMap_tgt P Q i)
@[simp] theorem rightEvent_src (i : Fin P.tgtLen) :
    rightEvent m (Q.src (Fin.cast m.len_eq i)) = index m (.mid i) := by
  unfold rightEvent
  rw [GluedE.rightMap_src]
  simp

theorem leftPart_leftCell {U : Cube Lab k} (c : TrackCell P U) : LeftPart m (leftCell m hP c) := by
  intro e
  rw [leftCell_raw]
  rfl

theorem rightPart_rightCell {U : Cube Lab k} (c : TrackCell Q U) : RightPart m (rightCell m hP hQ c) := by
  intro e
  rw [rightCell_raw]
  rfl

@[simp] theorem leftCell_restrict {U : Cube Lab k} (c : TrackCell (glueData P Q m) U)
    (hc : LeftPart m c) : leftCell m hP (restrictLeft m hP c hc) = c := by
  apply TrackCell.ext
  · funext e
    obtain ⟨a,rfl⟩ := (index m).surjective e
    cases a with
    | left a => rw [← leftEvent_left,leftCell_status]; rfl
    | mid i => rw [← leftEvent_tgt,leftCell_status]; rfl
    | right a => rw [leftCell_raw]; exact (hc a).symm
  · funext i
    exact leftOcc_spec m c hc i

@[simp] theorem rightCell_restrict {U : Cube Lab k} (c : TrackCell (glueData P Q m) U)
    (hc : RightPart m c) : rightCell m hP hQ (restrictRight m hP hQ c hc) = c := by
  apply TrackCell.ext
  · funext e
    obtain ⟨a,rfl⟩ := (index m).surjective e
    cases a with
    | right a => rw [← rightEvent_right,rightCell_status]; rfl
    | mid i => rw [← rightEvent_src,rightCell_status]; rfl
    | left a => rw [rightCell_raw]; exact (hc a).symm
  · funext i
    exact rightOcc_spec m c hc i

@[simp] theorem restrictLeft_leftCell {U : Cube Lab k} (c : TrackCell P U)
    (hc : LeftPart m (leftCell m hP c)) : restrictLeft m hP (leftCell m hP c) hc = c := by
  apply leftCell_injective m hP U
  exact leftCell_restrict m hP _ hc

@[simp] theorem restrictRight_rightCell {U : Cube Lab k} (c : TrackCell Q U)
    (hc : RightPart m (rightCell m hP hQ c)) : restrictRight m hP hQ (rightCell m hP hQ c) hc = c := by
  apply rightCell_injective m hP hQ U
  exact rightCell_restrict m hP hQ _ hc

@[simp] theorem restrictLeft_face {U V : Cube Lab k} (f : Face U V)
    (c : TrackCell (glueData P Q m) V) (hc : LeftPart m c) :
    restrictLeft m hP (c.face f) (leftPart_face m f c hc) = (restrictLeft m hP c hc).face f := by
  apply leftCell_injective m hP U
  rw [leftCell_restrict,leftCell_face,leftCell_restrict]

@[simp] theorem restrictRight_face {U V : Cube Lab k} (f : Face U V)
    (c : TrackCell (glueData P Q m) V) (hc : RightPart m c) :
    restrictRight m hP hQ (c.face f) (rightPart_face m f c hc) = (restrictRight m hP hQ c hc).face f := by
  apply rightCell_injective m hP hQ U
  rw [rightCell_restrict,rightCell_face,rightCell_restrict]

end CounterFreeHDA.Cubical.TrackGlue
