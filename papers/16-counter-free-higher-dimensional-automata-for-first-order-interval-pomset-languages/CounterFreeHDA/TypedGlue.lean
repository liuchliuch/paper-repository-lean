import CounterFreeHDA.TypedBoundary

namespace CounterFreeHDA.Cubical.TrackGlue
universe u
variable {Lab : Type u} {P Q : PomsetData Lab} (m : GlueMatch P Q)

theorem inSrc_left (e : Fin P.n) :
    (glueData P Q m).inSrc (leftEvent m e) ↔ P.inSrc e := by
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨i,GluedE.leftMap_inj P Q ((index m).injective hi)⟩
  · rintro ⟨i,hi⟩
    exact ⟨i,congrArg (leftEvent m) hi⟩

theorem inTgt_right (e : Fin Q.n) :
    (glueData P Q m).inTgt (rightEvent m e) ↔ Q.inTgt e := by
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨i,GluedE.rightMap_inj P Q m.len_eq ((index m).injective hi)⟩
  · rintro ⟨i,hi⟩
    exact ⟨i,congrArg (rightEvent m) hi⟩

theorem not_inSrc_right (e : {e : Fin Q.n // ¬ Q.inSrc e}) :
    ¬ (glueData P Q m).inSrc (index m (.right e)) := by
  rintro ⟨i,hi⟩
  have h := congrArg (GluedE.leftProjection P Q) ((index m).injective hi)
  rw [GluedE.leftProjection_leftMap] at h
  cases h

theorem not_inTgt_left (e : {e : Fin P.n // ¬ P.inTgt e}) :
    ¬ (glueData P Q m).inTgt (index m (.left e)) := by
  rintro ⟨i,hi⟩
  have h := congrArg (GluedE.rightProjection P Q m.len_eq) ((index m).injective hi)
  rw [GluedE.rightProjection_rightMap] at h
  cases h

end CounterFreeHDA.Cubical.TrackGlue

namespace CounterFreeHDA.Cubical.Arrow
universe u v
variable {Lab : Type u} {k : ℕ} {U V W : Cube Lab k}
variable (A : Arrow U V) (B : Arrow V W)
open TrackGlue

@[simp] theorem sourceCell_comp :
    (A.comp B).sourceCell = leftCell (GlueMatch.ofType (A.target.trans B.source.symm)) A.pom.property A.sourceCell := by
  classical
  let m := GlueMatch.ofType (A.target.trans B.source.symm)
  apply TrackCell.status_injective
  funext e
  change (A.comp B).sourceCell.status e = (leftCell m A.pom.property A.sourceCell).status e
  obtain ⟨a,rfl⟩ := (index m).surjective e
  cases a with
  | left a =>
    rw [← leftEvent_left,leftCell_status]
    change (if (glueData A.pom.val B.pom.val m).inSrc (leftEvent m a.val) then Status.star else Status.zero) =
      (if A.pom.val.inSrc a.val then Status.star else Status.zero)
    rw [inSrc_left]
  | mid i =>
    rw [← leftEvent_tgt,leftCell_status]
    change (if (glueData A.pom.val B.pom.val m).inSrc (leftEvent m (A.pom.tgt i)) then Status.star else Status.zero) =
      (if A.pom.val.inSrc (A.pom.tgt i) then Status.star else Status.zero)
    rw [inSrc_left]
  | right a =>
    rw [leftCell_raw]
    change (if (glueData A.pom.val B.pom.val m).inSrc (index m (.right a)) then Status.star else Status.zero) = Status.zero
    rw [if_neg (not_inSrc_right m a)]

@[simp] theorem targetCell_comp :
    (A.comp B).targetCell = rightCell (GlueMatch.ofType (A.target.trans B.source.symm))
      A.pom.property B.pom.property B.targetCell := by
  classical
  let m := GlueMatch.ofType (A.target.trans B.source.symm)
  apply TrackCell.status_injective
  funext e
  change (A.comp B).targetCell.status e = (rightCell m A.pom.property B.pom.property B.targetCell).status e
  obtain ⟨a,rfl⟩ := (index m).surjective e
  cases a with
  | right a =>
    rw [← rightEvent_right,rightCell_status]
    change (if (glueData A.pom.val B.pom.val m).inTgt (rightEvent m a.val) then Status.star else Status.one) =
      (if B.pom.val.inTgt a.val then Status.star else Status.one)
    rw [inTgt_right]
  | mid i =>
    rw [← rightEvent_src,rightCell_status]
    change (if (glueData A.pom.val B.pom.val m).inTgt (rightEvent m (B.pom.src (Fin.cast m.len_eq i))) then Status.star else Status.one) =
      (if B.pom.val.inTgt (B.pom.src (Fin.cast m.len_eq i)) then Status.star else Status.one)
    rw [inTgt_right]
  | left a =>
    rw [rightCell_raw]
    change (if (glueData A.pom.val B.pom.val m).inTgt (index m (.left a)) then Status.star else Status.one) = Status.one
    rw [if_neg (not_inTgt_left m a)]

/-- The actual two typed boundary configurations identify at the seam. -/
theorem seamCell_eq :
    leftCell (GlueMatch.ofType (A.target.trans B.source.symm)) A.pom.property A.targetCell =
    rightCell (GlueMatch.ofType (A.target.trans B.source.symm)) A.pom.property B.pom.property B.sourceCell := by
  classical
  let m := GlueMatch.ofType (A.target.trans B.source.symm)
  apply TrackCell.status_injective
  funext e
  change (leftCell m A.pom.property A.targetCell).status e = (rightCell m A.pom.property B.pom.property B.sourceCell).status e
  obtain ⟨a,rfl⟩ := (index m).surjective e
  rw [leftCell_raw,rightCell_raw]
  cases a with
  | left a => exact if_neg a.property
  | right a => exact (if_neg a.property).symm
  | mid i =>
    change (if A.pom.val.inTgt (A.pom.tgt i) then Status.star else Status.one) =
      (if B.pom.val.inSrc (B.pom.src (Fin.cast m.len_eq i)) then Status.star else Status.zero)
    rw [if_pos ⟨i,rfl⟩,if_pos ⟨Fin.cast m.len_eq i,rfl⟩]

variable {Y : Precubical.{u,v} Lab k}

@[simp] theorem glueMap_onLeft (p : Map (track A.pom.val) Y) (q : Map (track B.pom.val) Y)
    (seam : p.app A.targetCell = q.app B.sourceCell) {T} (c : TrackCell A.pom.val T) :
    (glueMap A B p q seam).app (leftCell (GlueMatch.ofType (A.target.trans B.source.symm)) A.pom.property c) = p.app c :=
  TrackGlue.glueMap_left _ _ _ _ _ _ _ _

@[simp] theorem glueMap_onRight (p : Map (track A.pom.val) Y) (q : Map (track B.pom.val) Y)
    (seam : p.app A.targetCell = q.app B.sourceCell) {T} (c : TrackCell B.pom.val T) :
    (glueMap A B p q seam).app (rightCell (GlueMatch.ofType (A.target.trans B.source.symm)) A.pom.property B.pom.property c) = q.app c :=
  TrackGlue.glueMap_right _ _ _ _ _ _ _ _

end CounterFreeHDA.Cubical.Arrow
