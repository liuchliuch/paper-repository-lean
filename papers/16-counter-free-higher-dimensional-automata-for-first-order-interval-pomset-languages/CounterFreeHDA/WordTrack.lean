import CounterFreeHDA.StepTrack

/-! The full characteristic mapping property for every actual elementary
ST-label. Maps are constructed by the concrete characteristic gluing theorem,
not by assuming an endpoint equivalence. -/
namespace CounterFreeHDA.Cubical.Word
universe u v
variable {Lab : Type u} {k : ℕ} {U V : Cube Lab k}
open TrackGlue

/-- Every actual ST label is realised by its canonical characteristic run. -/
theorem canonicalRun (p : Word U V) :
    (track p.label.pom.val).Run p p.label.sourceCell p.label.targetCell := by
  induction p with
  | nil U =>
    change (track (Arrow.ident U).pom.val).Run (.nil U)
      (Arrow.ident U).sourceCell (Arrow.ident U).targetCell
    rw [Arrow.identity_source_target]
    exact .nil _
  | @cons U V W s p ih =>
    let A := s.label
    let B := p.label
    let m := GlueMatch.ofType (A.target.trans B.source.symm)
    let X := track (k := k) (A.comp B).pom.val
    have hleft : X.Run (.cons s (.nil V)) (leftCell m A.pom.property A.sourceCell)
        (leftCell m A.pom.property A.targetCell) :=
      (TrackGlue.leftMap m A.pom.property).map_run (Step.canonicalRun s)
    have hright : X.Run p (rightCell m A.pom.property B.pom.property B.sourceCell)
        (rightCell m A.pom.property B.pom.property B.targetCell) :=
      (TrackGlue.rightMap m A.pom.property B.pom.property).map_run ih
    have hr : X.Run p (leftCell m A.pom.property A.targetCell)
        (rightCell m A.pom.property B.pom.property B.targetCell) := by
      rw [Arrow.seamCell_eq A B]
      exact hright
    change X.Run (.cons s p) (A.comp B).sourceCell (A.comp B).targetCell
    rw [Arrow.sourceCell_comp,Arrow.targetCell_comp]
    exact (X.run_append_iff (.cons s (.nil V)) p _ _).mpr ⟨_,hleft,hr⟩

variable {Y : Precubical.{u,v} Lab k}

/-- A path determines an actual map from the characteristic HDA of its exact
computed pomset label, with both prescribed cells. -/
theorem map_of_run (p : Word U V) {x : Y.Cell U} {y : Y.Cell V} (r : Y.Run p x y) :
    ∃ a : Map (track p.label.pom.val) Y, a.app p.label.sourceCell = x ∧ a.app p.label.targetCell = y := by
  induction p with
  | nil U =>
    have hxy := (Y.run_nil_iff x y).mp r
    let a := mapFromFull (Arrow.ident U).sourceCell (Arrow.identity_full U) x
    refine ⟨a,mapFromFull_top _ _ _,?_⟩
    change a.app (Arrow.ident U).targetCell = y
    rw [← Arrow.identity_source_target]
    exact (mapFromFull_top _ _ _).trans hxy
  | @cons U V W s p ih =>
    cases s with
    | start f hl hd =>
      obtain ⟨z,hxz,hr⟩ := (Y.run_start_iff f hl hd p x y).mp r
      obtain ⟨q,hqs,hqt⟩ := ih hr
      let A := (Step.start f hl hd).label
      let B := p.label
      let a := Step.startMap f hl hd z
      have seam : a.app A.targetCell = q.app B.sourceCell :=
        (Step.startMap_target f hl hd z).trans hqs.symm
      refine ⟨Arrow.glueMap A B a q seam,?_,?_⟩
      · change (Arrow.glueMap A B a q seam).app (A.comp B).sourceCell = x
        rw [Arrow.sourceCell_comp,Arrow.glueMap_onLeft]
        exact (Step.startMap_source f hl hd z).trans hxz.symm
      · change (Arrow.glueMap A B a q seam).app (A.comp B).targetCell = y
        rw [Arrow.targetCell_comp,Arrow.glueMap_onRight]
        exact hqt
    | stop f hu hd =>
      have hr := (Y.run_stop_iff f hu hd p x y).mp r
      obtain ⟨q,hqs,hqt⟩ := ih hr
      let A := (Step.stop f hu hd).label
      let B := p.label
      let a := Step.stopMap f hu hd x
      have seam : a.app A.targetCell = q.app B.sourceCell :=
        (Step.stopMap_target f hu hd x).trans hqs.symm
      refine ⟨Arrow.glueMap A B a q seam,?_,?_⟩
      · change (Arrow.glueMap A B a q seam).app (A.comp B).sourceCell = x
        rw [Arrow.sourceCell_comp,Arrow.glueMap_onLeft]
        exact Step.stopMap_source f hu hd x
      · change (Arrow.glueMap A B a q seam).app (A.comp B).targetCell = y
        rw [Arrow.targetCell_comp,Arrow.glueMap_onRight]
        exact hqt

/-- Lemma 3.1(b) for all genuine ST labels: exact path/map equivalence,
with neither implication assumed as a premise. -/
theorem lemma_3_1_b_word (p : Word U V) (x : Y.Cell U) (y : Y.Cell V) :
    Y.Run p x y ↔ ∃ a : Map (track p.label.pom.val) Y,
      a.app p.label.sourceCell = x ∧ a.app p.label.targetCell = y := by
  constructor
  · exact map_of_run p
  · rintro ⟨a,hx,hy⟩
    have h := a.map_run p.canonicalRun
    rwa [hx,hy] at h

end CounterFreeHDA.Cubical.Word
