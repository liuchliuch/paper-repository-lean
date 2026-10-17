import CounterFreeHDA.BoundaryInequalities

namespace CounterFreeHDA.Cubical.Endpoint
universe u v
variable {Lab : Type u} {k : ℕ} {L : Set (IntervalPom Lab)} {h : ℕ}
    (F : OrderedPomsetRecognizer.{u,v} (k := k) L h)
    (P : PomsetData Lab) (hP : IsIntervalPom P) (hw : P.WidthLE k)
    (hs : P.srcLen ≤ k) (ht : P.tgtLen ≤ k) {S : Cube Lab k}
    (x : IdealDiagram F.C F.order F.stepImage S (sourceCube P hs))
    (y : IdealDiagram F.C F.order F.stepImage S (targetCube P ht))

/-- Construct the actual map extending both entire boundary diagrams. -/
noncomputable def boundaryMap (hint : ∃ e, ¬ P.inSrc e ∧ ¬ P.inTgt e)
    (hcrit : Criterion F P hP hs ht x y hw) : Map (track P) (ideal F.C F.order F.stepImage S) :=
  extendingMap F.C F.order F.stepImage (track P) S (boundary P hP hs ht)
    (fun _ c => colours F P hP hs ht x y c) (fun _ c => colours_lower F P hP hs ht x y c)
    (boundary_compatible F P hP hw hs ht x y hint hcrit)

theorem boundaryMap_source (hint : ∃ e, ¬ P.inSrc e ∧ ¬ P.inTgt e)
    (hcrit : Criterion F P hP hs ht x y hw) :
    (boundaryMap F P hP hw hs ht x y hint hcrit).app (iota P hP hs) = x := by
  let m := boundaryMap F P hP hw hs ht x y hint hcrit
  apply (prescribed_image_iff F.C F.order F.stepImage (track P) S _ m _ x).mpr
  intro U α
  change (m.app ((iota P hP hs).face α)).top = x.val α
  have hb := extendingMap_on_boundary F.C F.order F.stepImage (track P) S (boundary P hP hs ht)
    (fun _ c => colours F P hP hs ht x y c) (fun _ c => colours_lower F P hP hs ht x y c)
    (boundary_compatible F P hP hw hs ht x y hint hcrit) ((iota P hP hs).face α)
    (Or.inl ((TrackCell.inCube_self _).face α))
  exact hb.trans (colours_source_face F P hP hs ht x y α)

theorem boundaryMap_target (hint : ∃ e, ¬ P.inSrc e ∧ ¬ P.inTgt e)
    (hcrit : Criterion F P hP hs ht x y hw) :
    (boundaryMap F P hP hw hs ht x y hint hcrit).app (tau P hP ht) = y := by
  let m := boundaryMap F P hP hw hs ht x y hint hcrit
  apply (prescribed_image_iff F.C F.order F.stepImage (track P) S _ m _ y).mpr
  intro U β
  change (m.app ((tau P hP ht).face β)).top = y.val β
  have hb := extendingMap_on_boundary F.C F.order F.stepImage (track P) S (boundary P hP hs ht)
    (fun _ c => colours F P hP hs ht x y c) (fun _ c => colours_lower F P hP hs ht x y c)
    (boundary_compatible F P hP hw hs ht x y hint hcrit) ((tau P hP ht).face β)
    (Or.inr ((TrackCell.inCube_self _).face β))
  exact hb.trans (colours_target_face F P hP hs ht x y hint β)

theorem criterion_of_path
    (hpath : y ∈ (ideal F.C F.order F.stepImage S).dPom x ⟨P,hP⟩) :
    Criterion F P hP hs ht x y hw := by
  let A : Arrow (sourceCube P hs) (targetCube P ht) := { pom := ⟨P,hP⟩,source := rfl,target := rfl }
  obtain ⟨m,hx,hy⟩ := (A.lemma_3_1_b (Y := ideal F.C F.order F.stepImage S) hw x y).mp hpath
  have hsource : A.sourceCell = iota P hP hs := TrackCell.status_injective rfl
  have htarget : A.targetCell = tau P hP ht := TrackCell.status_injective rfl
  rw [hsource] at hx
  rw [htarget] at hy
  intro U V α β hc
  let C := CornerFaces.boundedArrow P hP hw hs ht α β hc
  obtain ⟨p,hr,⟨φ⟩⟩ := corner_complete_path P hP hs ht α β hc hw
  have hm := m.map_run hr
  change (ideal F.C F.order F.stepImage S).Run p
    (m.app ((track P).face α (iota P hP hs))) (m.app ((track P).face β (tau P hP ht))) at hm
  rw [m.natural,m.natural,hx,hy] at hm
  have ha := IdealDiagram.run_action hm
  have he : wordImage F.C F.stepImage p = F.map C :=
    (F.wordImage_eq p).trans (F.map_iso (BoundedArrow.ofWord p) C φ)
  rw [he] at ha
  simpa only [ideal,IdealDiagram.top,IdealDiagram.restrict_val,Face.ident_comp] using ha

/-- **Proposition 3.6.** Actual pomset reachability between arbitrary ideal
diagrams is exactly the full family of actual corner inequalities (13). -/
theorem lemma_3_6 (hint : ∃ e, ¬ P.inSrc e ∧ ¬ P.inTgt e) :
    y ∈ (ideal F.C F.order F.stepImage S).dPom x ⟨P,hP⟩ ↔ Criterion F P hP hs ht x y hw := by
  constructor
  · exact criterion_of_path F P hP hw hs ht x y
  · intro hcrit
    let A : Arrow (sourceCube P hs) (targetCube P ht) := { pom := ⟨P,hP⟩,source := rfl,target := rfl }
    let m := boundaryMap F P hP hw hs ht x y hint hcrit
    apply (A.lemma_3_1_b (Y := ideal F.C F.order F.stepImage S) hw x y).mpr
    refine ⟨m,?_,?_⟩
    · have he : A.sourceCell = iota P hP hs := TrackCell.status_injective rfl
      exact (congrArg m.app he).trans (boundaryMap_source F P hP hw hs ht x y hint hcrit)
    · have he : A.targetCell = tau P hP ht := TrackCell.status_injective rfl
      exact (congrArg m.app he).trans (boundaryMap_target F P hP hw hs ht x y hint hcrit)

end CounterFreeHDA.Cubical.Endpoint
