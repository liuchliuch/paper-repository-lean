import CounterFreeHDA.EndpointColors

namespace CounterFreeHDA.Cubical.IdealDiagram
universe u v
variable {Lab : Type u} {k : ℕ} {C : FinCat.{u,v} (Cube Lab k)} {ord : C.IsOrdered}
    {image : ∀ {U V}, Step U V → C.Hom U V}

theorem run_action {S U V : Cube Lab k} {p : Word U V}
    {x : IdealDiagram C ord image S U} {y : IdealDiagram C ord image S V}
    (hr : (ideal C ord image S).Run p x y) :
    LowerSetAction.act ord x.top (wordImage C image p) ⊆ y.top := by
  intro a ha
  obtain ⟨b,hb,hab⟩ := (LowerSetAction.mem_act ord).mp ha
  exact y.lower (Face.ident V) (run_propagates hr hb) hab

end CounterFreeHDA.Cubical.IdealDiagram

namespace CounterFreeHDA.Cubical
universe u v
variable {Lab : Type u} {k : ℕ} {P : PomsetData Lab}
    (C : FinCat.{u,v} (Cube Lab k)) (ord : C.IsOrdered)
    (image : ∀ {U V}, Step U V → C.Hom U V)

/-- Inequalities between faces of the same boundary cube already follow
from that diagram's actual precubical identities and arc inequalities. -/
theorem same_cube_action {S D U V : Cube Lab k} (d : TrackCell P D)
    (z : IdealDiagram C ord image S D) {x : TrackCell P U} {y : TrackCell P V}
    (hx : TrackCell.InCube d x) (hy : TrackCell.InCube d y) (p : Word U V)
    (hr : (track P).Run p x y) :
    LowerSetAction.act ord (z.val (TrackCell.faceFrom x d hx)) (wordImage C image p) ⊆
      z.val (TrackCell.faceFrom y d hy) := by
  let α := TrackCell.faceFrom x d hx
  let β := TrackCell.faceFrom y d hy
  have hr' : (track P).Run p (d.face α) (d.face β) := by
    rw [TrackCell.faceFrom_face,TrackCell.faceFrom_face]
    exact hr
  have hz := TrackCell.run_faces d α β hr' (Y := ideal C ord image S) z
  have ha := IdealDiagram.run_action hz
  simpa only [ideal,IdealDiagram.top,IdealDiagram.restrict_val,Face.ident_comp] using ha

end CounterFreeHDA.Cubical

namespace CounterFreeHDA.Cubical.Endpoint
universe u v
variable {Lab : Type u} {k : ℕ} {L : Set (IntervalPom Lab)} {h : ℕ}
    (F : OrderedPomsetRecognizer.{u,v} (k := k) L h)
    (P : PomsetData Lab) (hP : IsIntervalPom P) (hw : P.WidthLE k)
    (hs : P.srcLen ≤ k) (ht : P.tgtLen ≤ k) {S : Cube Lab k}
    (x : IdealDiagram F.C F.order F.stepImage S (sourceCube P hs))
    (y : IdealDiagram F.C F.order F.stepImage S (targetCube P ht))

/-- The actual corner inequalities imply every prescribed-boundary path
inequality in the full characteristic face graph. -/
theorem boundary_compatible (hint : ∃ e, ¬ P.inSrc e ∧ ¬ P.inTgt e)
    (hcrit : Criterion F P hP hs ht x y hw) :
    BoundaryCompatible F.C F.order F.stepImage (track P) S (boundary P hP hs ht)
      (fun _ c => colours F P hP hs ht x y c) := by
  intro U V c d hc hd p hr
  change LowerSetAction.act F.order (colours F P hP hs ht x y c) (wordImage F.C F.stepImage p) ⊆ colours F P hP hs ht x y d
  rcases hc with hc | hc <;> rcases hd with hd | hd
  · rw [colours_left F P hP hs ht x y c hc,colours_left F P hP hs ht x y d hd]
    exact same_cube_action F.C F.order F.stepImage (iota P hP hs) x hc hd p hr
  · rw [colours_left F P hP hs ht x y c hc,colours_right F P hP hs ht x y hint d hd]
    let α := TrackCell.faceFrom c (iota P hP hs) hc
    let β := TrackCell.faceFrom d (tau P hP ht) hd
    have hr' : (track P).Run p ((iota P hP hs).face α) ((tau P hP ht).face β) := by
      rw [TrackCell.faceFrom_face,TrackCell.faceFrom_face]
      exact hr
    have hcomp := compatible_of_boundary_run P hP hs ht α β p hr'
    let A := CornerFaces.boundedArrow P hP hw hs ht α β hcomp
    have hsub : p.label.pom ⊑ₛ A.pom :=
      (lemma_3_5_compatible P hP hs ht α β hcomp p.label p.label_width).mp ⟨p,hr',⟨PomsetIso.refl _⟩⟩
    have hm : F.order.homLE (wordImage F.C F.stepImage p) (F.map A) := by
      rw [F.wordImage_eq]
      exact F.monotone (BoundedArrow.ofWord p) A hsub
    exact (LowerSetAction.act_mono_arrow F.order (x.val α) hm).trans (hcrit U V α β hcomp)
  · obtain ⟨e,heS,heT⟩ := hint
    exact False.elim (no_reverse_boundary_run P hP hs ht e heS heT c d hc hd p hr)
  · rw [colours_right F P hP hs ht x y hint c hc,colours_right F P hP hs ht x y hint d hd]
    exact same_cube_action F.C F.order F.stepImage (tau P hP ht) y hc hd p hr

end CounterFreeHDA.Cubical.Endpoint
