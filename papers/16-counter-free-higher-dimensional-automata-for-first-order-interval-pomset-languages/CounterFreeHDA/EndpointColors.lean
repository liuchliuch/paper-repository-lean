import CounterFreeHDA.BoundaryGeometry
import CounterFreeHDA.RecognitionEquality

namespace CounterFreeHDA.Cubical.CornerFaces
universe u
variable {Lab : Type u} {k : ℕ} (P : PomsetData Lab) (hP : IsIntervalPom P)
    (hw : P.WidthLE k) (hs : P.srcLen ≤ k) (ht : P.tgtLen ≤ k) {U V : Cube Lab k}
    (α : Face U (sourceCube P hs)) (β : Face V (targetCube P ht))
    (hc : Corners.Compatible P α.status β.status)

noncomputable def boundedArrow : BoundedArrow U V where
  toArrow := arrow P hP hs ht α β hc
  width := hw.ofEmbedding (Corners.inclusion P α.status β.status hc) (fun _ _ h => h)

end CounterFreeHDA.Cubical.CornerFaces

namespace CounterFreeHDA.Cubical.Endpoint
universe u v
variable {Lab : Type u} {k : ℕ} {L : Set (IntervalPom Lab)} {h : ℕ}
    (F : OrderedPomsetRecognizer.{u,v} (k := k) L h)
    (P : PomsetData Lab) (hP : IsIntervalPom P) (hs : P.srcLen ≤ k) (ht : P.tgtLen ≤ k)
    {S : Cube Lab k}
    (x : IdealDiagram F.C F.order F.stepImage S (sourceCube P hs))
    (y : IdealDiagram F.C F.order F.stepImage S (targetCube P ht))

/-- Prescribe all faces of both actual boundary cubes. -/
def boundary (U : Cube Lab k) : Set (TrackCell P U) :=
  {c | TrackCell.InCube (iota P hP hs) c ∨ TrackCell.InCube (tau P hP ht) c}

noncomputable def colours {U : Cube Lab k} (c : TrackCell P U) : Set (F.C.Hom S U) := by
  classical
  exact if hl : TrackCell.InCube (iota P hP hs) c then
    x.val (TrackCell.faceFrom c (iota P hP hs) hl) else
    if hr : TrackCell.InCube (tau P hP ht) c then
      y.val (TrackCell.faceFrom c (tau P hP ht) hr) else ∅

theorem colours_lower {U : Cube Lab k} (c : TrackCell P U) :
    IsLowerSet F.order.homLE (colours F P hP hs ht x y c) := by
  classical
  unfold colours
  split_ifs
  · exact x.lower _
  · exact y.lower _
  · exact IsLowerSet.empty

theorem colours_left {U : Cube Lab k} (c : TrackCell P U) (hc : TrackCell.InCube (iota P hP hs) c) :
    colours F P hP hs ht x y c = x.val (TrackCell.faceFrom c (iota P hP hs) hc) := by
  classical
  exact dif_pos hc

theorem colours_right (hint : ∃ e, ¬ P.inSrc e ∧ ¬ P.inTgt e)
    {U : Cube Lab k} (c : TrackCell P U) (hc : TrackCell.InCube (tau P hP ht) c) :
    colours F P hP hs ht x y c = y.val (TrackCell.faceFrom c (tau P hP ht) hc) := by
  classical
  obtain ⟨e,heS,heT⟩ := hint
  have hn : ¬ TrackCell.InCube (iota P hP hs) c := fun hl => boundary_cubes_disjoint P hP hs ht e heS heT c hl hc
  unfold colours
  rw [dif_neg hn,dif_pos hc]

theorem colours_source_face {U : Cube Lab k} (α : Face U (sourceCube P hs)) :
    colours F P hP hs ht x y ((iota P hP hs).face α) = x.val α := by
  rw [colours_left F P hP hs ht x y _ ((TrackCell.inCube_self _).face α)]
  exact congrArg (fun f => x.val f) (TrackCell.faceFrom_of_face _ α)

theorem colours_target_face (hint : ∃ e, ¬ P.inSrc e ∧ ¬ P.inTgt e)
    {U : Cube Lab k} (β : Face U (targetCube P ht)) :
    colours F P hP hs ht x y ((tau P hP ht).face β) = y.val β := by
  rw [colours_right F P hP hs ht x y hint _ ((TrackCell.inCube_self _).face β)]
  exact congrArg (fun f => y.val f) (TrackCell.faceFrom_of_face _ β)

/-- The finite family of actual corner inequalities (13). -/
def Criterion (hw : P.WidthLE k) : Prop :=
  ∀ (U V : Cube Lab k) (α : Face U (sourceCube P hs)) (β : Face V (targetCube P ht))
    (hc : Corners.Compatible P α.status β.status),
      LowerSetAction.act F.order (x.val α) (F.map (CornerFaces.boundedArrow P hP hw hs ht α β hc)) ⊆ y.val β

end CounterFreeHDA.Cubical.Endpoint
