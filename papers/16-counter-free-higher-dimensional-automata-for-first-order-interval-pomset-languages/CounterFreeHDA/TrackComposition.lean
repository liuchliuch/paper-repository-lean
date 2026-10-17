import CounterFreeHDA.RefinementAntisymmetry

namespace CounterFreeHDA.Cubical.Arrow
universe u v
variable {Lab : Type u} {k : ℕ} {U V W : Cube Lab k}

noncomputable def leftInclusion (A : Arrow U V) (B : Arrow V W) :
    Map (track (k := k) A.pom.val) (track (k := k) (A.comp B).pom.val) :=
  TrackGlue.leftMap (GlueMatch.ofType (A.target.trans B.source.symm)) A.pom.property

noncomputable def rightInclusion (A : Arrow U V) (B : Arrow V W) :
    Map (track (k := k) B.pom.val) (track (k := k) (A.comp B).pom.val) :=
  TrackGlue.rightMap (GlueMatch.ofType (A.target.trans B.source.symm)) A.pom.property B.pom.property

@[simp] theorem leftInclusion_source (A : Arrow U V) (B : Arrow V W) :
    (leftInclusion A B).app A.sourceCell = (A.comp B).sourceCell := (sourceCell_comp A B).symm

@[simp] theorem rightInclusion_target (A : Arrow U V) (B : Arrow V W) :
    (rightInclusion A B).app B.targetCell = (A.comp B).targetCell := (targetCell_comp A B).symm

theorem inclusion_seam (A : Arrow U V) (B : Arrow V W) :
    (leftInclusion A B).app A.targetCell = (rightInclusion A B).app B.sourceCell := seamCell_eq A B

variable {Y : Precubical.{u,v} Lab k}

@[simp] theorem glueMap_source (A : Arrow U V) (B : Arrow V W)
    (p : Map (track (k := k) A.pom.val) Y) (q : Map (track (k := k) B.pom.val) Y)
    (hs : p.app A.targetCell = q.app B.sourceCell) :
    (A.glueMap B p q hs).app (A.comp B).sourceCell = p.app A.sourceCell := by
  rw [sourceCell_comp,glueMap_onLeft]

@[simp] theorem glueMap_target (A : Arrow U V) (B : Arrow V W)
    (p : Map (track (k := k) A.pom.val) Y) (q : Map (track (k := k) B.pom.val) Y)
    (hs : p.app A.targetCell = q.app B.sourceCell) :
    (A.glueMap B p q hs).app (A.comp B).targetCell = q.app B.targetCell := by
  rw [targetCell_comp,glueMap_onRight]

/-- The characteristic mapping and language theorems reflect a concrete
endpoint-preserving map back to an actual pomset subsumption. -/
theorem subsumption_of_map (A B : BoundedArrow U V)
    (m : Map (track (k := k) A.pom.val) (track (k := k) B.pom.val))
    (hs : m.app A.toArrow.sourceCell = B.toArrow.sourceCell)
    (ht : m.app A.toArrow.targetCell = B.toArrow.targetCell) : A.pom ⊑ₛ B.pom :=
  (A.toArrow.lemma_3_1_a B.toArrow A.width).mp
    ((A.toArrow.lemma_3_1_b (Y := track B.pom.val) A.width _ _).mpr ⟨m,hs,ht⟩)

end CounterFreeHDA.Cubical.Arrow

namespace CounterFreeHDA.Cubical
universe u v
variable {Lab : Type u} {k : ℕ} {U V W Z : Cube Lab k}

structure TripleMap (A : Arrow U V) (B : Arrow V W) (C : Arrow W Z)
    (Y : Precubical.{u,v} Lab k) where
  first : Map (track (k := k) A.pom.val) Y
  second : Map (track (k := k) B.pom.val) Y
  third : Map (track (k := k) C.pom.val) Y
  seam₁ : first.app A.targetCell = second.app B.sourceCell
  seam₂ : second.app B.targetCell = third.app C.sourceCell

namespace TripleMap
variable {A : Arrow U V} {B : Arrow V W} {C : Arrow W Z} {Y : Precubical.{u,v} Lab k}
    (M : TripleMap A B C Y)

noncomputable def left : Map (track (k := k) ((A.comp B).comp C).pom.val) Y :=
  (A.comp B).glueMap C (A.glueMap B M.first M.second M.seam₁) M.third
    ((A.glueMap_target B M.first M.second M.seam₁).trans M.seam₂)

noncomputable def right : Map (track (k := k) (A.comp (B.comp C)).pom.val) Y :=
  A.glueMap (B.comp C) M.first (B.glueMap C M.second M.third M.seam₂)
    (M.seam₁.trans (B.glueMap_source C M.second M.third M.seam₂).symm)

@[simp] theorem left_source : M.left.app ((A.comp B).comp C).sourceCell = M.first.app A.sourceCell := by
  unfold left
  rw [Arrow.glueMap_source,Arrow.glueMap_source]

@[simp] theorem left_target : M.left.app ((A.comp B).comp C).targetCell = M.third.app C.targetCell := by
  unfold left
  rw [Arrow.glueMap_target]

@[simp] theorem right_source : M.right.app (A.comp (B.comp C)).sourceCell = M.first.app A.sourceCell := by
  unfold right
  rw [Arrow.glueMap_source]

@[simp] theorem right_target : M.right.app (A.comp (B.comp C)).targetCell = M.third.app C.targetCell := by
  unfold right
  rw [Arrow.glueMap_target,Arrow.glueMap_target]

end TripleMap

namespace BoundedArrow

noncomputable def leftTriple (A : BoundedArrow U V) (B : BoundedArrow V W) (C : BoundedArrow W Z) :
    TripleMap A.toArrow B.toArrow C.toArrow (track (k := k) ((A.comp B).comp C).pom.val) := by
  let l := Arrow.leftInclusion (A.comp B).toArrow C.toArrow
  let r := Arrow.rightInclusion (A.comp B).toArrow C.toArrow
  let ab₁ := Arrow.leftInclusion A.toArrow B.toArrow
  let ab₂ := Arrow.rightInclusion A.toArrow B.toArrow
  exact {
    first := ab₁.comp l
    second := ab₂.comp l
    third := r
    seam₁ := congrArg l.app (Arrow.inclusion_seam A.toArrow B.toArrow)
    seam₂ := (congrArg l.app (Arrow.rightInclusion_target A.toArrow B.toArrow)).trans
      (Arrow.inclusion_seam (A.comp B).toArrow C.toArrow) }

noncomputable def rightTriple (A : BoundedArrow U V) (B : BoundedArrow V W) (C : BoundedArrow W Z) :
    TripleMap A.toArrow B.toArrow C.toArrow (track (k := k) (A.comp (B.comp C)).pom.val) := by
  let l := Arrow.leftInclusion A.toArrow (B.comp C).toArrow
  let r := Arrow.rightInclusion A.toArrow (B.comp C).toArrow
  let bc₁ := Arrow.leftInclusion B.toArrow C.toArrow
  let bc₂ := Arrow.rightInclusion B.toArrow C.toArrow
  exact {
    first := l
    second := bc₁.comp r
    third := bc₂.comp r
    seam₁ := (Arrow.inclusion_seam A.toArrow (B.comp C).toArrow).trans
      (congrArg r.app (Arrow.leftInclusion_source B.toArrow C.toArrow).symm)
    seam₂ := congrArg r.app (Arrow.inclusion_seam B.toArrow C.toArrow) }

/-- Actual interface gluing is associative up to event/order/interface
isomorphism. The proof uses both concrete characteristic gluing maps, then
finite subsumption antisymmetry; no associativity conclusion is assumed. -/
noncomputable def assocIso (A : BoundedArrow U V) (B : BoundedArrow V W) (C : BoundedArrow W Z) :
    PomsetIso ((A.comp B).comp C).pom.val (A.comp (B.comp C)).pom.val := by
  let l := leftTriple A B C
  let r := rightTriple A B C
  have h₁ : ((A.comp B).comp C).pom ⊑ₛ (A.comp (B.comp C)).pom := by
    apply Arrow.subsumption_of_map _ _ r.left
    · exact r.left_source.trans (Arrow.leftInclusion_source A.toArrow (B.comp C).toArrow)
    · exact r.left_target.trans ((congrArg (Arrow.rightInclusion A.toArrow (B.comp C).toArrow).app
        (Arrow.rightInclusion_target B.toArrow C.toArrow)).trans
          (Arrow.rightInclusion_target A.toArrow (B.comp C).toArrow))
  have h₂ : (A.comp (B.comp C)).pom ⊑ₛ ((A.comp B).comp C).pom := by
    apply Arrow.subsumption_of_map _ _ l.right
    · exact l.right_source.trans ((congrArg (Arrow.leftInclusion (A.comp B).toArrow C.toArrow).app
        (Arrow.leftInclusion_source A.toArrow B.toArrow)).trans
          (Arrow.leftInclusion_source (A.comp B).toArrow C.toArrow))
    · exact l.right_target.trans (Arrow.rightInclusion_target (A.comp B).toArrow C.toArrow)
  exact Refinement.iso_of_mutual h₁ h₂

end BoundedArrow
end CounterFreeHDA.Cubical
