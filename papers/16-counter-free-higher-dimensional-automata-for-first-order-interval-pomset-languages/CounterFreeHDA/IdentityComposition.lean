import CounterFreeHDA.TrackComposition

namespace CounterFreeHDA.Cubical.Arrow
universe u v
variable {Lab : Type u} {k : ℕ} {U : Cube Lab k} {Y : Precubical.{u,v} Lab k}

noncomputable def identityToCell (x : Y.Cell U) : Map (track (k := k) (ident U).pom.val) Y :=
  mapFromFull (ident U).sourceCell (identity_full U) x

@[simp] theorem identityToCell_source (x : Y.Cell U) :
    (identityToCell x).app (ident U).sourceCell = x := mapFromFull_top _ _ _

@[simp] theorem identityToCell_target (x : Y.Cell U) :
    (identityToCell x).app (ident U).targetCell = x :=
  (congrArg (identityToCell x).app (identity_source_target U).symm).trans (identityToCell_source x)

end CounterFreeHDA.Cubical.Arrow

namespace CounterFreeHDA.Cubical.BoundedArrow
universe u
variable {Lab : Type u} {k : ℕ} {U V : Cube Lab k}

noncomputable def identityLeftIso (A : BoundedArrow U V) : PomsetIso ((ident U).comp A).pom.val A.pom.val := by
  let p := Arrow.identityToCell (Y := track A.pom.val) A.toArrow.sourceCell
  let q : Map (track (k := k) A.pom.val) (track A.pom.val) := {app := fun c => c,natural := fun _ _ => rfl}
  have hs : p.app (Arrow.ident U).targetCell = q.app A.toArrow.sourceCell := Arrow.identityToCell_target _
  let m := (Arrow.ident U).glueMap A.toArrow p q hs
  have h₁ : ((ident U).comp A).pom ⊑ₛ A.pom :=
    Arrow.subsumption_of_map _ _ m
      (((Arrow.ident U).glueMap_source A.toArrow p q hs).trans (Arrow.identityToCell_source _))
      ((Arrow.ident U).glueMap_target A.toArrow p q hs)
  have h₂ : A.pom ⊑ₛ ((ident U).comp A).pom := by
    apply Arrow.subsumption_of_map _ _ (Arrow.rightInclusion (Arrow.ident U) A.toArrow)
    · exact (Arrow.inclusion_seam (Arrow.ident U) A.toArrow).symm.trans
        ((congrArg (Arrow.leftInclusion (Arrow.ident U) A.toArrow).app (Arrow.identity_source_target U).symm).trans
          (Arrow.leftInclusion_source (Arrow.ident U) A.toArrow))
    · exact Arrow.rightInclusion_target (Arrow.ident U) A.toArrow
  exact Refinement.iso_of_mutual h₁ h₂

noncomputable def identityRightIso (A : BoundedArrow U V) : PomsetIso (A.comp (ident V)).pom.val A.pom.val := by
  let p : Map (track (k := k) A.pom.val) (track A.pom.val) := {app := fun c => c,natural := fun _ _ => rfl}
  let q := Arrow.identityToCell (Y := track A.pom.val) A.toArrow.targetCell
  have hs : p.app A.toArrow.targetCell = q.app (Arrow.ident V).sourceCell := (Arrow.identityToCell_source _).symm
  let m := A.toArrow.glueMap (Arrow.ident V) p q hs
  have h₁ : (A.comp (ident V)).pom ⊑ₛ A.pom :=
    Arrow.subsumption_of_map _ _ m
      (A.toArrow.glueMap_source (Arrow.ident V) p q hs)
      ((A.toArrow.glueMap_target (Arrow.ident V) p q hs).trans (Arrow.identityToCell_target _))
  have h₂ : A.pom ⊑ₛ (A.comp (ident V)).pom := by
    apply Arrow.subsumption_of_map _ _ (Arrow.leftInclusion A.toArrow (Arrow.ident V))
    · exact Arrow.leftInclusion_source A.toArrow (Arrow.ident V)
    · exact (Arrow.inclusion_seam A.toArrow (Arrow.ident V)).trans
        ((congrArg (Arrow.rightInclusion A.toArrow (Arrow.ident V)).app (Arrow.identity_source_target V)).trans
          (Arrow.rightInclusion_target A.toArrow (Arrow.ident V)))
  exact Refinement.iso_of_mutual h₁ h₂

end CounterFreeHDA.Cubical.BoundedArrow
