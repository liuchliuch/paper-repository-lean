import Paper18.Category.GraphPicardAssociatedBasic

/-! # Actual dominance of the right central action on the graph orbit

The genuine alpha equivalence supplies actual preimages, so no dominance
certificate or property of the adjoint-unit algebra is assumed.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open MonoidalOpposite
universe v u w
namespace Paper18.Category.GraphPicard
attribute [local instance 2000] RightRigidCategory.rightDual
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)
  (α : D ⥤ D) [α.Braided] [α.Additive] [α.Linear ℂ] [α.IsEquivalence]
  (hD : IsNondegenerate (C := D))
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

/-- The actual central action is essentially surjective, since its
actual positive restriction is the proved alpha equivalence. -/
def graphRightCentralActionEssSurj :
    (rightCentralAction D (GraphLagrangian.ModuleOrbit S α)).EssSurj := by
  letI := graphPositiveOrbitActionIsEquivalence S α hD
  refine ⟨fun Y => ?_⟩
  exact ⟨(Drinfeld.positive D).obj ((graphPositiveOrbitAction S α).objPreimage Y),
    ⟨(graphPositiveOrbitAction S α).objObjPreimageIso Y⟩⟩

include hD in
/-- Every actual module endofunctor is a retract of an actual central
action value, with a genuine isomorphism providing the retract. -/
theorem graphRightCentralAction_retract_dominant
    (Y : ModuleAlphaInduction.End Dᴹᵒᵖ (GraphLagrangian.ModuleOrbit S α)) :
    ∃ Z : Center D, Nonempty (Retract Y
      ((rightCentralAction D (GraphLagrangian.ModuleOrbit S α)).obj Z)) := by
  letI := graphRightCentralActionEssSurj S α hD
  let H := rightCentralAction D (GraphLagrangian.ModuleOrbit S α)
  exact ⟨H.objPreimage Y, ⟨Retract.ofIso (H.objObjPreimageIso Y).symm⟩⟩

end Paper18.Category.GraphPicard
