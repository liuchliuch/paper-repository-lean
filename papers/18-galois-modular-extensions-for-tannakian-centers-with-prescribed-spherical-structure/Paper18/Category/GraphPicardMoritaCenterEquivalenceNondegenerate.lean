import Paper18.Category.GraphPicardMoritaCenterEquivalence

/-! # Actual nondegeneracy of the graph dual's canonical center -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits MonoidalOpposite
open scoped MonoidalLeftAction
universe v u w
namespace Paper18.Category.GraphPicard
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)
  (α : D ⥤ D) [α.Braided] [α.Additive] [α.Linear ℂ] [α.IsEquivalence]
  (hD : IsNondegenerate (C := D))
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

include hD in
/-- The genuine Morita center equivalence transports actual Müger
nondegeneracy to the canonical graph dual center. This statement requires
no auxiliary braiding on the module-endofunctor category. -/
theorem graphMoritaCenter_nondegenerate : IsNondegenerate
    (C := Center (ModuleAlphaInduction.End Dᴹᵒᵖ (GraphLagrangian.ModuleOrbit S α))) := by
  have hZ := DrinfeldNoPivotal.center_nondegenerate S
  have hRev : @IsNondegenerate (Center D) _ _ (reverseBraiding (Center D)) _ _ :=
    RelativeTensor.nondegenerate_reverse_iff.mpr hZ
  letI : BraidedCategory (Center D) := reverseBraiding (Center D)
  let e := graphMoritaCenterEquivalence S α hD
  letI : e.inverse.Braided := graphMoritaCenterEquivalenceInverseReverseBraided S α hD
  exact RelativeTensor.nondegenerate_of_braided_equivalence e.inverse hRev

end Paper18.Category.GraphPicard
