import Paper18.Category.GraphPicardRightCentralDominant
import Paper18.Category.GraphPicardMoritaGraphAdjoint
import Paper18.Category.GraphPicardMoritaImageModules

/-! # Genuine dominance of the actual graph-orbit central action

The actual positive central-sign action is an actual equivalence, so
every actual orbit endofunctor is the image of an actual central object.
This is a consequence of the proved graph cap and alpha equivalences.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj MonoidalLeftAction
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

/-- The actual central-lift forgetful composite has the same genuine
essential surjectivity; no target-dominance certificate is supplied. -/
def graphCentralUnderlyingEssSurj : (graphCentralUnderlying S α).EssSurj :=
  graphRightCentralActionEssSurj S α hD

end Paper18.Category.GraphPicard
