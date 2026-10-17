import Paper18.Category.GraphPicardComparisonDefectCorrected
import Paper18.Category.GraphPicardCapUnit

/-! # Genuine monoidality of the double-dual-corrected graph comparison

The actual graph algebra supplies both original unit and cap product laws.
The actual Drinfeld map cancels the derived monodromy tensor defect.
There is no pivotal choice and no rigid structure on the target.
-/
noncomputable section
set_option maxHeartbeats 2000000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits Functor.LaxMonoidal
open scoped MonObj MonoidalLeftAction
universe v u w
namespace Paper18.Category.GraphPicard
attribute [local instance 2000] RightRigidCategory.rightDual
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)
  (α : D ⥤ D) [α.Braided] [α.Additive] [α.Linear ℂ] [α.IsEquivalence]
local notation "F" => graphCapPositive S α
local notation "G" => graphCapNegative S α

/-- The actual graph algebra unit gives the corrected comparison's
actual unit law after the genuine Drinfeld unit comparison. -/
lemma graphCapCorrectedComparison_unit :
    Functor.LaxMonoidal.ε G ≫ (graphCapCorrectedComparison S α).app (𝟙_ D) =
      Functor.LaxMonoidal.ε (doubleDualFunctor D ⋙ F) :=
  drinfeldCorrectedNatTrans_unit (graphCapComparison S α) (graphCapComparison_unit S α)

/-- The actual corrected graph comparison is genuinely monoidal.
All equations come from the constructed graph cap and actual rigidity;
no unit, tensor, pivotal, or invertibility certificate is an input. -/
instance graphCapCorrectedComparisonMonoidal :
    NatTrans.IsMonoidal (graphCapCorrectedComparison S α) where
  unit := graphCapCorrectedComparison_unit S α
  tensor X Y := graphCapCorrectedComparison_tensor S α X Y

end Paper18.Category.GraphPicard
