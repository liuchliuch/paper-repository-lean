import Paper18.Category.GraphPicardComparisonDefectTensor

/-! # The actual double-dual-corrected graph cap comparison -/
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
local notation "A" => GraphLagrangian.algebra S α
local instance graphDefectCorrectedUnderlyingMonObj : MonObj A.1 :=
  Functor.monObjObj (F := Center.forget D) A
local notation "M" => Mod_ D A.1
local notation "H" => rightCentralAction D M
local notation "F" => graphCapPositive S α
local notation "G" => graphCapNegative S α

/-- The actual graph cap transpose, corrected by the source's actual
Drinfeld double-dual map. No target rigid structure is required. -/
def graphCapCorrectedComparison : G ⟶ doubleDualFunctor D ⋙ F :=
  drinfeldCorrectedNatTrans (graphCapComparison S α)

@[simp] lemma graphCapCorrectedComparison_app (X : D) :
    (graphCapCorrectedComparison S α).app X =
      (graphCapComparison S α).app X ≫ (F).map (drinfeldIso X).hom := rfl

/-- The genuine graph cap product and the genuine Drinfeld tensor defect
cancel, giving the actual corrected tensor condition. -/
lemma graphCapCorrectedComparison_tensor (X Y : D) :
    Functor.LaxMonoidal.μ G X Y ≫ (graphCapCorrectedComparison S α).app (X ⊗ Y) =
      ((graphCapCorrectedComparison S α).app X ⊗ₘ
        (graphCapCorrectedComparison S α).app Y) ≫
          Functor.LaxMonoidal.μ (doubleDualFunctor D ⋙ F) X Y :=
  drinfeldCorrectedNatTrans_tensor (graphCapComparison S α) X Y
    (graphCapComparison_tensor_defect S α X Y)

end Paper18.Category.GraphPicard
