import Paper18.Category.GraphPicardComparisonDefectCrossing
import Paper18.Category.GraphPicardCapProduct
import Paper18.Category.GraphPicardGraphTensorFormula

/-! # The genuine ordered product of the actual graph pairings -/
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
local instance graphDefectUnderlyingMonObj : MonObj A.1 :=
  Functor.monObjObj (F := Center.forget D) A
local notation "M" => Mod_ D A.1
local notation "H" => rightCentralAction D M
local notation "F" => graphCapPositive S α
local notation "G" => graphCapNegative S α

/-- Applying the actual graph algebra product to two actual module caps
produces the actual central shuffle and the actual reversed dual cap.
Every tensorator and crossing comes from the constructed graph functor. -/
lemma graphCapPairing_ordered_product (X Y : D) :
    (graphCapPairing S α Y ⊗ₘ graphCapPairing S α X) ≫
        (λ_ (𝟙_ (ModuleAlphaInduction.End Dᴹᵒᵖ M))).hom =
      centralTensorShuffle ((rightCentralLift D M).obj
          ((Drinfeld.negative D).obj (α.obj Y)))
        ((F).obj (dual D Y)) ((F).obj (dual D X)) ((G).obj X) ≫
      ((Functor.LaxMonoidal.μ F (dual D Y) (dual D X) ≫ (F).map (dualTensorIso X Y).inv) ⊗ₘ
        (Functor.LaxMonoidal.μ G Y X ≫ (G).map (β_ X Y).inv)) ≫ graphCapPairing S α (X ⊗ Y) := by
  dsimp only [graphCapPairing]
  rw [← tensorHom_comp_tensorHom_assoc, graphCentralCap_mul]
  rw [graphRaw_tensor]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (rightCentralAction_mixedShuffle D M (dual D Y) (α.obj Y)
    (dual D X) (α.obj X))]
  rw [← μ_natural_assoc, ← μ_natural_assoc]
  simp only [graphCapPositive, graphCapNegative, Functor.LaxMonoidal.comp_μ,
    Functor.comp_obj, Functor.comp_map, Functor.map_comp,
    tensorHom_comp_tensorHom_assoc, Category.assoc]

end Paper18.Category.GraphPicard
