import Paper18.Category.GraphPicardComparisonDefectProduct
import Paper18.Category.GraphPicardCapProduct
import Paper18.Category.GraphPicardGraphTensorFormula
import Paper18.Category.GraphPicardComparisonDefectSlide
import Paper18.Category.GraphPicardComparisonDefectTranspose

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
local instance graphDefectTensorUnderlyingMonObj : MonObj A.1 :=
  Functor.monObjObj (F := Center.forget D) A
local notation "M" => Mod_ D A.1
local notation "H" => rightCentralAction D M
local notation "F" => graphCapPositive S α
local notation "G" => graphCapNegative S α

/-- The graph pairing's genuine product has inverse monodromy on its
negative input. The sign is forced by the actual same-negative crossing. -/
lemma graphCapPairing_tensor_defect (X Y : D) :
    (F).obj (dual D (X ⊗ Y)) ◁
        (Functor.LaxMonoidal.μ G X Y ≫ (G).map (doubleBraiding X Y).inv) ≫
          graphCapPairing S α (X ⊗ Y) =
      ((F).map (dualTensorIso X Y).hom ≫
        Functor.OplaxMonoidal.δ F (dual D Y) (dual D X)) ▷
          ((G).obj X ⊗ (G).obj Y) ≫
        nestedCap (graphCapPairing S α X) (graphCapPairing S α Y) := by
  let Z := (rightCentralLift D M).obj ((Drinfeld.negative D).obj (α.obj Y))
  let a : (F).obj (dual D Y) ⊗ (F).obj (dual D X) ≅
      (F).obj (dual D (X ⊗ Y)) :=
    Functor.Monoidal.μIso F (dual D Y) (dual D X) ≪≫
      (F).mapIso (dualTensorIso X Y).symm
  have hc : (Z.2.β ((G).obj X)).inv ≫
      (Functor.LaxMonoidal.μ G Y X ≫ (G).map (β_ X Y).inv) =
        Functor.LaxMonoidal.μ G X Y ≫ (G).map (doubleBraiding X Y).inv := by
    have h := negativeMoritaCentralLift_comp_braiding D M α Y X
    change Functor.LaxMonoidal.μ G Y X ≫ (G).map (β_ Y X).hom =
      (Z.2.β ((G).obj X)).hom ≫ Functor.LaxMonoidal.μ G X Y at h
    have hh := congrArg (fun f => (Z.2.β ((G).obj X)).inv ≫ f ≫
      (G).map (β_ Y X).inv ≫ (G).map (β_ X Y).inv) h
    simpa only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id, Iso.hom_inv_id_assoc,
      Functor.map_id, Category.comp_id, Iso.inv_hom_id_assoc,
      doubleBraiding, Iso.trans_inv] using hh
  have hp := capProduct_of_ordered Z a
    (Functor.LaxMonoidal.μ G Y X ≫ (G).map (β_ X Y).inv)
    (graphCapPairing S α Y) (graphCapPairing S α X)
    (graphCapPairing S α (X ⊗ Y)) (by
      simpa only [a, Iso.trans_hom, Functor.Monoidal.μIso_hom,
        Functor.mapIso_hom, Iso.symm_hom] using graphCapPairing_ordered_product S α X Y)
  simpa only [hc, a, Iso.trans_inv, Functor.Monoidal.μIso_inv,
    Functor.mapIso_inv, Iso.symm_inv] using hp

/-- The actual raw graph comparison has precisely positive monodromy as
its tensor defect. No multiplicativity law is supplied as input. -/
lemma graphCapComparison_tensor_defect (X Y : D) :
    Functor.LaxMonoidal.μ G X Y ≫ (graphCapComparison S α).app (X ⊗ Y) =
      ((graphCapComparison S α).app X ⊗ₘ (graphCapComparison S α).app Y) ≫
        Functor.LaxMonoidal.μ F X Y ≫ (F).map (doubleBraiding X Y).hom :=
  capFamilyNatTrans_tensor_defect_of_cap_product F G (graphCapPairing S α)
    (graphCapPairing_dinaturality S α) X Y (graphCapPairing_tensor_defect S α X Y)

end Paper18.Category.GraphPicard
