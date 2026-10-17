import Paper18.Category.GraphPicardGraphTensor
import Paper18.Category.GraphPicardCapComparison

/-! # The actual normalized graph-cap multiplication law -/
noncomputable section
set_option maxHeartbeats 2000000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj TensorProduct
universe v u w
namespace Paper18.Category.GraphPicard
attribute [local instance 2000] RightRigidCategory.rightDual
open DiagonalAlgebra
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)
  (α : D ⥤ D) [α.Braided] [α.Additive] [α.Linear ℂ] [α.IsEquivalence]

/-- The genuine graph multiplication is the actual normalized pure-pair
product, followed by the actual dual and negative-braiding maps. -/
lemma graphCap_mul (X Y : D) :
    (graphCap S α X ⊗ₘ graphCap S α Y) ≫ μ[GraphLagrangian.algebra S α] =
      Functor.LaxMonoidal.μ (graphRaw α)
          (⟨dual D X,X⟩ : LinearTensor D D) (⟨dual D Y,Y⟩ : LinearTensor D D) ≫
        ((Drinfeld.positive D).map (dualTensorIso Y X).inv ⊗ₘ
          (Drinfeld.negative D).map (α.map (β_ Y X).inv)) ≫
        graphCap S α (Y ⊗ X) := by
  change (((graphPairIso α (dual D X) X).inv ≫
      (GraphLagrangian.graphFunctor α).map (capGenerator S X)) ⊗ₘ
      ((graphPairIso α (dual D Y) Y).inv ≫
        (GraphLagrangian.graphFunctor α).map (capGenerator S Y))) ≫
    (Functor.LaxMonoidal.μ (GraphLagrangian.graphFunctor α) _ _ ≫
      (GraphLagrangian.graphFunctor α).map μ[canonicalAlgebra S]) = _
  rw [← tensorHom_comp_tensorHom_assoc, Functor.LaxMonoidal.μ_natural_assoc,
    ← Functor.map_comp, DrinfeldCoendModules.capGenerator_mul]
  simp only [Functor.map_comp, Category.assoc]
  have hm (Z : D) : (GraphLagrangian.graphFunctor α).map (capGenerator S Z) =
      (graphPairIso α (dual D Z) Z).hom ≫ graphCap S α Z := by
    rw [graphCap, mappedGraphCap, Iso.hom_inv_id_assoc]
  rw [hm, graphPairIso_naturality_assoc, graphPairIso_tensor_assoc]
  simp only [tensorHom_comp_tensorHom_assoc, Iso.inv_hom_id,
    tensorHom_id, id_whiskerRight, Category.id_comp]

/-- In the actual module-endofunctor category, the graph cap action
satisfies the actual mapped normalized product relation. -/
lemma graphCentralCap_mul (X Y : D) :
    let A := GraphLagrangian.algebra S α
    letI : MonObj A.1 := Functor.monObjObj (F := Center.forget D) A
    let H := rightCentralAction D (Mod_ D A.1)
    (centralCapHom A (graphCap S α X) ⊗ₘ centralCapHom A (graphCap S α Y)) ≫
        (λ_ (𝟙_ (ModuleAlphaInduction.End Dᴹᵒᵖ (Mod_ D A.1)))).hom =
      Functor.LaxMonoidal.μ H
          ((Drinfeld.positive D).obj (dual D X) ⊗ (Drinfeld.negative D).obj (α.obj X))
          ((Drinfeld.positive D).obj (dual D Y) ⊗ (Drinfeld.negative D).obj (α.obj Y)) ≫
        H.map (Functor.LaxMonoidal.μ (graphRaw α)
          (⟨dual D X,X⟩ : LinearTensor D D) (⟨dual D Y,Y⟩ : LinearTensor D D) ≫
          ((Drinfeld.positive D).map (dualTensorIso Y X).inv ⊗ₘ
            (Drinfeld.negative D).map (α.map (β_ Y X).inv))) ≫
        centralCapHom A (graphCap S α (Y ⊗ X)) := by
  dsimp only
  exact centralCapHom_mul _ _ _ _ _ (by
    simpa only [Category.assoc] using graphCap_mul S α X Y)

end Paper18.Category.GraphPicard
