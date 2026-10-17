import Paper18.Category.GraphLagrangianNoPivotal
import Paper18.Category.DrinfeldCoendModulesProduct
import Paper18.Category.DrinfeldCoendModulesUnit

/-! # Actual cap generators and multiplication of the central graph algebra -/
noncomputable section
set_option maxHeartbeats 2000000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits Functor.LaxMonoidal
open scoped MonObj
universe v u w
namespace Paper18.Category.GraphPicard
attribute [local instance 2000] RightRigidCategory.rightDual
open DiagonalAlgebra DrinfeldCoendModules
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)
  (α : D ⥤ D) [α.Braided] [α.Additive] [α.Linear ℂ] [α.IsEquivalence]

/-- The graph functor's actual comparison on a genuine pure external pair. -/
def graphPairIso (X Y : D) :
    (GraphLagrangian.graphFunctor α).obj (DeligneProduct.externalObject X Y) ≅
      (Drinfeld.positive D).obj X ⊗ (Drinfeld.negative D).obj (α.obj Y) :=
  (Drinfeld.deligneFactorization D).mapIso (DeligneProduct.mapPairIso (𝟭 D) α X Y) ≪≫
    Drinfeld.deligneFactorizationPairIso X (α.obj Y)

/-- The actual mapped cap generator before normalization of its pure pair. -/
def mappedGraphCap (X : D) :
    (GraphLagrangian.graphFunctor α).obj (DeligneProduct.externalObject (dual D X) X) ⟶
      GraphLagrangian.algebra S α :=
  (GraphLagrangian.graphFunctor α).map (capGenerator S X)

/-- The graph cap is a genuine morphism in the actual Drinfeld center. -/
def graphCap (X : D) :
    (Drinfeld.positive D).obj (dual D X) ⊗ (Drinfeld.negative D).obj (α.obj X) ⟶
      GraphLagrangian.algebra S α :=
  (graphPairIso α (dual D X) X).inv ≫ mappedGraphCap S α X

/-- The actual graph multiplication on the actual cap generators,
including its genuine tensorator and chosen dual comparison. -/
lemma mappedGraphCap_mul (X Y : D) :
    (mappedGraphCap S α X ⊗ₘ mappedGraphCap S α Y) ≫ μ[GraphLagrangian.algebra S α] =
      Functor.LaxMonoidal.μ (GraphLagrangian.graphFunctor α)
          (DeligneProduct.externalObject (dual D X) X)
          (DeligneProduct.externalObject (dual D Y) Y) ≫
        (GraphLagrangian.graphFunctor α).map
          ((DeligneProduct.externalTensorIso (dual D X) (dual D Y) X Y).hom ≫
            capPairMap (dualTensorIso Y X).inv (β_ Y X).inv) ≫
          mappedGraphCap S α (Y ⊗ X) := by
  change ((GraphLagrangian.graphFunctor α).map (capGenerator S X) ⊗ₘ
      (GraphLagrangian.graphFunctor α).map (capGenerator S Y)) ≫
      (Functor.LaxMonoidal.μ (GraphLagrangian.graphFunctor α) _ _ ≫
        (GraphLagrangian.graphFunctor α).map μ[canonicalAlgebra S]) = _
  rw [μ_natural_assoc, ← Functor.map_comp, capGenerator_mul]
  simp only [Functor.map_comp, Category.assoc, mappedGraphCap]

/-- The actual unit is the actual mapped unit-cap generator. -/
lemma mappedGraphCap_one :
    Functor.LaxMonoidal.ε (GraphLagrangian.graphFunctor α) ≫
        (GraphLagrangian.graphFunctor α).map (unitCapMap (D := D)) ≫
        mappedGraphCap S α (𝟙_ D) = η[GraphLagrangian.algebra S α] := by
  change _ = Functor.LaxMonoidal.ε (GraphLagrangian.graphFunctor α) ≫
    (GraphLagrangian.graphFunctor α).map η[canonicalAlgebra S]
  dsimp only [mappedGraphCap]
  rw [← Functor.map_comp, capGenerator_one]

/-- The graph functor preserves the actual diagonal cap coend because its
right adjoint is constructed from the actual finite simple skeleton. -/
def graphFunctor_preservesCoend :
    PreservesColimit (multispanIndexCoend (capDiagram (D := D))).multispan
      (GraphLagrangian.graphFunctor α) := by
  letI := DeligneProduct.hasKernels S S
  letI := (semisimpleRightAdjunction (DeligneProduct.skeleton S S)
    (GraphLagrangian.graphFunctor α)).isLeftAdjoint
  infer_instance

/-- The actual mapped graph caps determine all actual maps out of the
actual graph algebra. -/
lemma mappedGraphCap_hom_ext {W : Center D}
    {f g : GraphLagrangian.algebra S α ⟶ W}
    (h : ∀ X : D, mappedGraphCap S α X ≫ f = mappedGraphCap S α X ≫ g) : f = g := by
  letI := graphFunctor_preservesCoend S α
  exact capGenerator_hom_ext S (GraphLagrangian.graphFunctor α) h

end Paper18.Category.GraphPicard
