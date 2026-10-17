import Paper18.Category.DrinfeldCoendModulesProductBasic
import Paper18.Category.DrinfeldCoendModulesProductDiagram

/-! # The actual coend multiplication formula for the transported diagonal -/
noncomputable section
set_option maxHeartbeats 2000000
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj
universe v u w
namespace Paper18.Category.DrinfeldCoendModules
attribute [local instance 2000] RightRigidCategory.rightDual
open DiagonalAlgebra
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)

/-- The actual diagonal multiplication, evaluated on its cap generators,
uses the canonical chosen-dual comparison and the negative crossing. -/
lemma capGenerator_mul (X Y : D) :
    (capGenerator S X ⊗ₘ capGenerator S Y) ≫ μ[canonicalAlgebra S] =
      (DeligneProduct.externalTensorIso (dual D X) (dual D Y) X Y).hom ≫
        capPairMap (dualTensorIso Y X).inv (β_ Y X).inv ≫ capGenerator S (Y ⊗ X) := by
  apply ((tensorProductRightAdjunction S).homEquiv _ _).symm.injective
  change (tensorProductFunctor (C := D)).map
      ((capGenerator S X ⊗ₘ capGenerator S Y) ≫ μ[canonicalAlgebra S]) ≫
        canonicalAlgebraCounit S =
    (tensorProductFunctor (C := D)).map
      ((DeligneProduct.externalTensorIso (dual D X) (dual D Y) X Y).hom ≫
        capPairMap (dualTensorIso Y X).inv (β_ Y X).inv ≫ capGenerator S (Y ⊗ X)) ≫
      canonicalAlgebraCounit S
  apply (cancel_epi (Functor.LaxMonoidal.μ (tensorProductFunctor (C := D))
    (DeligneProduct.externalObject (dual D X) X)
    (DeligneProduct.externalObject (dual D Y) Y))).mp
  rw [capGenerator_mul_counit]
  simp only [Functor.map_comp, assoc]
  rw [capGenerator_counit, capPairIso_naturality_assoc, capPairIso_tensor_assoc]
  have ht : ((dualTensorIso Y X).inv ⊗ₘ (β_ Y X).inv) ≫
      ε_ (Y ⊗ X) (dual D (Y ⊗ X)) =
    (dual D X ⊗ dual D Y) ◁ (β_ Y X).inv ≫ tensorEvaluation D Y X := by
    rw [tensorHom_def', assoc, dualTensorIso_inv_evaluation]
  rw [ht, negative_tensor_cap]
  rw [← tensorHom_comp_tensorHom_assoc]

end Paper18.Category.DrinfeldCoendModules
