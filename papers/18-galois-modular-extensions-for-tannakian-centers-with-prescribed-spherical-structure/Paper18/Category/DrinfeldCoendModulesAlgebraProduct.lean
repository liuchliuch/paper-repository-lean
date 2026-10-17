import Paper18.Category.DrinfeldCoendModulesProduct

/-! # The transported internal multiplication is the genuine coend product -/
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

lemma mapped_capGenerator (X : D) :
    (tensorProductFunctor (C := D)).map (capGenerator S X) =
      (capPairIso (dual D X) X).hom ≫ injection S X := by
  simp only [injection, Iso.hom_inv_id_assoc]

/-- The actual transported multiplication is precisely the negative-crossing
coend product, with canonical chosen-dual comparison and fixed generators. -/
lemma injection_mul (X Y : D) :
    (injection S X ⊗ₘ injection S Y) ≫ μ[algebra S] =
      @tensorμ D _ _ (reverseBraiding D) (dual D X) X (dual D Y) Y ≫
        ((dualTensorIso Y X).inv ⊗ₘ (β_ Y X).inv) ≫ injection S (Y ⊗ X) := by
  change (((capPairIso (dual D X) X).inv ≫
      (tensorProductFunctor (C := D)).map (capGenerator S X)) ⊗ₘ
      ((capPairIso (dual D Y) Y).inv ≫
        (tensorProductFunctor (C := D)).map (capGenerator S Y))) ≫
    (Functor.LaxMonoidal.μ (tensorProductFunctor (C := D)) _ _ ≫
      (tensorProductFunctor (C := D)).map μ[canonicalAlgebra S]) = _
  rw [← tensorHom_comp_tensorHom_assoc, Functor.LaxMonoidal.μ_natural_assoc,
    ← Functor.map_comp, capGenerator_mul]
  simp only [Functor.map_comp]
  rw [mapped_capGenerator, capPairIso_naturality_assoc, capPairIso_tensor_assoc]
  simp only [tensorHom_comp_tensorHom_assoc, Iso.inv_hom_id,
    tensorHom_id, id_whiskerRight, id_comp]

end Paper18.Category.DrinfeldCoendModules
