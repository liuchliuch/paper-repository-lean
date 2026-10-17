import Paper18.Category.CentralFunctorAdjointSeparableNativeDesc
import Paper18.Category.DrinfeldCoendModulesProduct

/-! # Actual tensor-cap coordinates of the native diagonal map

The associator naturality of the constructed native action identifies
the two successive cap coordinates of the descended map. This is the
right-hand side of the algebra-module associativity equation.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonoidalLeftAction MonObj
universe v u vM uM vN uN w wM
namespace Paper18.Category.CentralFunctorAdjointSeparable
open MonoidalLeftAction ModuleFunctor.DiagonalAction
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {M : Type uM} [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [HasFiniteBiproducts M] [MonoidalLeftAction C M]
  {κ : Type wM} [Fintype κ] (T : FiniteSemisimpleSkeleton M κ)
  {N : Type uN} [Category.{vN} N] [Preadditive N] [Linear ℂ N]
  [HasFiniteBiproducts N] [MonoidalLeftAction C N]
  [∀ X Y : N, FiniteDimensional ℂ (X ⟶ Y)]
  [∀ X : C, (actionLeft M X).Additive] [∀ X : C, (actionLeft M X).Linear ℂ]
  [∀ X : C, (actionLeft N X).Additive] [∀ X : C, (actionLeft N X).Linear ℂ]
  [∀ m : M, (actionRight C m).Additive] [∀ m : M, (actionRight C m).Linear ℂ]
  [∀ n : N, (actionRight C n).Additive] [∀ n : N, (actionRight C n).Linear ℂ]

/-- Actual associator naturality and the actual generator equations
reduce a double diagonal coordinate to successive native caps. -/
lemma nativeActionMap_capTensor (F : Ordinary C M N) (X Y : C) :
    (DiagonalAlgebra.capGenerator S X ⊗ₘ DiagonalAlgebra.capGenerator S Y) ⊵ₗ F ≫
        (αₗ (DiagonalAlgebra.canonicalAlgebra S) (DiagonalAlgebra.canonicalAlgebra S) F).hom ≫
        DiagonalAlgebra.canonicalAlgebra S ⊴ₗ nativeActionMap S T F ≫
        nativeActionMap S T F =
      (αₗ (DeligneProduct.externalObject Xᘁ X) (DeligneProduct.externalObject Yᘁ Y) F).hom ≫
        DeligneProduct.externalObject Xᘁ X ⊴ₗ nativeCap F Y ≫ nativeCap F X := by
  have hn := actionAssocIso_hom_naturality
    (DiagonalAlgebra.capGenerator S X) (DiagonalAlgebra.capGenerator S Y) (𝟙 F)
  simp only [actionHom_def, actionHomRight_id, Category.comp_id] at hn
  rw [reassoc_of% hn]
  rw [← actionHomRight_comp_assoc, capGenerator_nativeActionMap]
  rw [← action_exchange_assoc, capGenerator_nativeActionMap]

/-- The genuine diagonal multiplication has its actual negative-crossing
cap coordinate under the genuine native action. -/
lemma nativeActionMap_capTensor_mul (F : Ordinary C M N) (X Y : C) :
    (DiagonalAlgebra.capGenerator S X ⊗ₘ DiagonalAlgebra.capGenerator S Y) ⊵ₗ F ≫
        μ[DiagonalAlgebra.canonicalAlgebra S] ⊵ₗ F ≫ nativeActionMap S T F =
      (DeligneProduct.externalTensorIso Xᘁ Yᘁ X Y).hom ⊵ₗ F ≫
        DiagonalAlgebra.capPairMap (dualTensorIso Y X).inv (β_ Y X).inv ⊵ₗ F ≫
          nativeCap F (Y ⊗ X) := by
  rw [← comp_actionHomLeft_assoc, DrinfeldCoendModules.capGenerator_mul]
  simp only [comp_actionHomLeft, Category.assoc]
  rw [capGenerator_nativeActionMap]

/-- The actual preserved double coend detects the module multiplication
law exactly on the genuine rigid cap coordinates. -/
theorem nativeActionMap_mul_iff (F : Ordinary C M N) :
    (μ[DiagonalAlgebra.canonicalAlgebra S] ⊵ₗ F ≫ nativeActionMap S T F =
      (αₗ (DiagonalAlgebra.canonicalAlgebra S) (DiagonalAlgebra.canonicalAlgebra S) F).hom ≫
        DiagonalAlgebra.canonicalAlgebra S ⊴ₗ nativeActionMap S T F ≫
        nativeActionMap S T F) ↔
    ∀ X Y : C,
      (DeligneProduct.externalTensorIso Xᘁ Yᘁ X Y).hom ⊵ₗ F ≫
          DiagonalAlgebra.capPairMap (dualTensorIso Y X).inv (β_ Y X).inv ⊵ₗ F ≫
            nativeCap F (Y ⊗ X) =
        (αₗ (DeligneProduct.externalObject Xᘁ X) (DeligneProduct.externalObject Yᘁ Y) F).hom ≫
          DeligneProduct.externalObject Xᘁ X ⊴ₗ nativeCap F Y ≫ nativeCap F X := by
  constructor
  · intro h X Y
    have hh := congrArg (fun k =>
      (DiagonalAlgebra.capGenerator S X ⊗ₘ DiagonalAlgebra.capGenerator S Y) ⊵ₗ F ≫ k) h
    dsimp only at hh
    rw [nativeActionMap_capTensor_mul, nativeActionMap_capTensor] at hh
    exact hh
  · intro h
    let A := actionRight (DeligneProduct C C) F
    apply ordinaryFunctor_capTensor_hom_ext S T A
    intro X Y
    change (DiagonalAlgebra.capGenerator S X ⊗ₘ DiagonalAlgebra.capGenerator S Y) ⊵ₗ F ≫
        μ[DiagonalAlgebra.canonicalAlgebra S] ⊵ₗ F ≫ nativeActionMap S T F =
      (DiagonalAlgebra.capGenerator S X ⊗ₘ DiagonalAlgebra.capGenerator S Y) ⊵ₗ F ≫
        (αₗ (DiagonalAlgebra.canonicalAlgebra S) (DiagonalAlgebra.canonicalAlgebra S) F).hom ≫
        DiagonalAlgebra.canonicalAlgebra S ⊴ₗ nativeActionMap S T F ≫
        nativeActionMap S T F
    rw [nativeActionMap_capTensor_mul, nativeActionMap_capTensor]
    exact h X Y

end Paper18.Category.CentralFunctorAdjointSeparable
