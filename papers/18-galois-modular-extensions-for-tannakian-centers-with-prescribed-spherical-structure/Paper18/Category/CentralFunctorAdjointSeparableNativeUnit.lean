import Paper18.Category.CentralFunctorAdjointSeparableNativeDesc
import Paper18.Category.CentralFunctorAdjointSeparableNativeNormalization
import Paper18.Category.DrinfeldCoendModulesUnit

/-! # The genuine module unit law of the native cap action -/
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

/-- The genuine diagonal algebra unit acts by the genuine native unitor. -/
lemma nativeActionMap_one (F : Ordinary C M N) :
    η[DiagonalAlgebra.canonicalAlgebra S] ⊵ₗ F ≫ nativeActionMap S T F =
      (λₗ[DeligneProduct C C] F).hom := by
  apply (cancel_epi (λₗ[DeligneProduct C C] F).inv).mp
  rw [← DrinfeldCoendModules.capGenerator_one S, comp_actionHomLeft,
    Category.assoc, capGenerator_nativeActionMap]
  dsimp only [nativeCap]
  rw [DrinfeldCoendModules.unitCapMap, nativePairIso_map_assoc,
    nativePairIso_unit_assoc]
  have hi : (pairMapRight (𝟙_ C)ᘁ (𝟙 (𝟙_ C))).app F =
      𝟙 (pairObject (𝟙_ C)ᘁ (𝟙_ C) F) := by
    apply ordinary_hom_ext
    intro m
    change (𝟙_ C)ᘁ ⊴ₗ (toFunctor F).map ((𝟙 (𝟙_ C)) ⊵ₗ m) = 𝟙 _
    simp
  erw [hi, Category.id_comp]
  rw [ordinaryCap_unit, Iso.inv_hom_id]

end Paper18.Category.CentralFunctorAdjointSeparable
