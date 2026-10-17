import Paper18.Category.CentralFunctorAdjointSeparableOrdinaryDesc
import Paper18.Category.CentralFunctorAdjointSeparableOrdinaryCapTensor
import Paper18.Category.DrinfeldCoendModulesUnit

/-! # The actual unit law of the cap-descended diagonal map -/
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

/-- The actual lifted unit comparison, formed from the actual native
unitors and the actual singleton comparison. -/
def diagonalUnitIso (F : Ordinary C M N) :
    F ≅ (deligneAt F).obj (𝟙_ (DeligneProduct C C)) :=
  pairUnitComponent F ≪≫ (deligneAtPairIso F (𝟙_ C) (𝟙_ C)).symm

/-- The actual diagonal algebra unit acts as the identity under the
actual lifted unit comparison. -/
lemma diagonalActionMap_unit (F : Ordinary C M N) :
    (diagonalUnitIso F).hom ≫ (deligneAt F).map η[DiagonalAlgebra.canonicalAlgebra S] ≫
        diagonalActionMap S T F = 𝟙 F := by
  rw [← DrinfeldCoendModules.capGenerator_one S, Functor.map_comp]
  simp only [diagonalUnitIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [capGenerator_diagonalActionMap]
  rw [DrinfeldCoendModules.unitCapMap, delignePairIso_map_assoc]
  simp only [Iso.inv_hom_id_assoc]
  have hi : (pairMapRight (𝟙_ C)ᘁ (𝟙 (𝟙_ C))).app F =
      𝟙 (pairObject (𝟙_ C)ᘁ (𝟙_ C) F) := by
    apply ordinary_hom_ext
    intro m
    change (𝟙_ C)ᘁ ⊴ₗ (toFunctor F).map ((𝟙 (𝟙_ C)) ⊵ₗ m) = 𝟙 _
    simp
  erw [hi, Category.id_comp]
  exact ordinaryCap_unit F

end Paper18.Category.CentralFunctorAdjointSeparable
