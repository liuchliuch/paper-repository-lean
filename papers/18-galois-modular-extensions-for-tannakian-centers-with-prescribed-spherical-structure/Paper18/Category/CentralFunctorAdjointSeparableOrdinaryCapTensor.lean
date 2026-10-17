import Paper18.Category.CentralFunctorAdjointSeparableOrdinaryCap
import Paper18.Category.ModuleFunctorDiagonalActionPairIso

/-! # Actual cap unit and multiplication in post/precomposition coordinates -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped MonoidalLeftAction
universe v u vM uM vN uN
namespace Paper18.Category.CentralFunctorAdjointSeparable
open MonoidalLeftAction ModuleFunctor.DiagonalAction
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C]
  {M : Type uM} [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [MonoidalLeftAction C M]
  {N : Type uN} [Category.{vN} N] [Preadditive N] [Linear ℂ N]
  [MonoidalLeftAction C N]
  [∀ X : C, (actionLeft M X).Additive] [∀ X : C, (actionLeft M X).Linear ℂ]
  [∀ X : C, (actionLeft N X).Additive] [∀ X : C, (actionLeft N X).Linear ℂ]

/-- The actual pair-action unit and the actual dual-unit cap cancel. -/
lemma ordinaryCap_unit (F : Ordinary C M N) :
    (pairUnitComponent F).hom ≫
        (pairMapLeft (dualUnitIso (C := C)).inv (𝟙_ C)).app F ≫
          ordinaryCap F (𝟙_ C) = 𝟙 F := by
  apply ordinary_hom_ext
  intro m
  simp only [Functor.map_comp, NatTrans.comp_app,
    pairUnitComponent_hom_app, Category.assoc]
  change (toFunctor F).map (λₗ[C] m).inv ≫
      (λₗ[C] ((toFunctor F).obj ((𝟙_ C) ⊙ₗ m))).inv ≫
        (dualUnitIso (C := C)).inv ⊵ₗ (toFunctor F).obj ((𝟙_ C) ⊙ₗ m) ≫
          (capComponent (toFunctor F) (𝟙_ C) (𝟙_ C)ᘁ).app m = 𝟙 _
  rw [capComponent_unit]
  simp only [Iso.inv_hom_id_assoc, ← (toFunctor F).map_comp, Iso.inv_hom_id]
  exact (toFunctor F).map_id m

/-- Composition of the true post/precomposition actions multiplies the
actual cap labels in the reversed order and with the actual dual comparison.
No formal diagram identity is supplied as a premise. -/
lemma ordinaryCap_tensor (F : Ordinary C M N) (X Y : C) :
    (pairTensorComponent Xᘁ X Yᘁ Y F).hom ≫
        (pairMapLeft (dualTensorIso Y X).inv (Y ⊗ X)).app F ≫
          ordinaryCap F (Y ⊗ X) =
      (pairEnd (M := M) (N := N) Xᘁ X).map (ordinaryCap F Y) ≫ ordinaryCap F X := by
  apply ordinary_hom_ext
  intro m
  simp only [Functor.map_comp, NatTrans.comp_app,
    pairTensorComponent_hom_app, Category.assoc]
  change (Xᘁ ⊴ₗ Yᘁ ⊴ₗ (toFunctor F).map (αₗ Y X m).inv) ≫
      (αₗ Xᘁ Yᘁ ((toFunctor F).obj ((Y ⊗ X) ⊙ₗ m))).inv ≫
        (dualTensorIso Y X).inv ⊵ₗ (toFunctor F).obj ((Y ⊗ X) ⊙ₗ m) ≫
          (capComponent (toFunctor F) (Y ⊗ X) (Y ⊗ X)ᘁ).app m =
    (Xᘁ ⊴ₗ (capComponent (toFunctor F) Y Yᘁ).app (X ⊙ₗ m)) ≫
      (capComponent (toFunctor F) X Xᘁ).app m
  rw [capComponent_tensor]
  simp only [← actionHomRight_comp_assoc, ← (toFunctor F).map_comp, Iso.inv_hom_id]
  erw [(toFunctor F).map_id]
  simp only [actionHomRight_id, Category.id_comp]

end Paper18.Category.CentralFunctorAdjointSeparable
