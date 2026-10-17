import Paper18.Category.RelativeTensorAmbient
import Mathlib.CategoryTheory.Monoidal.Action.Opposites

/-! # The ambient right action on actual internal modules

For an arbitrary algebra object, tensoring its left modules on the right
uses only the ambient associator. No braiding or commutativity is needed.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory
open scoped MonObj
universe v u
namespace Paper18.Category.InternalModule
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {A : C} [MonObj A]

open RelativeTensor

/-- The actual right unitor is linear for the left algebra action. -/
def ambientTensorUnit (M : Mod_ C A) : ambientTensor M (𝟙_ C) ≅ M where
  hom := Mod_.Hom.mk' (ρ_ M.X).hom (by
    change ((α_ A M.X (𝟙_ C)).inv ≫ γ[A,M.X] ▷ (𝟙_ C)) ≫
        (ρ_ M.X).hom = (A ◁ (ρ_ M.X).hom) ≫ γ[A,M.X]
    monoidal)
  inv := Mod_.Hom.mk' (ρ_ M.X).inv (by
    change γ[A,M.X] ≫ (ρ_ M.X).inv =
      (A ◁ (ρ_ M.X).inv) ≫ (α_ A M.X (𝟙_ C)).inv ≫
        γ[A,M.X] ▷ (𝟙_ C)
    monoidal)
  hom_inv_id := by apply Mod_.Hom.ext; exact (ρ_ M.X).hom_inv_id
  inv_hom_id := by apply Mod_.Hom.ext; exact (ρ_ M.X).inv_hom_id

/-- The native ambient right action on actual left internal modules. -/
def ambientRightAction : MonoidalRightAction C (Mod_ C A) where
  actionObj M X := ambientTensor M X
  actionHomLeft f X := ambientTensorMap f X
  actionHomRight M _ _ f := ambientTensorMapRight M f
  actionHom f g := ambientTensorMap f _ ≫ ambientTensorMapRight _ g
  actionAssocIso M X Y := (ambientTensorAssoc M X Y).symm
  actionUnitIso M := ambientTensorUnit M
  actionHom_def _ _ := rfl
  actionHomRight_id X M := by
    apply Mod_.Hom.ext
    exact whiskerLeft_id M.X X
  id_actionHomLeft X M := by
    apply Mod_.Hom.ext
    exact id_whiskerRight M.X X
  actionHom_comp f₁ f₂ g₁ g₂ := by
    apply Mod_.Hom.ext
    change (f₁.hom ≫ f₂.hom) ▷ _ ≫ (_ ◁ (g₁ ≫ g₂)) =
      (f₁.hom ▷ _ ≫ (_ ◁ g₁)) ≫ (f₂.hom ▷ _ ≫ (_ ◁ g₂))
    simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
    rw [whisker_exchange_assoc]
  actionAssocIso_hom_naturality f g h := by
    apply Mod_.Hom.ext
    change (f.hom ▷ _ ≫ (_ ◁ (g ⊗ₘ h))) ≫ (α_ _ _ _).inv =
      (α_ _ _ _).inv ≫ ((f.hom ▷ _ ≫ (_ ◁ g)) ▷ _ ≫ (_ ◁ h))
    simpa only [MonoidalCategory.tensorHom_def, comp_whiskerRight, Category.assoc] using
      associator_inv_naturality f.hom g h
  actionUnitIso_hom_naturality f := by
    apply Mod_.Hom.ext
    exact (rightUnitor_naturality f.hom).symm
  actionHomRight_whiskerRight f X M := by
    apply Mod_.Hom.ext
    change M.X ◁ (f ▷ X) =
      (α_ _ _ _).inv ≫ (M.X ◁ f) ▷ X ≫ (α_ _ _ _).hom
    monoidal
  whiskerRight_actionHomLeft := by
    intro X X' X'' f M
    apply Mod_.Hom.ext
    change M.X ◁ (X ◁ f) =
      (α_ _ _ _).inv ≫ ((M.X ⊗ X) ◁ f) ≫ (α_ _ _ _).hom
    monoidal
  actionHom_associator X Y Z M := by
    apply Mod_.Hom.ext
    change (M.X ◁ (α_ X Y Z).hom) ≫ (α_ _ _ _).inv ≫
        (α_ _ _ _).inv = (α_ _ _ _).inv ≫ (α_ _ _ _).inv ▷ Z
    monoidal
  actionHom_leftUnitor X M := by
    apply Mod_.Hom.ext
    change M.X ◁ (λ_ X).hom = (α_ _ _ _).inv ≫ (ρ_ M.X).hom ▷ X
    monoidal
  actionHom_rightUnitor X M := by
    apply Mod_.Hom.ext
    change M.X ◁ (ρ_ X).hom = (α_ _ _ _).inv ≫ (ρ_ (M.X ⊗ X)).hom
    monoidal

/-- The same native action as a left action of the monoidal opposite. -/
def ambientMonoidalOppositeLeftAction : MonoidalLeftAction Cᴹᵒᵖ (Mod_ C A) := by
  letI := ambientRightAction (A := A)
  exact MonoidalLeftAction.monoidalOppositeLeftAction C (Mod_ C A)

end Paper18.Category.InternalModule
