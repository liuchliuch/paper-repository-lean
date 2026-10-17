import Paper18.Category.RelativeCenterRigidBasic
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-! # Rigidity makes an actual relative lax half-braiding invertible -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {P : ObjectProperty C} [P.IsMonoidal]

structure RelativeLaxHalfBraiding (X : C) where
  hom : ∀ U : C, P U → (X ⊗ U ⟶ U ⊗ X)
  naturality : ∀ {U V : C} (hU : P U) (hV : P V) (f : U ⟶ V),
    X ◁ f ≫ hom V hV = hom U hU ≫ f ▷ X
  monoidal : ∀ (U V : C) (hU : P U) (hV : P V),
    hom (U ⊗ V) (ObjectProperty.prop_tensor hU hV) =
      (α_ X U V).inv ≫ hom U hU ▷ V ≫ (α_ U X V).hom ≫ U ◁ hom V hV ≫ (α_ U V X).inv
  unit : hom (𝟙_ C) (ObjectProperty.prop_unit P) = (ρ_ X).hom ≫ (λ_ X).inv

namespace RelativeLaxHalfBraiding
variable {X : C} (b : RelativeLaxHalfBraiding (P := P) X)

def inv (U : C) [HasLeftDual U] (hU : P U) (hL : P (ᘁU)) : U ⊗ X ⟶ X ⊗ U :=
  𝟙 (U ⊗ X) ⊗≫ (U ⊗ X) ◁ η_ (ᘁU) U ⊗≫
    U ◁ b.hom (ᘁU) hL ▷ U ⊗≫ ε_ (ᘁU) U ▷ (X ⊗ U) ⊗≫ 𝟙 (X ⊗ U)

lemma hom_inv_id (U : C) [HasLeftDual U] (hU : P U) (hL : P (ᘁU)) :
    b.hom U hU ≫ b.inv U hU hL = 𝟙 (X ⊗ U) := by
  calc
    _ = 𝟙 (X ⊗ U) ⊗≫
        (b.hom U hU ▷ (𝟙_ C) ≫ (U ⊗ X) ◁ η_ (ᘁU) U) ⊗≫
        U ◁ b.hom (ᘁU) hL ▷ U ⊗≫ ε_ (ᘁU) U ▷ (X ⊗ U) ⊗≫ 𝟙 (X ⊗ U) := by
      dsimp [inv]
      monoidal
    _ = 𝟙 (X ⊗ U) ⊗≫ X ◁ (U ◁ η_ (ᘁU) U) ⊗≫
        (b.hom (U ⊗ ᘁU) (ObjectProperty.prop_tensor hU hL) ≫ ε_ (ᘁU) U ▷ X) ▷ U ⊗≫ 𝟙 (X ⊗ U) := by
      rw [← whisker_exchange, b.monoidal U (ᘁU) hU hL]
      monoidal
    _ = 𝟙 (X ⊗ U) ⊗≫
        X ◁ (U ◁ η_ (ᘁU) U ⊗≫ ε_ (ᘁU) U ▷ U) ⊗≫ 𝟙 (X ⊗ U) := by
      rw [← b.naturality (ObjectProperty.prop_tensor hU hL) (ObjectProperty.prop_unit P)
        (ε_ (ᘁU) U), b.unit]
      monoidal
    _ = 𝟙 (X ⊗ U) := by
      rw [ExactPairing.coevaluation_evaluation'']
      monoidal

lemma inv_hom_id (U : C) [HasLeftDual U] (hU : P U) (hL : P (ᘁU)) :
    b.inv U hU hL ≫ b.hom U hU = 𝟙 (U ⊗ X) := by
  calc
    _ = 𝟙 (U ⊗ X) ⊗≫ (U ⊗ X) ◁ η_ (ᘁU) U ⊗≫
        U ◁ b.hom (ᘁU) hL ▷ U ⊗≫
        (ε_ (ᘁU) U ▷ (X ⊗ U) ≫ (𝟙_ C) ◁ b.hom U hU) ⊗≫ 𝟙 (U ⊗ X) := by
      dsimp [inv]
      monoidal
    _ = 𝟙 (U ⊗ X) ⊗≫
        U ◁ (X ◁ η_ (ᘁU) U ≫ b.hom ((ᘁU : C) ⊗ U) (ObjectProperty.prop_tensor hL hU)) ⊗≫
        ε_ (ᘁU) U ▷ (U ⊗ X) ⊗≫ 𝟙 (U ⊗ X) := by
      rw [← whisker_exchange, b.monoidal (ᘁU) U hL hU]
      monoidal
    _ = 𝟙 (U ⊗ X) ⊗≫
        (U ◁ η_ (ᘁU) U ⊗≫ ε_ (ᘁU) U ▷ U) ▷ X ⊗≫ 𝟙 (U ⊗ X) := by
      rw [b.naturality (ObjectProperty.prop_unit P) (ObjectProperty.prop_tensor hL hU)
        (η_ (ᘁU) U), b.unit]
      monoidal
    _ = 𝟙 (U ⊗ X) := by
      rw [ExactPairing.coevaluation_evaluation'']
      monoidal

lemma hom_isIso (U : C) [HasLeftDual U] (hU : P U) (hL : P (ᘁU)) : IsIso (b.hom U hU) :=
  ⟨⟨b.inv U hU hL, b.hom_inv_id U hU hL, b.inv_hom_id U hU hL⟩⟩

def toHalfBraiding [LeftRigidCategory C] (hD : ∀ U, P U → P (ᘁU)) : RelativeHalfBraiding P X where
  β U hU := by
    letI := b.hom_isIso U hU (hD U hU)
    exact asIso (b.hom U hU)
  monoidal := b.monoidal
  naturality := b.naturality

end RelativeLaxHalfBraiding
namespace RelativeCenter
attribute [local instance 2000] RightRigidCategory.rightDual
variable [RightRigidCategory C] (Z : RelativeCenter P)

def dualLaxHalfBraiding : RelativeLaxHalfBraiding (P := P) Z.1ᘁ where
  hom := dualHalfBraidingHom Z
  naturality := dualHalfBraidingHom_naturality Z
  monoidal := dualHalfBraidingHom_monoidal Z
  unit := dualHalfBraidingHom_unit Z

end RelativeCenter
end Paper18.Category
