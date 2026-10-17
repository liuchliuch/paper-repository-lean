import Paper18.Category.DrinfeldRigidBasic
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-!
# Invertibility of a lax half-braiding from rigidity

The inverse is constructed using a left dual of the object being crossed.
It is verified by the two snake identities, the hexagon and naturality.
-/
noncomputable section
universe v u
namespace Paper18.Category.Drinfeld
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- A half-braiding before invertibility has been proved. -/
structure LaxHalfBraiding (X : C) where
  hom : ∀ U : C, X ⊗ U ⟶ U ⊗ X
  naturality : ∀ {U V : C} (f : U ⟶ V), (X ◁ f) ≫ hom V = hom U ≫ (f ▷ X)
  monoidal (U V : C) : hom (U ⊗ V) =
    (α_ X U V).inv ≫ (hom U ▷ V) ≫ (α_ U X V).hom ≫ (U ◁ hom V) ≫ (α_ U V X).inv
  unit : hom (𝟙_ C) = (ρ_ X).hom ≫ (λ_ X).inv

namespace LaxHalfBraiding
variable {X : C} (b : LaxHalfBraiding X)

/-- The inverse is the rigid transpose across a left dual of the crossed object. -/
def inv (U : C) [HasLeftDual U] : U ⊗ X ⟶ X ⊗ U :=
  𝟙 (U ⊗ X) ⊗≫ (U ⊗ X) ◁ η_ (ᘁU) U ⊗≫
    U ◁ b.hom (ᘁU) ▷ U ⊗≫ ε_ (ᘁU) U ▷ (X ⊗ U) ⊗≫ 𝟙 (X ⊗ U)

lemma hom_inv_id (U : C) [HasLeftDual U] : b.hom U ≫ b.inv U = 𝟙 (X ⊗ U) := by
  calc
    _ = 𝟙 (X ⊗ U) ⊗≫
        (b.hom U ▷ (𝟙_ C) ≫ (U ⊗ X) ◁ η_ (ᘁU) U) ⊗≫
        U ◁ b.hom (ᘁU) ▷ U ⊗≫ ε_ (ᘁU) U ▷ (X ⊗ U) ⊗≫ 𝟙 (X ⊗ U) := by
      dsimp [inv]
      monoidal
    _ = 𝟙 (X ⊗ U) ⊗≫ X ◁ (U ◁ η_ (ᘁU) U) ⊗≫
        (b.hom (U ⊗ ᘁU) ≫ ε_ (ᘁU) U ▷ X) ▷ U ⊗≫ 𝟙 (X ⊗ U) := by
      rw [← whisker_exchange, b.monoidal]
      monoidal
    _ = 𝟙 (X ⊗ U) ⊗≫
        X ◁ (U ◁ η_ (ᘁU) U ⊗≫ ε_ (ᘁU) U ▷ U) ⊗≫ 𝟙 (X ⊗ U) := by
      rw [← b.naturality, b.unit]
      monoidal
    _ = 𝟙 (X ⊗ U) := by
      rw [ExactPairing.coevaluation_evaluation'']
      monoidal

lemma inv_hom_id (U : C) [HasLeftDual U] : b.inv U ≫ b.hom U = 𝟙 (U ⊗ X) := by
  calc
    _ = 𝟙 (U ⊗ X) ⊗≫ (U ⊗ X) ◁ η_ (ᘁU) U ⊗≫
        U ◁ b.hom (ᘁU) ▷ U ⊗≫
        (ε_ (ᘁU) U ▷ (X ⊗ U) ≫ (𝟙_ C) ◁ b.hom U) ⊗≫ 𝟙 (U ⊗ X) := by
      dsimp [inv]
      monoidal
    _ = 𝟙 (U ⊗ X) ⊗≫
        U ◁ (X ◁ η_ (ᘁU) U ≫ b.hom ((ᘁU : C) ⊗ U)) ⊗≫
        ε_ (ᘁU) U ▷ (U ⊗ X) ⊗≫ 𝟙 (U ⊗ X) := by
      rw [← whisker_exchange, b.monoidal]
      monoidal
    _ = 𝟙 (U ⊗ X) ⊗≫
        (U ◁ η_ (ᘁU) U ⊗≫ ε_ (ᘁU) U ▷ U) ▷ X ⊗≫ 𝟙 (U ⊗ X) := by
      rw [b.naturality, b.unit]
      monoidal
    _ = 𝟙 (U ⊗ X) := by
      rw [ExactPairing.coevaluation_evaluation'']
      monoidal

instance hom_isIso (U : C) [HasLeftDual U] : IsIso (b.hom U) :=
  ⟨⟨b.inv U, b.hom_inv_id U, b.inv_hom_id U⟩⟩

/-- A lax half-braiding is an actual half-braiding when all objects have left duals. -/
def toHalfBraiding [LeftRigidCategory C] : HalfBraiding X where
  β U := asIso (b.hom U)
  monoidal := b.monoidal
  naturality := b.naturality

end LaxHalfBraiding

attribute [local instance 2000] RightRigidCategory.rightDual
variable [RightRigidCategory C] (Z : Center C)

/-- The partial transpose has all coherence of a lax half-braiding, derived
from the original central structure and the actual rigid adjunction. -/
def dualLaxHalfBraiding : LaxHalfBraiding Z.1ᘁ where
  hom := dualHalfBraidingHom Z
  naturality := dualHalfBraidingHom_naturality Z
  monoidal := dualHalfBraidingHom_monoidal Z
  unit := dualHalfBraidingHom_unit Z

end Paper18.Category.Drinfeld
