import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-! # An actual inverse from a morphism of exact pairings -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {X Y X' Y' : C} [ExactPairing X Y] [ExactPairing X' Y']

/-- The inverse of the object map is the actual cup-cap contraction of
the accompanying map between its duals. -/
def pairingMapInverse (g : Y ⟶ Y') : X' ⟶ X :=
  (λ_ X').inv ≫ η_ X Y ▷ X' ≫ (α_ X Y X').hom ≫
    X ◁ (g ▷ X') ≫ X ◁ ε_ X' Y' ≫ (ρ_ X).hom

/-- Preservation of evaluation gives one inverse equation. -/
theorem pairingMap_hom_inv (f : X ⟶ X') (g : Y ⟶ Y')
    (he : (g ⊗ₘ f) ≫ ε_ X' Y' = ε_ X Y) :
    f ≫ pairingMapInverse g = 𝟙 X := by
  calc
    _ = (λ_ X).inv ≫ η_ X Y ▷ X ≫ (α_ X Y X).hom ≫
        X ◁ ((g ⊗ₘ f) ≫ ε_ X' Y') ≫ (ρ_ X).hom := by
      unfold pairingMapInverse
      rw [leftUnitor_inv_naturality_assoc f, whisker_exchange_assoc,
        associator_naturality_right_assoc]
      simp only [MonoidalCategory.tensorHom_def', whiskerLeft_comp, Category.assoc]
    _ = _ := by
      rw [he]
      rw [ExactPairing.evaluation_coevaluation_assoc]
      simp

/-- Preservation of coevaluation gives the other inverse equation. -/
theorem pairingMap_inv_hom (f : X ⟶ X') (g : Y ⟶ Y')
    (hc : η_ X Y ≫ (f ⊗ₘ g) = η_ X' Y') :
    pairingMapInverse g ≫ f = 𝟙 X' := by
  calc
    _ = (λ_ X').inv ≫ (η_ X Y ≫ (f ⊗ₘ g)) ▷ X' ≫
        (α_ X' Y' X').hom ≫ X' ◁ ε_ X' Y' ≫ (ρ_ X').hom := by
      unfold pairingMapInverse
      simp only [MonoidalCategory.tensorHom_def, comp_whiskerRight, Category.assoc]
      rw [← rightUnitor_naturality, whisker_exchange_assoc,
        whisker_exchange_assoc, ← associator_naturality_left_assoc,
        associator_naturality_middle_assoc]
    _ = _ := by
      rw [hc]
      rw [ExactPairing.evaluation_coevaluation_assoc]
      simp

/-- A genuine morphism of exact pairings has an invertible object map. -/
def pairingMapIso (f : X ⟶ X') (g : Y ⟶ Y')
    (he : (g ⊗ₘ f) ≫ ε_ X' Y' = ε_ X Y)
    (hc : η_ X Y ≫ (f ⊗ₘ g) = η_ X' Y') : X ≅ X' where
  hom := f
  inv := pairingMapInverse g
  hom_inv_id := pairingMap_hom_inv f g he
  inv_hom_id := pairingMap_inv_hom f g hc

end Paper18.Category
