import Paper18.Category.CrossedExtensionInnerCenterConjugationCrossing

/-! # Canonical fiber transports commute with the actual line braiding -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u
namespace Paper18.Category.CrossedExtension
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]

/-- Braiding naturality cancels an actual change of the conjugating line;
all transports between equal fibers are the canonical categorical maps. -/
lemma lineBraiding_eqToHom {U V X Y Z : D} (r : U ≅ V)
    (h₁ : X = Y) (h₂ : Y = Z) (h₃ : X = Z) :
    (r.inv ⊗ₘ 𝟙 X) ≫ (β_ U X).hom ≫ eqToHom h₁ ▷ U ≫
        eqToHom h₂ ▷ U ≫ Z ◁ r.hom =
      (β_ V X).hom ≫ eqToHom h₃ ▷ V := by
  subst Y
  subst Z
  simp only [eqToHom_refl, id_whiskerRight, id_comp, comp_id, tensorHom_id]
  rw [BraidedCategory.braiding_naturality_left_assoc, ← whiskerLeft_comp,
    Iso.inv_hom_id, whiskerLeft_id, comp_id]

end Paper18.Category.CrossedExtension
