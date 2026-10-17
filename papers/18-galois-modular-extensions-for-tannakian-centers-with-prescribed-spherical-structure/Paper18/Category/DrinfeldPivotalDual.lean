import Paper18.Category.DrinfeldRigid
import Paper18.Category.RigidDoubleDual

/-! # Dual half-braidings and the canonical tensor comparisons -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u
namespace Paper18.Category.Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C]

/-- Slide the constructed dual half-braiding through its defining cap. -/
lemma dualHalfBraiding_cap_slide (Z : Center C) (U : C) :
    𝟙 ((Z.1ᘁ ⊗ U) ⊗ Z.1) ⊗≫ dualHalfBraidingHom Z U ▷ Z.1 ⊗≫
        U ◁ ε_ Z.1 Z.1ᘁ ⊗≫ 𝟙 U =
      𝟙 ((Z.1ᘁ ⊗ U) ⊗ Z.1) ⊗≫ Z.1ᘁ ◁ (Z.2.β U).inv ⊗≫
        ε_ Z.1 Z.1ᘁ ▷ U ⊗≫ 𝟙 U := by
  calc
    _ = dualHalfBraidingHom Z U ▷ Z.1 ≫ (α_ U Z.1ᘁ Z.1).hom ≫
        U ◁ ε_ Z.1 Z.1ᘁ ≫ (ρ_ U).hom := by monoidal
    _ = dualHalfBraidingCap Z U := dualHalfBraidingHom_cap Z U
    _ = _ := by dsimp [dualHalfBraidingCap]; monoidal

/-- Slide the original half-braiding through the actual cap of the crossed object. -/
lemma halfBraiding_cap_slide (Z : Center C) (U : C) :
    𝟙 (Uᘁ ⊗ (Z.1 ⊗ U)) ⊗≫ Uᘁ ◁ (Z.2.β U).hom ⊗≫
        ε_ U Uᘁ ▷ Z.1 ⊗≫ 𝟙 Z.1 =
      𝟙 (Uᘁ ⊗ (Z.1 ⊗ U)) ⊗≫ (Z.2.β Uᘁ).inv ▷ U ⊗≫
        Z.1 ◁ ε_ U Uᘁ ⊗≫ 𝟙 Z.1 := by
  calc
    _ = 𝟙 (Uᘁ ⊗ (Z.1 ⊗ U)) ⊗≫ (Z.2.β Uᘁ).inv ▷ U ⊗≫
        ((Z.2.β (Uᘁ ⊗ U)).hom ≫ ε_ U Uᘁ ▷ Z.1) ⊗≫ 𝟙 Z.1 := by
      rw [Z.2.monoidal]
      simp only [monoidalComp]
      simp
    _ = 𝟙 (Uᘁ ⊗ (Z.1 ⊗ U)) ⊗≫ (Z.2.β Uᘁ).inv ▷ U ⊗≫
        (Z.1 ◁ ε_ U Uᘁ ≫ (Z.2.β (𝟙_ C)).hom) ⊗≫ 𝟙 Z.1 := by
      rw [← Z.2.naturality]
    _ = _ := by
      rw [halfBraiding_unit]
      monoidal

/-- Transposing an actual half-braiding transposes both tensor factors. -/
lemma tensorEvaluation_halfBraiding (Z : Center C) (U : C) :
    dualHalfBraidingHom Z Uᘁ ▷ (Z.1 ⊗ U) ≫ tensorEvaluation C Z.1 U =
      (Z.1ᘁ ⊗ Uᘁ) ◁ (Z.2.β U).hom ≫ tensorEvaluation C U Z.1 := by
  calc
    _ = 𝟙 ((Z.1ᘁ ⊗ Uᘁ) ⊗ (Z.1 ⊗ U)) ⊗≫
        (𝟙 ((Z.1ᘁ ⊗ Uᘁ) ⊗ Z.1) ⊗≫ dualHalfBraidingHom Z Uᘁ ▷ Z.1 ⊗≫
          Uᘁ ◁ ε_ Z.1 Z.1ᘁ ⊗≫ 𝟙 Uᘁ) ▷ U ⊗≫ ε_ U Uᘁ ⊗≫ 𝟙 (𝟙_ C) := by
      dsimp only [tensorEvaluation]
      monoidal
    _ = 𝟙 ((Z.1ᘁ ⊗ Uᘁ) ⊗ (Z.1 ⊗ U)) ⊗≫
        Z.1ᘁ ◁ (Z.2.β Uᘁ).inv ▷ U ⊗≫
          (ε_ Z.1 Z.1ᘁ ▷ (Uᘁ ⊗ U) ≫ (𝟙_ C) ◁ ε_ U Uᘁ) ⊗≫ 𝟙 (𝟙_ C) := by
      rw [dualHalfBraiding_cap_slide]
      monoidal
    _ = 𝟙 ((Z.1ᘁ ⊗ Uᘁ) ⊗ (Z.1 ⊗ U)) ⊗≫
        Z.1ᘁ ◁ (Z.2.β Uᘁ).inv ▷ U ⊗≫
          ((Z.1ᘁ ⊗ Z.1) ◁ ε_ U Uᘁ ≫ ε_ Z.1 Z.1ᘁ ▷ (𝟙_ C)) ⊗≫ 𝟙 (𝟙_ C) := by
      rw [← whisker_exchange]
    _ = 𝟙 ((Z.1ᘁ ⊗ Uᘁ) ⊗ (Z.1 ⊗ U)) ⊗≫
        Z.1ᘁ ◁ (𝟙 (Uᘁ ⊗ (Z.1 ⊗ U)) ⊗≫ Uᘁ ◁ (Z.2.β U).hom ⊗≫
          ε_ U Uᘁ ▷ Z.1 ⊗≫ 𝟙 Z.1) ⊗≫ ε_ Z.1 Z.1ᘁ ⊗≫ 𝟙 (𝟙_ C) := by
      rw [halfBraiding_cap_slide]
      monoidal
    _ = _ := by
      dsimp only [tensorEvaluation]
      monoidal

/-- The canonical dual tensor comparison identifies the mate of a
half-braiding with the constructed half-braiding of the dual object. -/
lemma dualTensorIso_halfBraiding (Z : Center C) (U : C) :
    dualMap C (Z.2.β U).hom ≫ (dualTensorIso Z.1 U).hom =
      (dualTensorIso U Z.1).hom ≫ dualHalfBraidingHom Z Uᘁ := by
  apply pairing_hom_ext (tensorExactPairing Z.1 U)
  change (dualMap C (Z.2.β U).hom ≫ (dualTensorIso Z.1 U).hom) ▷ (Z.1 ⊗ U) ≫
    tensorEvaluation C Z.1 U =
      ((dualTensorIso U Z.1).hom ≫ dualHalfBraidingHom Z Uᘁ) ▷ (Z.1 ⊗ U) ≫
        tensorEvaluation C Z.1 U
  simp only [comp_whiskerRight, assoc]
  rw [dualTensorIso_evaluation, rightAdjointMate_comp_evaluation]
  apply (cancel_epi ((dualTensorIso U Z.1).inv ▷ (Z.1 ⊗ U))).mp
  rw [← whisker_exchange_assoc]
  simp only [← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight, id_comp]
  rw [dualTensorIso_inv_evaluation]
  simp only [Iso.inv_hom_id_assoc]
  exact (tensorEvaluation_halfBraiding Z U).symm

end Paper18.Category.Drinfeld
