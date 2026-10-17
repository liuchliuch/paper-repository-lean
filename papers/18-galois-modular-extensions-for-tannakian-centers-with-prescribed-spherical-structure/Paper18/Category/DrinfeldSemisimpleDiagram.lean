import Paper18.Category.DrinfeldSemisimpleTrace

/-! # Actual cup and rigid-transpose diagrams for the averaging slide -/
noncomputable section
universe v u
namespace Paper18.Category.Drinfeld
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

/-- The cup component is exactly the actual rigid transpose of the
half-braiding, expressed with coherent associators. -/
lemma inductionSectionComponent_transpose (Z : Center C) (A : C) :
    inductionSectionComponent Z A =
      𝟙 Z.1 ⊗≫ Z.1 ◁ η_ A (dual C A) ⊗≫
        (Z.2.β A).hom ▷ dual C A ⊗≫ 𝟙 ((A ⊗ Z.1) ⊗ dual C A) := by
  apply (cancel_mono ((α_ A Z.1 (dual C A)).hom ≫ A ◁ (Z.2.β (dual C A)).hom)).mp
  symm
  calc
    _ = (ρ_ Z.1).inv ≫ Z.1 ◁ η_ A (dual C A) ≫
        (Z.2.β (A ⊗ dual C A)).hom ≫ (α_ A (dual C A) Z.1).hom := by
      rw [Z.2.monoidal]
      monoidal
    _ = (λ_ Z.1).inv ≫ η_ A (dual C A) ▷ Z.1 ≫
        (α_ A (dual C A) Z.1).hom := by
      rw [HalfBraiding.naturality_assoc, halfBraiding_unit]
      simp only [assoc, Iso.inv_hom_id_assoc]
    _ = _ := by
      calc
        _ = 𝟙 Z.1 ⊗≫ η_ A (dual C A) ▷ Z.1 ⊗≫
            A ◁ ((Z.2.β (dual C A)).inv ≫ (Z.2.β (dual C A)).hom) ⊗≫
              𝟙 (A ⊗ (dual C A ⊗ Z.1)) := by
          rw [Iso.inv_hom_id]
          simp only [whiskerLeft_id]
          monoidal
        _ = _ := by
          dsimp only [inductionSectionComponent]
          monoidal

end Paper18.Category.Drinfeld
