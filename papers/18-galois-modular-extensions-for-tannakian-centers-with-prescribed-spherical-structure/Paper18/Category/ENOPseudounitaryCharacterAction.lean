import Paper18.Category.DrinfeldInductionAdjunctionCaps

/-! # The actual fusion-character action on central invariant vectors

Closing an actual half-braiding around an invariant vector gives the
character action. Tensor multiplicativity is proved from the actual nested
cup and cap identities, with no numerical character law supplied.
-/

noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u
namespace Paper18.Category.Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  (J : PivotalStructure C)

/-- An actual central invariant vector acted on by a rigid object label. -/
def characterAction (Z : Center C) (T : C) (f : 𝟙_ C ⟶ Z.1) : 𝟙_ C ⟶ Z.1 :=
  η_ T Tᘁ ≫ (ρ_ T).inv ▷ Tᘁ ≫ inductionAugmentationComponent J Z f T

/-- The actual character action respects tensor products of its object
labels. It is the two nested cups and two nested pivotal caps. -/
lemma characterAction_tensor (Z : Center C) (A B : C) (f : 𝟙_ C ⟶ Z.1) :
    characterAction J Z (A ⊗ B) f =
      characterAction J Z A (characterAction J Z B f) := by
  have hc : η_ (A ⊗ B) (A ⊗ B)ᘁ =
      tensorCoevaluation C A B ≫ (A ⊗ B) ◁ (dualTensorIso A B).inv := by
    rw [← dualTensorIso_coevaluation]
    simp only [Category.assoc, ← whiskerLeft_comp, Iso.hom_inv_id,
      whiskerLeft_id, comp_id]
  calc
    _ = tensorCoevaluation C A B ≫
        (ρ_ (A ⊗ B)).inv ▷ (Bᘁ ⊗ Aᘁ) ≫
        ((A ⊗ B) ◁ f) ▷ (Bᘁ ⊗ Aᘁ) ≫
        (((A ⊗ B) ⊗ Z.1) ◁ (dualTensorIso A B).inv) ≫
        inductionAugmentationCap J Z (A ⊗ B) := by
      dsimp only [characterAction, inductionAugmentationComponent]
      rw [hc]
      simp only [Category.assoc]
      rw [← whisker_exchange_assoc, ← whisker_exchange_assoc]
    _ = tensorCoevaluation C A B ≫
        (ρ_ (A ⊗ B)).inv ▷ (Bᘁ ⊗ Aᘁ) ≫
        ((A ⊗ B) ◁ f) ▷ (Bᘁ ⊗ Aᘁ) ≫
        (𝟙 (((A ⊗ B) ⊗ Z.1) ⊗ (Bᘁ ⊗ Aᘁ)) ⊗≫
          (A ◁ inductionAugmentationCap J Z B) ▷ Aᘁ ⊗≫
            inductionAugmentationCap J Z A) := by
      rw [inductionAugmentationCap_tensor]
    _ = _ := by
      dsimp [characterAction, tensorCoevaluation, inductionAugmentationComponent]
      monoidal

end Paper18.Category.Drinfeld
