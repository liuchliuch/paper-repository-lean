import Paper18.Category.DrinfeldCoendModulesFamily
import Paper18.Category.RadfordDualBraiding

/-! # Actual mixed cap interchange for annular multiplication -/
noncomputable section
set_option maxHeartbeats 2000000
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory
universe v u
namespace Paper18.Category.DrinfeldCoendModules
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]

/-- Pulling an arbitrary actual action through an ambient crossing. -/
lemma braided_action_slide (A Y M : D) (a : A ⊗ M ⟶ M) :
    (𝟙 (A ⊗ (Y ⊗ M)) ⊗≫ A ◁ (β_ Y M).hom ⊗≫ a ▷ Y ⊗≫
      (β_ Y M).inv ⊗≫ 𝟙 (Y ⊗ M)) =
    (𝟙 (A ⊗ (Y ⊗ M)) ⊗≫ (β_ Y A).inv ▷ M ⊗≫ Y ◁ a ⊗≫ 𝟙 (Y ⊗ M)) := by
  calc
    _ = 𝟙 (A ⊗ (Y ⊗ M)) ⊗≫ (β_ Y A).inv ▷ M ⊗≫
        ((β_ Y (A ⊗ M)).hom ≫ a ▷ Y) ⊗≫ (β_ Y M).inv ⊗≫ 𝟙 (Y ⊗ M) := by
      simp [monoidalComp, braiding_tensor_right_hom]
    _ = 𝟙 (A ⊗ (Y ⊗ M)) ⊗≫ (β_ Y A).inv ▷ M ⊗≫
        (Y ◁ a ≫ (β_ Y M).hom) ⊗≫ (β_ Y M).inv ⊗≫ 𝟙 (Y ⊗ M) := by
      rw [← braiding_naturality_right]
    _ = _ := by
      simp [monoidalComp]

/-- Closing an actual cap after moving the two cap strands negatively
past an arbitrary actual action equals closing that cap first. -/
lemma braided_cap_interchange (A P Y M : D) (ey : P ⊗ Y ⟶ 𝟙_ D)
    (h : Y ⊗ M ⟶ Y ⊗ M) (a : A ⊗ M ⟶ M) :
    (𝟙 ((A ⊗ (P ⊗ Y)) ⊗ M) ⊗≫ (β_ P A).inv ▷ (Y ⊗ M) ⊗≫
      P ◁ (A ◁ h) ⊗≫ P ◁ (A ◁ (β_ Y M).hom) ⊗≫
      P ◁ (a ▷ Y) ⊗≫ P ◁ (β_ Y M).inv ⊗≫ ey ▷ M ⊗≫ 𝟙 M) =
    (α_ A (P ⊗ Y) M).hom ≫
      A ◁ ((α_ P Y M).hom ≫ P ◁ h ≫ (α_ P Y M).inv ≫ ey ▷ M ≫ (λ_ M).hom) ≫ a := by
  calc
    _ = 𝟙 ((A ⊗ (P ⊗ Y)) ⊗ M) ⊗≫
        (((β_ P A).inv ▷ (Y ⊗ M)) ≫ (P ⊗ A) ◁ h) ⊗≫
        P ◁ (𝟙 (A ⊗ (Y ⊗ M)) ⊗≫ A ◁ (β_ Y M).hom ⊗≫ a ▷ Y ⊗≫
          (β_ Y M).inv ⊗≫ 𝟙 (Y ⊗ M)) ⊗≫ ey ▷ M ⊗≫ 𝟙 M := by monoidal
    _ = 𝟙 ((A ⊗ (P ⊗ Y)) ⊗ M) ⊗≫
        ((A ⊗ P) ◁ h ≫ (β_ P A).inv ▷ (Y ⊗ M)) ⊗≫
        P ◁ (𝟙 (A ⊗ (Y ⊗ M)) ⊗≫ A ◁ (β_ Y M).hom ⊗≫ a ▷ Y ⊗≫
          (β_ Y M).inv ⊗≫ 𝟙 (Y ⊗ M)) ⊗≫ ey ▷ M ⊗≫ 𝟙 M := by
      rw [← whisker_exchange]
    _ = 𝟙 ((A ⊗ (P ⊗ Y)) ⊗ M) ⊗≫ (A ⊗ P) ◁ h ⊗≫
        (β_ P A).inv ▷ (Y ⊗ M) ⊗≫
        P ◁ (𝟙 (A ⊗ (Y ⊗ M)) ⊗≫ A ◁ (β_ Y M).hom ⊗≫ a ▷ Y ⊗≫
          (β_ Y M).inv ⊗≫ 𝟙 (Y ⊗ M)) ⊗≫ ey ▷ M ⊗≫ 𝟙 M := by monoidal
    _ = 𝟙 ((A ⊗ (P ⊗ Y)) ⊗ M) ⊗≫ (A ⊗ P) ◁ h ⊗≫
        (β_ P A).inv ▷ (Y ⊗ M) ⊗≫
        P ◁ (𝟙 (A ⊗ (Y ⊗ M)) ⊗≫ (β_ Y A).inv ▷ M ⊗≫
          Y ◁ a ⊗≫ 𝟙 (Y ⊗ M)) ⊗≫ ey ▷ M ⊗≫ 𝟙 M := by
      rw [braided_action_slide]
    _ = 𝟙 ((A ⊗ (P ⊗ Y)) ⊗ M) ⊗≫ (A ⊗ P) ◁ h ⊗≫
        (β_ (P ⊗ Y) A).inv ▷ M ⊗≫ ((P ⊗ Y) ◁ a) ⊗≫ ey ▷ M ⊗≫ 𝟙 M := by
      simp only [braiding_tensor_left_inv]
      monoidal
    _ = 𝟙 ((A ⊗ (P ⊗ Y)) ⊗ M) ⊗≫ (A ⊗ P) ◁ h ⊗≫
        (β_ (P ⊗ Y) A).inv ▷ M ⊗≫
        ((P ⊗ Y) ◁ a ≫ ey ▷ M) ⊗≫ 𝟙 M := by monoidal
    _ = 𝟙 ((A ⊗ (P ⊗ Y)) ⊗ M) ⊗≫ (A ⊗ P) ◁ h ⊗≫
        (β_ (P ⊗ Y) A).inv ▷ M ⊗≫
        (ey ▷ (A ⊗ M) ≫ (𝟙_ D) ◁ a) ⊗≫ 𝟙 M := by rw [whisker_exchange]
    _ = 𝟙 ((A ⊗ (P ⊗ Y)) ⊗ M) ⊗≫ (A ⊗ P) ◁ h ⊗≫
        ((β_ (P ⊗ Y) A).inv ≫ ey ▷ A) ▷ M ⊗≫ a ⊗≫ 𝟙 M := by monoidal
    _ = 𝟙 ((A ⊗ (P ⊗ Y)) ⊗ M) ⊗≫ (A ⊗ P) ◁ h ⊗≫
        (A ◁ ey ≫ (β_ (𝟙_ D) A).inv) ▷ M ⊗≫ a ⊗≫ 𝟙 M := by
      rw [← braiding_inv_naturality_right]
    _ = _ := by
      simp only [braiding_inv_tensorUnit_left]
      monoidal

end Paper18.Category.DrinfeldCoendModules
