import Paper18.Category.RigidDoubleDual
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-! # Right dualization of the actual braiding -/
noncomputable section
universe v u
namespace Paper18.Category
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Sliding a crossing of the two dual strands through one actual cap. -/
lemma braid_cap_slide_left (Q P X : C) (ex : Q ⊗ X ⟶ 𝟙_ C) :
    𝟙 ((Q ⊗ P) ⊗ X) ⊗≫ (β_ Q P).hom ▷ X ⊗≫ P ◁ ex ⊗≫ 𝟙 P =
      𝟙 ((Q ⊗ P) ⊗ X) ⊗≫ Q ◁ (β_ X P).inv ⊗≫ ex ▷ P ⊗≫ 𝟙 P := by
  calc
    _ = 𝟙 ((Q ⊗ P) ⊗ X) ⊗≫ Q ◁ (β_ X P).inv ⊗≫
        ((β_ (Q ⊗ X) P).hom ≫ P ◁ ex) ⊗≫ 𝟙 P := by
      simp [monoidalComp, braiding_tensor_left_hom]
    _ = 𝟙 ((Q ⊗ P) ⊗ X) ⊗≫ Q ◁ (β_ X P).inv ⊗≫
        (ex ▷ P ≫ (β_ (𝟙_ C) P).hom) ⊗≫ 𝟙 P := by
      rw [← braiding_naturality_left]
    _ = _ := by
      simp only [braiding_tensorUnit_left]
      monoidal

/-- Sliding a crossing of the two original strands through the other cap. -/
lemma braid_cap_slide_right (X P Y : C) (ey : P ⊗ Y ⟶ 𝟙_ C) :
    𝟙 (P ⊗ (X ⊗ Y)) ⊗≫ P ◁ (β_ X Y).hom ⊗≫ ey ▷ X ⊗≫ 𝟙 X =
      𝟙 (P ⊗ (X ⊗ Y)) ⊗≫ (β_ X P).inv ▷ Y ⊗≫ X ◁ ey ⊗≫ 𝟙 X := by
  calc
    _ = 𝟙 (P ⊗ (X ⊗ Y)) ⊗≫ (β_ X P).inv ▷ Y ⊗≫
        ((β_ X (P ⊗ Y)).hom ≫ ey ▷ X) ⊗≫ 𝟙 X := by
      simp [monoidalComp, braiding_tensor_right_hom]
    _ = 𝟙 (P ⊗ (X ⊗ Y)) ⊗≫ (β_ X P).inv ▷ Y ⊗≫
        (X ◁ ey ≫ (β_ X (𝟙_ C)).hom) ⊗≫ 𝟙 X := by
      rw [← braiding_naturality_right]
    _ = _ := by
      simp only [braiding_tensorUnit_right]
      monoidal

/-- Transposing a crossing of the two original strands gives the crossing
of the two dual strands, with all tensor-cap coherence included. -/
lemma tensorEval_braiding (X Y Q P : C)
    (ex : Q ⊗ X ⟶ 𝟙_ C) (ey : P ⊗ Y ⟶ 𝟙_ C) :
    (β_ Q P).hom ▷ (X ⊗ Y) ≫ tensorEval X Y Q P ex ey =
      (Q ⊗ P) ◁ (β_ X Y).hom ≫ tensorEval Y X P Q ey ex := by
  calc
    _ = 𝟙 ((Q ⊗ P) ⊗ (X ⊗ Y)) ⊗≫
        (𝟙 ((Q ⊗ P) ⊗ X) ⊗≫ (β_ Q P).hom ▷ X ⊗≫ P ◁ ex ⊗≫ 𝟙 P) ▷ Y ⊗≫
          ey ⊗≫ 𝟙 (𝟙_ C) := by
      dsimp only [tensorEval]
      monoidal
    _ = 𝟙 ((Q ⊗ P) ⊗ (X ⊗ Y)) ⊗≫
        Q ◁ (β_ X P).inv ▷ Y ⊗≫ (ex ▷ (P ⊗ Y) ≫ (𝟙_ C) ◁ ey) ⊗≫
          𝟙 (𝟙_ C) := by
      rw [braid_cap_slide_left]
      monoidal
    _ = 𝟙 ((Q ⊗ P) ⊗ (X ⊗ Y)) ⊗≫
        Q ◁ (β_ X P).inv ▷ Y ⊗≫ ((Q ⊗ X) ◁ ey ≫ ex ▷ (𝟙_ C)) ⊗≫
          𝟙 (𝟙_ C) := by rw [← whisker_exchange]
    _ = 𝟙 ((Q ⊗ P) ⊗ (X ⊗ Y)) ⊗≫
        Q ◁ (𝟙 (P ⊗ (X ⊗ Y)) ⊗≫ P ◁ (β_ X Y).hom ⊗≫ ey ▷ X ⊗≫ 𝟙 X) ⊗≫
          ex ⊗≫ 𝟙 (𝟙_ C) := by
      rw [braid_cap_slide_right]
      monoidal
    _ = _ := by
      dsimp only [tensorEval]
      monoidal

variable [RightRigidCategory C]

/-- The chosen-dual tensor comparison carries the right mate of the actual
braiding to the actual braiding of the right duals. -/
lemma dualTensorIso_braiding (X Y : C) :
    dualMap C (β_ X Y).hom ≫ (dualTensorIso X Y).hom =
      (dualTensorIso Y X).hom ≫ (β_ (dual C X) (dual C Y)).hom := by
  apply pairing_hom_ext (tensorExactPairing X Y)
  change (dualMap C (β_ X Y).hom ≫ (dualTensorIso X Y).hom) ▷ (X ⊗ Y) ≫
    tensorEvaluation C X Y =
      ((dualTensorIso Y X).hom ≫ (β_ (dual C X) (dual C Y)).hom) ▷ (X ⊗ Y) ≫
        tensorEvaluation C X Y
  simp only [comp_whiskerRight, assoc]
  rw [dualTensorIso_evaluation]
  rw [rightAdjointMate_comp_evaluation]
  apply (cancel_epi ((dualTensorIso Y X).inv ▷ (X ⊗ Y))).mp
  rw [← whisker_exchange_assoc]
  simp only [← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight, id_comp]
  rw [dualTensorIso_inv_evaluation]
  simp only [Iso.inv_hom_id_assoc]
  simpa only [← tensorEvaluation_eq] using
    (tensorEval_braiding X Y (dual C X) (dual C Y)
      (ε_ X (dual C X)) (ε_ Y (dual C Y))).symm

end Paper18.Category
