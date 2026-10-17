import Paper18.Category.PivotalDuality

/-! # Actual right partial traces and their tensor contraction law -/
noncomputable section
universe v u
namespace Paper18.Category
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Close the right tensor factor with actual cup and cap morphisms. -/
def rightClosure {A B X P : C} (cup : 𝟙_ C ⟶ X ⊗ P) (cap : X ⊗ P ⟶ 𝟙_ C)
    (f : A ⊗ X ⟶ B ⊗ X) : A ⟶ B :=
  (ρ_ A).inv ≫ A ◁ cup ≫ (α_ A X P).inv ≫ f ▷ P ≫
    (α_ B X P).hom ≫ B ◁ cap ≫ (ρ_ B).hom

/-- Moving a comparison of closing objects from the cup to the cap leaves
the actual contraction unchanged. No scalar or semisimple assumption is used. -/
lemma rightClosure_transport {A B X P Q : C}
    (cup : 𝟙_ C ⟶ X ⊗ P) (cap : X ⊗ Q ⟶ 𝟙_ C) (s : P ⟶ Q)
    (f : A ⊗ X ⟶ B ⊗ X) :
    rightClosure (cup ≫ X ◁ s) cap f = rightClosure cup (X ◁ s ≫ cap) f := by
  simp only [rightClosure, whiskerLeft_comp, assoc]
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    associator_naturality_right_assoc]

variable [RightRigidCategory C]
namespace PivotalStructure
variable (J : PivotalStructure C)

/-- The actual right partial pivotal trace, retaining the left tensor factor. -/
def rightPartialTrace {A B : C} (X : C) (f : A ⊗ X ⟶ B ⊗ X) : A ⟶ B :=
  rightClosure (η_ X (dual C X)) (J.leftEvaluation X) f

/-- Maps on the retained factor pass through an actual partial trace. -/
lemma rightPartialTrace_naturality {A B A' B' : C} (X : C)
    (a : A' ⟶ A) (f : A ⊗ X ⟶ B ⊗ X) (b : B ⟶ B') :
    J.rightPartialTrace X (a ▷ X ≫ f ≫ b ▷ X) =
      a ≫ J.rightPartialTrace X f ≫ b := by
  simp only [rightPartialTrace, rightClosure, comp_whiskerRight, assoc]
  rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc,
    associator_inv_naturality_left_assoc, associator_naturality_left_assoc,
    ← whisker_exchange_assoc, rightUnitor_naturality]

/-- A factor retained on the far left commutes with partial contraction. -/
lemma rightPartialTrace_whiskerLeft {A B : C} (Z X : C)
    (f : A ⊗ X ⟶ B ⊗ X) :
    J.rightPartialTrace X ((α_ Z A X).hom ≫ Z ◁ f ≫ (α_ Z B X).inv) =
      Z ◁ J.rightPartialTrace X f := by
  dsimp [rightPartialTrace, rightClosure]
  monoidal

/-- The tensor cap contracts the second factor before the first factor. -/
lemma leftEvaluation_tensor_nested (X Y : C) :
    (X ⊗ Y) ◁ (dualTensorIso X Y).inv ≫ J.leftEvaluation (X ⊗ Y) =
      (α_ X Y (dual C Y ⊗ dual C X)).hom ≫
        X ◁ ((α_ Y (dual C Y) (dual C X)).inv ≫
          J.leftEvaluation Y ▷ dual C X ≫ (λ_ (dual C X)).hom) ≫ J.leftEvaluation X := by
  rw [J.leftEvaluation_tensor]
  let jX : X ⟶ dual C (dual C X) := J.j.hom.app X
  let jY : Y ⟶ dual C (dual C Y) := J.j.hom.app Y
  calc
    _ = 𝟙 ((X ⊗ Y) ⊗ (dual C Y ⊗ dual C X)) ⊗≫
        X ◁ jY ▷ dual C Y ▷ dual C X ⊗≫
        (jX ▷ ((dual C (dual C Y) ⊗ dual C Y) ⊗ dual C X) ≫
          dual C (dual C X) ◁ (ε_ (dual C Y) (dual C (dual C Y)) ▷ dual C X)) ⊗≫
        ε_ (dual C X) (dual C (dual C X)) ⊗≫ 𝟙 (𝟙_ C) := by
      dsimp [tensorEvaluation, jX, jY, doubleDualFunctor]
      rw [tensorHom_def']
      monoidal
    _ = _ := by
      rw [← whisker_exchange]
      dsimp [leftEvaluation, jX, jY, doubleDualFunctor]
      monoidal

/-- Changing from the chosen dual of a tensor product to the tensor of the
chosen duals gives this explicit actual partial trace. -/
lemma rightPartialTrace_tensor_expand {A B : C} (X Y : C)
    (f : A ⊗ (X ⊗ Y) ⟶ B ⊗ (X ⊗ Y)) :
    J.rightPartialTrace (X ⊗ Y) f =
      rightClosure (tensorCoevaluation C X Y)
        ((α_ X Y (dual C Y ⊗ dual C X)).hom ≫
          X ◁ ((α_ Y (dual C Y) (dual C X)).inv ≫
            J.leftEvaluation Y ▷ dual C X ≫ (λ_ (dual C X)).hom) ≫
              J.leftEvaluation X) f := by
  have hc : η_ (X ⊗ Y) (dual C (X ⊗ Y)) =
      tensorCoevaluation C X Y ≫ (X ⊗ Y) ◁ (dualTensorIso X Y).inv := by
    rw [← dualTensorIso_coevaluation]
    simp only [assoc, ← whiskerLeft_comp, Iso.hom_inv_id, whiskerLeft_id, comp_id]
  rw [rightPartialTrace, hc, rightClosure_transport, J.leftEvaluation_tensor_nested]

/-- Fubini for actual right partial traces. -/
theorem rightPartialTrace_tensor {A B : C} (X Y : C)
    (f : A ⊗ (X ⊗ Y) ⟶ B ⊗ (X ⊗ Y)) :
    J.rightPartialTrace (X ⊗ Y) f =
      J.rightPartialTrace X (J.rightPartialTrace Y
        ((α_ A X Y).hom ≫ f ≫ (α_ B X Y).inv)) := by
  rw [J.rightPartialTrace_tensor_expand]
  dsimp [rightPartialTrace, rightClosure, tensorCoevaluation]
  monoidal

/-- Closing the retained factor after a partial trace gives the actual full
pivotal trace of the original endomorphism. -/
theorem rightTrace_rightPartialTrace (A X : C) (f : A ⊗ X ⟶ A ⊗ X) :
    J.rightTrace (J.rightPartialTrace X f) = J.rightTrace f := by
  have hc : η_ (A ⊗ X) (dual C (A ⊗ X)) =
      tensorCoevaluation C A X ≫ (A ⊗ X) ◁ (dualTensorIso A X).inv := by
    rw [← dualTensorIso_coevaluation]
    simp only [assoc, ← whiskerLeft_comp, Iso.hom_inv_id, whiskerLeft_id, comp_id]
  simp only [rightTrace, hc, assoc]
  rw [whisker_exchange_assoc, ← assoc, ← assoc]
  rw [J.leftEvaluation_tensor_nested]
  dsimp [rightPartialTrace, rightClosure, tensorCoevaluation]
  monoidal

end PivotalStructure
end Paper18.Category
