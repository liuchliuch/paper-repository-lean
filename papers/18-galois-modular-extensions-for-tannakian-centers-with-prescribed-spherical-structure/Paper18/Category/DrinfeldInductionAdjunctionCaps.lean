import Paper18.Category.DrinfeldInductionAdjunctionBasic

/-! # Pivotal cap identities for the actual induction augmentation -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u
namespace Paper18.Category.Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  (J : PivotalStructure C)

/-- A pivotal cap on a tensor product is the nested pair of pivotal caps,
using the actual canonical comparison of right duals. -/
lemma pivotalLeftEvaluation_tensor_nested (X Y : C) :
    (X ⊗ Y) ◁ (dualTensorIso X Y).inv ≫ J.leftEvaluation (X ⊗ Y) =
      𝟙 ((X ⊗ Y) ⊗ (Yᘁ ⊗ Xᘁ)) ⊗≫
        (X ◁ J.leftEvaluation Y) ▷ Xᘁ ⊗≫ J.leftEvaluation X := by
  rw [J.leftEvaluation_tensor]
  let jX : X ⟶ dual C (dual C X) := J.j.hom.app X
  let jY : Y ⟶ dual C (dual C Y) := J.j.hom.app Y
  change (jX ⊗ₘ jY) ▷ (dual C Y ⊗ dual C X) ≫ _ = _
  calc
    _ = 𝟙 ((X ⊗ Y) ⊗ (Yᘁ ⊗ Xᘁ)) ⊗≫
        (jX ▷ ((Y ⊗ dual C Y) ⊗ dual C X) ≫
          dual C (dual C X) ◁ (J.leftEvaluation Y ▷ dual C X)) ⊗≫
            ε_ (dual C X) (dual C (dual C X)) := by
      dsimp [tensorEvaluation, PivotalStructure.leftEvaluation, jX, jY, doubleDualFunctor]
      rw [tensorHom_def]
      monoidal
    _ = _ := by
      rw [← whisker_exchange]
      dsimp [PivotalStructure.leftEvaluation, jX, jY, doubleDualFunctor]
      monoidal

/-- The pivotal cap on the chosen right dual cancels the pivotal map on
its partner; this is dual compatibility, proved from actual pivotal coherence. -/
lemma pivotalLeftEvaluation_dual (U : C) :
    (Uᘁ ◁ J.j.hom.app U) ≫ J.leftEvaluation Uᘁ = ε_ U Uᘁ := by
  dsimp only [PivotalStructure.leftEvaluation]
  rw [J.dual_component U]
  dsimp only [dualMap, dual, doubleDualFunctor]
  rw [rightAdjointMate_comp_evaluation]
  simp [← whiskerLeft_comp_assoc]


/-- Closing a tensor label is the successive closing of its inner and
outer labels, using the actual inverse half-braiding hexagon. -/
lemma inductionAugmentationCap_tensor (Z : Center C) (A T : C) :
    (((A ⊗ T) ⊗ Z.1) ◁ (dualTensorIso A T).inv) ≫
        inductionAugmentationCap J Z (A ⊗ T) =
      𝟙 (((A ⊗ T) ⊗ Z.1) ⊗ (Tᘁ ⊗ Aᘁ)) ⊗≫
        (A ◁ inductionAugmentationCap J Z T) ▷ Aᘁ ⊗≫
          inductionAugmentationCap J Z A := by
  calc
    _ = (Z.2.β (A ⊗ T)).inv ▷ (Tᘁ ⊗ Aᘁ) ≫
        (α_ Z.1 (A ⊗ T) (Tᘁ ⊗ Aᘁ)).hom ≫
          Z.1 ◁ ((A ⊗ T) ◁ (dualTensorIso A T).inv ≫ J.leftEvaluation (A ⊗ T)) ≫
            (ρ_ Z.1).hom := by
      dsimp [inductionAugmentationCap]
      rw [whisker_exchange_assoc]
      monoidal
    _ = 𝟙 (((A ⊗ T) ⊗ Z.1) ⊗ (Tᘁ ⊗ Aᘁ)) ⊗≫
        (A ◁ (Z.2.β T).inv) ▷ (Tᘁ ⊗ Aᘁ) ⊗≫
        (((Z.2.β A).inv ▷ (T ⊗ Tᘁ)) ≫
          (Z.1 ⊗ A) ◁ J.leftEvaluation T) ▷ Aᘁ ⊗≫
        Z.1 ◁ J.leftEvaluation A ⊗≫ 𝟙 Z.1 := by
      rw [pivotalLeftEvaluation_tensor_nested, halfBraiding_inv_monoidal]
      monoidal
    _ = _ := by
      rw [← whisker_exchange]
      dsimp [inductionAugmentationCap]
      monoidal

end Paper18.Category.Drinfeld
