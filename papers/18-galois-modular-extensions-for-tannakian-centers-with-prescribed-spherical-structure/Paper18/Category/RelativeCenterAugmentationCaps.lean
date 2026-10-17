import Paper18.Category.RelativeCenterAveragingBasic
import Paper18.Category.RelativeCenterRigidBasic

/-! # Actual dinaturality and tensor contraction of relative pivotal caps -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u
namespace Paper18.Category.RelativeCenter
open Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  {P : ObjectProperty C} [P.IsMonoidal] (J : PivotalStructure C)

def augmentationComponent {X : C} (Z : RelativeCenter P) (f : X ⟶ Z.1) (T : C) (hT : P T) :
    (T ⊗ X) ⊗ dual C T ⟶ Z.1 :=
  (T ◁ f) ▷ dual C T ≫ augmentationCap J Z T hT

/-- The actual cap family is dinatural in its indexing object. -/
lemma augmentationCap_dinatural (Z : RelativeCenter P) {T U : C} (hT : P T) (hU : P U) (f : T ⟶ U) :
    ((T ⊗ Z.1) ◁ rightAdjointMate f) ≫ augmentationCap J Z T hT =
      ((f ▷ Z.1) ▷ Uᘁ) ≫ augmentationCap J Z U hU := by
  calc
    _ = 𝟙 ((T ⊗ Z.1) ⊗ Uᘁ) ⊗≫
        (Z.2.β T hT).inv ▷ Uᘁ ⊗≫ Z.1 ◁ ((T ◁ rightAdjointMate f) ≫
          J.leftEvaluation T) ⊗≫ 𝟙 Z.1 := by
      dsimp [augmentationCap]
      rw [whisker_exchange_assoc]
      monoidal
    _ = 𝟙 ((T ⊗ Z.1) ⊗ Uᘁ) ⊗≫
        (Z.2.β T hT).inv ▷ Uᘁ ⊗≫ Z.1 ◁ ((f ▷ Uᘁ) ≫
          J.leftEvaluation U) ⊗≫ 𝟙 Z.1 := by
      rw [← pivotalLeftEvaluation_naturality J f]
    _ = 𝟙 ((T ⊗ Z.1) ⊗ Uᘁ) ⊗≫
        ((Z.2.β T hT).inv ≫ Z.1 ◁ f) ▷ Uᘁ ⊗≫
          Z.1 ◁ J.leftEvaluation U ⊗≫ 𝟙 Z.1 := by monoidal
    _ = _ := by
      rw [← halfBraiding_inv_naturality Z.2 hT hU f]
      dsimp [augmentationCap]
      monoidal

/-- The actual augmentation components satisfy exactly the induction
coend's dinaturality equation. -/
lemma augmentationComponent_dinatural {X : C} (Z : RelativeCenter P) (f : X ⟶ Z.1)
    {T U : C} (hT : P T) (hU : P U) (g : T ⟶ U) :
    ((T ⊗ X) ◁ rightAdjointMate g) ≫ augmentationComponent J Z f T hT =
      ((g ▷ X) ▷ Uᘁ) ≫ augmentationComponent J Z f U hU := by
  unfold augmentationComponent
  rw [whisker_exchange_assoc]
  rw [augmentationCap_dinatural J Z hT hU g]
  rw [← comp_whiskerRight_assoc, whisker_exchange, comp_whiskerRight_assoc]

/-- Closing a tensor label is the successive closing of its inner and
outer labels, using the actual inverse half-braiding hexagon. -/
lemma augmentationCap_tensor (Z : RelativeCenter P) (A T : C) (hA : P A) (hT : P T) :
    (((A ⊗ T) ⊗ Z.1) ◁ (dualTensorIso A T).inv) ≫
        augmentationCap J Z (A ⊗ T) (ObjectProperty.prop_tensor hA hT) =
      𝟙 (((A ⊗ T) ⊗ Z.1) ⊗ (Tᘁ ⊗ Aᘁ)) ⊗≫
        (A ◁ augmentationCap J Z T hT) ▷ Aᘁ ⊗≫
          augmentationCap J Z A hA := by
  calc
    _ = (Z.2.β (A ⊗ T) (ObjectProperty.prop_tensor hA hT)).inv ▷ (Tᘁ ⊗ Aᘁ) ≫
        (α_ Z.1 (A ⊗ T) (Tᘁ ⊗ Aᘁ)).hom ≫
          Z.1 ◁ ((A ⊗ T) ◁ (dualTensorIso A T).inv ≫ J.leftEvaluation (A ⊗ T)) ≫
            (ρ_ Z.1).hom := by
      dsimp [augmentationCap]
      rw [whisker_exchange_assoc]
      monoidal
    _ = 𝟙 (((A ⊗ T) ⊗ Z.1) ⊗ (Tᘁ ⊗ Aᘁ)) ⊗≫
        (A ◁ (Z.2.β T hT).inv) ▷ (Tᘁ ⊗ Aᘁ) ⊗≫
        (((Z.2.β A hA).inv ▷ (T ⊗ Tᘁ)) ≫
          (Z.1 ⊗ A) ◁ J.leftEvaluation T) ▷ Aᘁ ⊗≫
        Z.1 ◁ J.leftEvaluation A ⊗≫ 𝟙 Z.1 := by
      rw [pivotalLeftEvaluation_tensor_nested, halfBraiding_inv_monoidal Z.2 A T hA hT]
      monoidal
    _ = _ := by
      rw [← whisker_exchange]
      dsimp [augmentationCap]
      monoidal

/-- Naturality at the actual evaluation identifies the bent half-braiding
with the inverse half-braiding at the dual. -/
lemma halfBraiding_evaluation_mate (Z : RelativeCenter P) (U : C) (hU : P U) (hD : P Uᘁ) :
    (tensorLeftHomEquiv (Z.1 ⊗ U) U Uᘁ Z.1).symm (Z.2.β U hU).hom =
      (α_ Uᘁ Z.1 U).inv ≫ (Z.2.β Uᘁ hD).inv ▷ U ≫
        (α_ Z.1 Uᘁ U).hom ≫ Z.1 ◁ ε_ U Uᘁ ≫ (ρ_ Z.1).hom := by
  apply (cancel_epi ((Z.2.β Uᘁ hD).hom ▷ U ≫ (α_ Uᘁ Z.1 U).hom)).mp
  calc
    _ = (α_ Z.1 Uᘁ U).hom ≫
        ((Z.2.β (Uᘁ ⊗ U) (ObjectProperty.prop_tensor hD hU)).hom ≫ ε_ U Uᘁ ▷ Z.1) ≫ (λ_ Z.1).hom := by
      dsimp [tensorLeftHomEquiv]
      rw [Z.2.monoidal Uᘁ U hD hU]
      monoidal
    _ = (α_ Z.1 Uᘁ U).hom ≫
        (Z.1 ◁ ε_ U Uᘁ ≫ (Z.2.β (𝟙_ C) (ObjectProperty.prop_unit P)).hom) ≫ (λ_ Z.1).hom := by
      rw [Z.2.naturality (ObjectProperty.prop_tensor hD hU) (ObjectProperty.prop_unit P) (ε_ U Uᘁ)]
    _ = _ := by
      rw [Z.2.unit]
      simp

/-- Inserting the actual cup and then closing the dual-labelled pivotal
cap returns the original half-braiding. -/
lemma rigidInsertion_augmentationCap (Z : RelativeCenter P) (U : C) (hU : P U) (hD : P Uᘁ) :
    rigidInsertion J U Z.1 ≫ U ◁ augmentationCap J Z Uᘁ hD =
      (Z.2.β U hU).hom := by
  calc
    _ = 𝟙 (Z.1 ⊗ U) ⊗≫ η_ U Uᘁ ▷ (Z.1 ⊗ U) ⊗≫
        U ◁ (((Uᘁ ⊗ Z.1) ◁ pivotalMap J U) ≫
          (Z.2.β Uᘁ hD).inv ▷ dual C (dual C U)) ⊗≫
        U ◁ Z.1 ◁ J.leftEvaluation Uᘁ ⊗≫ 𝟙 (U ⊗ Z.1) := by
      dsimp [rigidInsertion, augmentationCap]
      monoidal
    _ = tensorLeftHomEquiv (Z.1 ⊗ U) U Uᘁ Z.1
        ((α_ Uᘁ Z.1 U).inv ≫ (Z.2.β Uᘁ hD).inv ▷ U ≫
          (α_ Z.1 Uᘁ U).hom ≫ Z.1 ◁
            ((Uᘁ ◁ J.j.hom.app U) ≫ J.leftEvaluation Uᘁ) ≫ (ρ_ Z.1).hom) := by
      rw [whisker_exchange]
      dsimp [tensorLeftHomEquiv, pivotalMap]
      monoidal
    _ = _ := by
      rw [pivotalLeftEvaluation_dual, ← halfBraiding_evaluation_mate Z U hU hD]
      exact Equiv.apply_symm_apply _ _


end Paper18.Category.RelativeCenter
