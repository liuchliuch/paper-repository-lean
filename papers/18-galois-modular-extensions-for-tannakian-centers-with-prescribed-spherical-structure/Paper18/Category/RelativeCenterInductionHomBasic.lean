import Paper18.Category.RelativeCenterSemisimple

/-! # Actual relative induction maps are determined on their supported labels -/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u w
namespace Paper18.Category.RelativeCenter
open Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  {P : ObjectProperty C} [P.IsMonoidal] (J : PivotalStructure C)

/-- Naturality at the actual pivotal cap converts a forward crossing on
the dual strand into the inverse crossing used by the augmentation. -/
lemma augmentationCap_forward (Z : RelativeCenter P) (T : C) (hT : P T) (hD : P Tᘁ) :
    𝟙 ((T ⊗ Z.1) ⊗ Tᘁ) ⊗≫ T ◁ (Z.2.β Tᘁ hD).hom ⊗≫
      J.leftEvaluation T ▷ Z.1 ⊗≫ 𝟙 Z.1 = augmentationCap J Z T hT := by
  apply (cancel_epi ((Z.2.β T hT).hom ▷ Tᘁ)).mp
  calc
    _ = (α_ Z.1 T Tᘁ).hom ≫
        ((Z.2.β (T ⊗ Tᘁ) (ObjectProperty.prop_tensor hT hD)).hom ≫ J.leftEvaluation T ▷ Z.1) ≫ (λ_ Z.1).hom := by
      rw [Z.2.monoidal T Tᘁ hT hD]
      monoidal
    _ = (α_ Z.1 T Tᘁ).hom ≫
        (Z.1 ◁ J.leftEvaluation T ≫ (Z.2.β (𝟙_ C) (ObjectProperty.prop_unit P)).hom) ≫ (λ_ Z.1).hom := by
      rw [Z.2.naturality (ObjectProperty.prop_tensor hT hD) (ObjectProperty.prop_unit P) (J.leftEvaluation T)]
    _ = _ := by
      rw [Z.2.unit]
      dsimp [augmentationCap]
      simp

variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- An actual map satisfying the central commutation equation is determined
on every universal component by its value on the actual adjunction unit. -/
lemma inductionCentralHom_component {X : C} (Z : RelativeCenter P)
    (h : inductionUnderlying S X ⟶ Z.1)
    (hc : ∀ U (hU : P U), (h ▷ U) ≫ (Z.2.β U hU).hom =
      inductionHalfBraidingHom S J X U ≫ U ◁ h) (T : C) (hT : P T) (hD : P Tᘁ) :
    inductionι S X T ≫ h =
      augmentationComponent J Z (inductionAdjunctionUnit J S X ≫ h) T hT := by
  calc
    _ = (𝟙 ((T ⊗ X) ⊗ Tᘁ) ⊗≫
        T ◁ ((inductionAdjunctionUnit J S X ▷ Tᘁ) ≫
          inductionHalfBraidingHom S J X Tᘁ) ⊗≫
        J.leftEvaluation T ▷ inductionUnderlying S X ⊗≫
          𝟙 (inductionUnderlying S X)) ≫ h := by
      rw [inductionι_generated]
    _ = 𝟙 ((T ⊗ X) ⊗ Tᘁ) ⊗≫
        T ◁ ((inductionAdjunctionUnit J S X ▷ Tᘁ) ≫
          inductionHalfBraidingHom S J X Tᘁ) ⊗≫
        ((J.leftEvaluation T ▷ inductionUnderlying S X) ≫ (𝟙_ C) ◁ h) ⊗≫
          𝟙 Z.1 := by monoidal
    _ = 𝟙 ((T ⊗ X) ⊗ Tᘁ) ⊗≫
        T ◁ ((inductionAdjunctionUnit J S X ▷ Tᘁ) ≫
          (inductionHalfBraidingHom S J X Tᘁ ≫ Tᘁ ◁ h)) ⊗≫
        J.leftEvaluation T ▷ Z.1 ⊗≫ 𝟙 Z.1 := by
      rw [← whisker_exchange]
      monoidal
    _ = ((T ◁ (inductionAdjunctionUnit J S X ≫ h)) ▷ Tᘁ) ≫
        (𝟙 ((T ⊗ Z.1) ⊗ Tᘁ) ⊗≫ T ◁ (Z.2.β Tᘁ hD).hom ⊗≫
          J.leftEvaluation T ▷ Z.1 ⊗≫ 𝟙 Z.1) := by
      rw [← hc Tᘁ hD]
      monoidal
    _ = _ := by
      rw [augmentationCap_forward J Z T hT hD]
      rfl


variable [Simple (𝟙_ C)] [BraidedCategory C] [IsAdditiveFullProperty P]

/-- Every actual relative-central map supported on the specified simple
coend labels is recovered from its actual unit component. -/
lemma augmentation_recover_supported {X : C} (Z : RelativeCenter P)
    (h : (restriction P).obj (inductionObj S J X) ⟶ Z)
    (hs : ∀ i, ¬ P (S.simpleObject i) → inductionι S X (S.simpleObject i) ≫ h.f = 0) :
    augmentation S J Z (inductionAdjunctionUnit J S X ≫ h.f) = h.f := by
  apply induction_hom_ext_simple S
  intro i
  rw [inductionι_augmentation_simple]
  by_cases hi : P (S.simpleObject i)
  · rw [dif_pos hi]
    exact (inductionCentralHom_component J S Z h.f
      (fun U hU => h.comm U hU) (S.simpleObject i) hi (S.property_rightDual P hi)).symm
  · rw [dif_neg hi, hs i hi]

end Paper18.Category.RelativeCenter
