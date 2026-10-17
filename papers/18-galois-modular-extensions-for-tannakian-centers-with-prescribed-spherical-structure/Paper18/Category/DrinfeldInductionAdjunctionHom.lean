import Paper18.Category.DrinfeldInductionAdjunctionGeneration

/-! # The actual universal Hom correspondence for central induction -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category.Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  (J : PivotalStructure C)

/-- Naturality at the actual pivotal cap converts a forward crossing on
the dual strand into the inverse crossing used by the augmentation. -/
lemma inductionAugmentationCap_forward (Z : Center C) (T : C) :
    𝟙 ((T ⊗ Z.1) ⊗ Tᘁ) ⊗≫ T ◁ (Z.2.β Tᘁ).hom ⊗≫
      J.leftEvaluation T ▷ Z.1 ⊗≫ 𝟙 Z.1 = inductionAugmentationCap J Z T := by
  apply (cancel_epi ((Z.2.β T).hom ▷ Tᘁ)).mp
  calc
    _ = (α_ Z.1 T Tᘁ).hom ≫
        ((Z.2.β (T ⊗ Tᘁ)).hom ≫ J.leftEvaluation T ▷ Z.1) ≫ (λ_ Z.1).hom := by
      rw [Z.2.monoidal]
      monoidal
    _ = (α_ Z.1 T Tᘁ).hom ≫
        (Z.1 ◁ J.leftEvaluation T ≫ (Z.2.β (𝟙_ C)).hom) ≫ (λ_ Z.1).hom := by
      rw [Z.2.naturality]
    _ = _ := by
      rw [halfBraiding_unit]
      dsimp [inductionAugmentationCap]
      simp

section Coend
variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- An actual map satisfying the central commutation equation is determined
on every universal component by its value on the actual adjunction unit. -/
lemma inductionCentralHom_component {X : C} (Z : Center C)
    (h : inductionUnderlying S X ⟶ Z.1)
    (hc : ∀ U, (h ▷ U) ≫ (Z.2.β U).hom =
      inductionHalfBraidingHom S J X U ≫ U ◁ h) (T : C) :
    inductionι S X T ≫ h =
      inductionAugmentationComponent J Z (inductionAdjunctionUnit J S X ≫ h) T := by
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
        (𝟙 ((T ⊗ Z.1) ⊗ Tᘁ) ⊗≫ T ◁ (Z.2.β Tᘁ).hom ⊗≫
          J.leftEvaluation T ▷ Z.1 ⊗≫ 𝟙 Z.1) := by
      rw [← hc]
      monoidal
    _ = _ := by
      rw [inductionAugmentationCap_forward]
      rfl

/-- The actual augmentation recovers every map satisfying the central
commutation equation; centrality is used as the genuine morphism equation. -/
lemma inductionAugmentation_recover {X : C} (Z : Center C)
    (h : inductionUnderlying S X ⟶ Z.1)
    (hc : ∀ U, (h ▷ U) ≫ (Z.2.β U).hom =
      inductionHalfBraidingHom S J X U ≫ U ◁ h) :
    inductionAugmentation J S Z (inductionAdjunctionUnit J S X ≫ h) = h := by
  letI := inductionHasCoend S X
  apply coend.hom_ext
  intro T
  change inductionι S X T ≫ _ = inductionι S X T ≫ _
  rw [inductionι_augmentation, inductionCentralHom_component J S Z h hc]

end Coend
end Paper18.Category.Drinfeld
