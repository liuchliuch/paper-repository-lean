import Paper18.Category.DrinfeldInductionAdjunctionAugmentation

/-! # Naturality of the actual induction augmentation -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category.Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  (J : PivotalStructure C)

omit [RightRigidCategory C] in
/-- The inverse commutation equation of an actual central morphism. -/
lemma centerHom_inv_halfBraiding {Z W : Center C} (h : Z ⟶ W) (T : C) :
    (T ◁ h.f) ≫ (W.2.β T).inv = (Z.2.β T).inv ≫ (h.f ▷ T) := by
  apply (cancel_epi (Z.2.β T).hom).mp
  rw [← assoc, ← h.comm T, assoc]
  simp

/-- Closing the inverse half-braiding commutes with actual central morphisms. -/
lemma inductionAugmentationCap_naturality {Z W : Center C} (h : Z ⟶ W) (T : C) :
    ((T ◁ h.f) ▷ Tᘁ) ≫ inductionAugmentationCap J W T =
      inductionAugmentationCap J Z T ≫ h.f := by
  dsimp [inductionAugmentationCap]
  rw [← comp_whiskerRight_assoc, centerHom_inv_halfBraiding, comp_whiskerRight_assoc]
  calc
    _ = (Z.2.β T).inv ▷ Tᘁ ≫ (α_ Z.1 T Tᘁ).hom ≫
        ((h.f ▷ (T ⊗ Tᘁ)) ≫ W.1 ◁ J.leftEvaluation T) ≫ (ρ_ W.1).hom := by
      monoidal
    _ = _ := by
      rw [← whisker_exchange]
      monoidal

/-- The actual dinatural augmentation components are natural in their central target. -/
lemma inductionAugmentationComponent_naturality {X : C} {Z W : Center C}
    (h : Z ⟶ W) (f : X ⟶ Z.1) (T : C) :
    inductionAugmentationComponent J W (f ≫ h.f) T =
      inductionAugmentationComponent J Z f T ≫ h.f := by
  simp only [inductionAugmentationComponent, whiskerLeft_comp, comp_whiskerRight,
    assoc, inductionAugmentationCap_naturality]

section Coend
variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- Naturality of the descended augmentation follows from the actual coend property. -/
lemma inductionAugmentation_naturality {X : C} {Z W : Center C}
    (h : Z ⟶ W) (f : X ⟶ Z.1) :
    inductionAugmentation J S W (f ≫ h.f) = inductionAugmentation J S Z f ≫ h.f := by
  letI := inductionHasCoend S X
  apply coend.hom_ext
  intro T
  change inductionι S X T ≫ _ = inductionι S X T ≫ _
  simp only [inductionι_augmentation, inductionι_augmentation_assoc,
    inductionAugmentationComponent_naturality]

end Coend
end Paper18.Category.Drinfeld
