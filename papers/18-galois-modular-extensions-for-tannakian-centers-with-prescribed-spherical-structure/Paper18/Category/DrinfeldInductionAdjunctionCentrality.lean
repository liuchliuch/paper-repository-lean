import Paper18.Category.DrinfeldInductionAdjunctionCaps
import Paper18.Category.DrinfeldInductionAdjunctionNaturality
import Paper18.Category.DrinfeldInductionBraiding

/-! # Actual half-braiding compatibility of the induction augmentation -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category.Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  (J : PivotalStructure C)

/-- Naturality at the actual evaluation identifies the bent half-braiding
with the inverse half-braiding at the dual. -/
lemma halfBraiding_evaluation_mate (Z : Center C) (U : C) :
    (tensorLeftHomEquiv (Z.1 ⊗ U) U Uᘁ Z.1).symm (Z.2.β U).hom =
      (α_ Uᘁ Z.1 U).inv ≫ (Z.2.β Uᘁ).inv ▷ U ≫
        (α_ Z.1 Uᘁ U).hom ≫ Z.1 ◁ ε_ U Uᘁ ≫ (ρ_ Z.1).hom := by
  apply (cancel_epi ((Z.2.β Uᘁ).hom ▷ U ≫ (α_ Uᘁ Z.1 U).hom)).mp
  calc
    _ = (α_ Z.1 Uᘁ U).hom ≫
        ((Z.2.β (Uᘁ ⊗ U)).hom ≫ ε_ U Uᘁ ▷ Z.1) ≫ (λ_ Z.1).hom := by
      dsimp [tensorLeftHomEquiv]
      rw [Z.2.monoidal]
      monoidal
    _ = (α_ Z.1 Uᘁ U).hom ≫
        (Z.1 ◁ ε_ U Uᘁ ≫ (Z.2.β (𝟙_ C)).hom) ≫ (λ_ Z.1).hom := by
      rw [Z.2.naturality]
    _ = _ := by
      rw [halfBraiding_unit]
      simp

/-- Inserting the actual cup and then closing the dual-labelled pivotal
cap returns the original half-braiding. -/
lemma rigidInsertion_augmentationCap (Z : Center C) (U : C) :
    rigidInsertion J U Z.1 ≫ U ◁ inductionAugmentationCap J Z Uᘁ =
      (Z.2.β U).hom := by
  calc
    _ = 𝟙 (Z.1 ⊗ U) ⊗≫ η_ U Uᘁ ▷ (Z.1 ⊗ U) ⊗≫
        U ◁ (((Uᘁ ⊗ Z.1) ◁ pivotalMap J U) ≫
          (Z.2.β Uᘁ).inv ▷ dual C (dual C U)) ⊗≫
        U ◁ Z.1 ◁ J.leftEvaluation Uᘁ ⊗≫ 𝟙 (U ⊗ Z.1) := by
      dsimp [rigidInsertion, inductionAugmentationCap]
      monoidal
    _ = tensorLeftHomEquiv (Z.1 ⊗ U) U Uᘁ Z.1
        ((α_ Uᘁ Z.1 U).inv ≫ (Z.2.β Uᘁ).inv ▷ U ≫
          (α_ Z.1 Uᘁ U).hom ≫ Z.1 ◁
            ((Uᘁ ◁ J.j.hom.app U) ≫ J.leftEvaluation Uᘁ) ≫ (ρ_ Z.1).hom) := by
      rw [whisker_exchange]
      dsimp [tensorLeftHomEquiv, pivotalMap]
      monoidal
    _ = _ := by
      rw [pivotalLeftEvaluation_dual, ← halfBraiding_evaluation_mate]
      exact Equiv.apply_symm_apply _ _


section Coend
variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- Closing the universal braiding tail is the successive actual closing
of the original coend label and the newly inserted dual label. -/
lemma inductionBraidingTail_augmentation {X : C} (Z : Center C) (f : X ⟶ Z.1)
    (U T : C) :
    inductionBraidingTail S X U T ≫ inductionAugmentation J S Z f =
      ((Uᘁ ◁ inductionAugmentationComponent J Z f T) ▷ dual C (dual C U)) ≫
        inductionAugmentationCap J Z Uᘁ := by
  calc
    _ = 𝟙 ((Uᘁ ⊗ ((T ⊗ X) ⊗ Tᘁ)) ⊗ dual C (dual C U)) ⊗≫
        (((((Uᘁ ⊗ T) ⊗ X) ◁ (dualTensorIso Uᘁ T).inv)) ≫
          ((Uᘁ ⊗ T) ◁ f) ▷ (Uᘁ ⊗ T)ᘁ) ⊗≫
            inductionAugmentationCap J Z (Uᘁ ⊗ T) := by
      simp only [inductionBraidingTail, monoidalComp, assoc, inductionι_augmentation,
        inductionAugmentationComponent]
      monoidal
    _ = 𝟙 ((Uᘁ ⊗ ((T ⊗ X) ⊗ Tᘁ)) ⊗ dual C (dual C U)) ⊗≫
        (((Uᘁ ⊗ T) ◁ f) ▷ (Tᘁ ⊗ dual C (dual C U))) ⊗≫
        (((((Uᘁ ⊗ T) ⊗ Z.1) ◁ (dualTensorIso Uᘁ T).inv)) ≫
          inductionAugmentationCap J Z (Uᘁ ⊗ T)) := by
      rw [whisker_exchange]
      monoidal
    _ = _ := by
      rw [inductionAugmentationCap_tensor]
      dsimp [inductionAugmentationComponent]
      monoidal

/-- Every actual dinatural augmentation component commutes with the
constructed induction half-braiding. -/
lemma inductionHalfBraidingComponent_augmentation {X : C} (Z : Center C)
    (f : X ⟶ Z.1) (U T : C) :
    inductionHalfBraidingComponent S J X U T ≫ U ◁ inductionAugmentation J S Z f =
      (inductionAugmentationComponent J Z f T ▷ U) ≫ (Z.2.β U).hom := by
  rw [inductionHalfBraidingComponent, assoc, ← whiskerLeft_comp,
    inductionBraidingTail_augmentation, whiskerLeft_comp, ← assoc,
    ← rigidInsertion_naturality, assoc, rigidInsertion_augmentationCap]

/-- The descended augmentation satisfies the actual central-morphism
commutation equation, proved by the preserved coend universal property. -/
lemma inductionAugmentation_central {X : C} (Z : Center C) (f : X ⟶ Z.1) (U : C) :
    (inductionAugmentation J S Z f ▷ U) ≫ (Z.2.β U).hom =
      inductionHalfBraidingHom S J X U ≫ U ◁ inductionAugmentation J S Z f := by
  letI := inductionHasCoend S X
  apply mappedCoend_hom_ext (inductionDiagram X) (tensorRight U)
  intro T
  change (inductionι S X T ▷ U) ≫ _ = (inductionι S X T ▷ U) ≫ _
  rw [← assoc, ← comp_whiskerRight, inductionι_augmentation,
    inductionHalfBraidingHom_ι_assoc, inductionHalfBraidingComponent_augmentation]

end Coend

end Paper18.Category.Drinfeld
