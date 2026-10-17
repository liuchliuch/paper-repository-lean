import Paper18.Category.RelativeCenterAugmentationResolution

/-! # The actual relative augmentation is central on the chosen subcategory -/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u w
namespace Paper18.Category.RelativeCenter
open Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [Simple (𝟙_ C)] [BraidedCategory C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {P : ObjectProperty C} [P.IsMonoidal] [IsAdditiveFullProperty P]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι) (J : PivotalStructure C)

lemma braidingTail_augmentation {X : C} (Z : RelativeCenter P) (f : X ⟶ Z.1)
    (U T : C) (hU : P U) (hT : P T) :
    inductionBraidingTail S X U T ≫ augmentation S J Z f =
      ((dual C U ◁ augmentationComponent J Z f T hT) ▷ dual C (dual C U)) ≫
        augmentationCap J Z (dual C U) (S.property_rightDual P hU) := by
  let hD := S.property_rightDual P hU
  calc
    _ = 𝟙 ((dual C U ⊗ ((T ⊗ X) ⊗ dual C T)) ⊗ dual C (dual C U)) ⊗≫
        (((((dual C U ⊗ T) ⊗ X) ◁ (dualTensorIso (dual C U) T).inv)) ≫
          ((dual C U ⊗ T) ◁ f) ▷ dual C (dual C U ⊗ T)) ⊗≫
            augmentationCap J Z (dual C U ⊗ T) (ObjectProperty.prop_tensor hD hT) := by
      simp only [inductionBraidingTail, monoidalComp, assoc,
        inductionι_augmentation_of_property S J Z f _ (ObjectProperty.prop_tensor hD hT),
        augmentationComponent]
      monoidal
    _ = 𝟙 ((dual C U ⊗ ((T ⊗ X) ⊗ dual C T)) ⊗ dual C (dual C U)) ⊗≫
        (((dual C U ⊗ T) ◁ f) ▷ (dual C T ⊗ dual C (dual C U))) ⊗≫
        (((((dual C U ⊗ T) ⊗ Z.1) ◁ (dualTensorIso (dual C U) T).inv)) ≫
          augmentationCap J Z (dual C U ⊗ T) (ObjectProperty.prop_tensor hD hT)) := by
      rw [whisker_exchange]
      monoidal
    _ = _ := by
      rw [augmentationCap_tensor J Z _ _ hD hT]
      dsimp [augmentationComponent]
      monoidal

lemma halfBraidingComponent_augmentation {X : C} (Z : RelativeCenter P)
    (f : X ⟶ Z.1) (U T : C) (hU : P U) (hT : P T) :
    inductionHalfBraidingComponent S J X U T ≫ U ◁ augmentation S J Z f =
      (augmentationComponent J Z f T hT ▷ U) ≫ (Z.2.β U hU).hom := by
  rw [inductionHalfBraidingComponent, assoc, ← whiskerLeft_comp,
    braidingTail_augmentation S J Z f U T hU hT, whiskerLeft_comp, ← assoc,
    ← rigidInsertion_naturality, assoc,
    rigidInsertion_augmentationCap J Z U hU (S.property_rightDual P hU)]

lemma halfBraidingComponent_augmentation_outside {X : C} (Z : RelativeCenter P)
    (f : X ⟶ Z.1) (U : C) (hU : P U) (i : ι) (hi : ¬ P (S.simpleObject i)) :
    inductionHalfBraidingComponent S J X U (S.simpleObject i) ≫ U ◁ augmentation S J Z f = 0 := by
  rw [inductionHalfBraidingComponent, assoc, ← whiskerLeft_comp]
  have hz : inductionBraidingTail S X U (S.simpleObject i) ≫ augmentation S J Z f = 0 := by
    dsimp only [inductionBraidingTail, monoidalComp]
    simp only [assoc, inductionι_augmentation_tensor_outside S J Z f U hU i hi, comp_zero]
  rw [hz, MonoidalPreadditive.whiskerLeft_zero, comp_zero]

/-- Actual relative augmentation commutes with the actual induced half-braiding;
labels outside the relative subcategory vanish by tensor and dual closure. -/
lemma augmentation_central {X : C} (Z : RelativeCenter P) (f : X ⟶ Z.1) (U : C) (hU : P U) :
    (augmentation S J Z f ▷ U) ≫ (Z.2.β U hU).hom =
      inductionHalfBraidingHom S J X U ≫ U ◁ augmentation S J Z f := by
  apply induction_tensor_hom_ext_simple S U
  intro i
  rw [← assoc, ← comp_whiskerRight, inductionι_augmentation_simple,
    inductionHalfBraidingHom_ι_assoc]
  by_cases hi : P (S.simpleObject i)
  · rw [dif_pos hi]
    exact (halfBraidingComponent_augmentation S J Z f U (S.simpleObject i) hU hi).symm
  · rw [dif_neg hi, MonoidalPreadditive.zero_whiskerRight, zero_comp,
      halfBraidingComponent_augmentation_outside S J Z f U hU i hi]

/-- The cap is an actual morphism in the relative center. -/
def augmentationHom {X : C} (Z : RelativeCenter P) (f : X ⟶ Z.1) :
    (restriction P).obj (inductionObj S J X) ⟶ Z where
  f := augmentation S J Z f
  comm U hU := augmentation_central S J Z f U hU

end Paper18.Category.RelativeCenter
