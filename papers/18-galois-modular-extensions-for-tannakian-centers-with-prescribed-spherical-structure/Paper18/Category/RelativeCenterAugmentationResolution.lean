import Paper18.Category.RelativeCenterAugmentationCaps

/-! # Actual relative augmentation on resolved ambient coend labels -/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
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

/-- An actual label in the relative subcategory has the expected actual cap
component after descent from the ambient semisimple coend. -/
@[reassoc]
lemma inductionι_augmentation_of_property (Z : RelativeCenter P) {X : C} (f : X ⟶ Z.1)
    (T : C) (hT : P T) :
    inductionι S X T ≫ augmentation S J Z f = augmentationComponent J Z f T hT := by
  rw [inductionι_of_resolution S X T
    (fun a : Fin (S.length T) => S.simpleObject (S.label T a))
    (S.coendInclusion T) (S.coendProjection T) (S.coendResolution T), Preadditive.sum_comp]
  calc
    _ = ∑ a : Fin (S.length T),
        (((S.coendProjection T a ▷ X) ▷ dual C T) ≫
          ((S.coendInclusion T a ▷ X) ▷ dual C T)) ≫ augmentationComponent J Z f T hT := by
      apply Finset.sum_congr rfl
      intro a _
      have ha : P (S.simpleObject (S.label T a)) := S.property_label P ⟨T, hT⟩ a
      simp only [assoc, inductionι_augmentation_simple, dif_pos ha]
      rw [← augmentationComponent_dinatural J Z f ha hT (S.coendInclusion T a)]
      simp only [augmentationComponent, assoc]
    _ = _ := by
      simp only [← comp_whiskerRight, ← Preadditive.sum_comp, ← sum_whiskerRight,
        S.coendResolution, id_whiskerRight, id_comp]

/-- If the tensor-resolution component is outside the relative support,
its actual augmentation component vanishes. -/
lemma inductionι_augmentation_tensor_outside (Z : RelativeCenter P) {X : C} (f : X ⟶ Z.1)
    (U : C) (hU : P U) (i : ι) (hi : ¬ P (S.simpleObject i)) :
    inductionι S X (dual C U ⊗ S.simpleObject i) ≫ augmentation S J Z f = 0 := by
  let T := dual C U ⊗ S.simpleObject i
  rw [inductionι_of_resolution S X T
    (fun a : Fin (S.length T) => S.simpleObject (S.label T a))
    (S.coendInclusion T) (S.coendProjection T) (S.coendResolution T), Preadditive.sum_comp]
  apply Finset.sum_eq_zero
  intro a _
  have ha : ¬ P (S.simpleObject (S.label T a)) := by
    intro hlabel
    have hs : averagingSlots S (dual C U) (S.label T a) i := ⟨a, rfl⟩
    exact hi ((S.averagingSlots_property_iff J P (S.property_rightDual P hU)
      (S.label T a) i hs).mp hlabel)
  simp only [assoc, inductionι_augmentation_simple, dif_neg ha, comp_zero]

/-- Actual coend maps can be checked on the actual finite simple diagonal. -/
lemma induction_hom_ext_simple {X Y : C} {f g : inductionUnderlying S X ⟶ Y}
    (h : ∀ i, inductionι S X (S.simpleObject i) ≫ f = inductionι S X (S.simpleObject i) ≫ g) : f = g := by
  apply (cancel_epi (inductionUnderlyingIso S X).inv).mp
  apply biproduct.hom_ext'
  intro i
  have hi : biproduct.ι (fun j => (S.simpleObject j ⊗ X) ⊗ dual C (S.simpleObject j)) i ≫
      (inductionUnderlyingIso S X).inv = inductionι S X (S.simpleObject i) :=
    S.semisimpleCoendIso_inv_ι (inductionDiagram X) i
  simpa only [← assoc, hi] using h i

/-- The tensor-translated actual coend has the same finite simple-diagonal test. -/
lemma induction_tensor_hom_ext_simple {X Y : C} (U : C) {f g : inductionUnderlying S X ⊗ U ⟶ Y}
    (h : ∀ i, (inductionι S X (S.simpleObject i) ▷ U) ≫ f =
      (inductionι S X (S.simpleObject i) ▷ U) ≫ g) : f = g := by
  letI := inductionHasCoend S X
  apply mappedCoend_hom_ext (inductionDiagram X) (tensorRight U)
  intro T
  change (inductionι S X T ▷ U) ≫ f = (inductionι S X T ▷ U) ≫ g
  rw [inductionι_of_resolution S X T
    (fun a : Fin (S.length T) => S.simpleObject (S.label T a))
    (S.coendInclusion T) (S.coendProjection T) (S.coendResolution T)]
  simp only [sum_whiskerRight, Preadditive.sum_comp, comp_whiskerRight, assoc, h]

end Paper18.Category.RelativeCenter
