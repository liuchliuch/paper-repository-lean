import Paper18.Category.RelativeCenterAveragingSlide

/-! # The actual relative weighted section is central on the chosen subcategory -/
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

lemma section_tensor_coend_expansion (Z : RelativeCenter P) (U : C) (i : ι)
    (hi : P (S.simpleObject i)) :
    J.leftDim (S.simpleObject i) • ((sectionComponent Z (S.simpleObject i) hi ▷ U) ≫
      inductionHalfBraidingComponent S J Z.1 U (S.simpleObject i)) =
      ∑ a : averagingReciprocalIndex S U i, J.leftDim (S.simpleObject a.1) •
        (slideMap J Z U (S.simpleObject i) (S.simpleObject a.1) hi
          (averagingReciprocalInclusion S J U i a.1 a.2)
          (averagingReciprocalProjection S U i a.1 a.2) ≫
            U ◁ inductionι S Z.1 (S.simpleObject a.1)) := by
  let k := (sectionComponent Z (S.simpleObject i) hi ▷ U) ≫
    rigidInsertion J U ((S.simpleObject i ⊗ Z.1) ⊗ dual C (S.simpleObject i)) ≫
      U ◁ inductionBraidingComparison Z.1 U (S.simpleObject i)
  calc
    _ = k ≫ U ◁ (J.leftDim (S.simpleObject i) • inductionι S Z.1 (dual C U ⊗ S.simpleObject i)) := by
      dsimp only [k, inductionHalfBraidingComponent]
      rw [← inductionBraidingComparison_ι]
      simp only [MonoidalLinear.whiskerLeft_smul, Linear.comp_smul, whiskerLeft_comp, assoc]
    _ = ∑ a : averagingReciprocalIndex S U i, J.leftDim (S.simpleObject a.1) •
        (k ≫ U ◁ ((((averagingReciprocalProjection S U i a.1 a.2) ▷ Z.1) ▷
          dual C (dual C U ⊗ S.simpleObject i)) ≫
          (S.simpleObject a.1 ⊗ Z.1) ◁ dualMap C (averagingReciprocalInclusion S J U i a.1 a.2) ≫
          inductionι S Z.1 (S.simpleObject a.1))) := by
      rw [inductionι_reciprocal_resolution]
      simp only [whiskerLeft_sum, Preadditive.comp_sum, MonoidalLinear.whiskerLeft_smul, Linear.comp_smul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      dsimp only [k, slideMap]
      monoidal

/-- The actual slide is linear in the resolved adjacent-strand endomorphism. -/
def slideOutputLinearMap (Z : RelativeCenter P) (U B : C) (hU : P U) (hB : P B) :
    (U ⊗ B ⟶ U ⊗ B) →ₗ[ℂ] (Z.1 ⊗ U ⟶ U ⊗ inductionUnderlying S Z.1) where
  toFun e := slideEndMap Z U B hU hB e ≫ U ◁ inductionι S Z.1 B
  map_add' e f := by
    dsimp only [slideEndMap, monoidalComp]
    simp only [MonoidalPreadditive.add_whiskerRight, Preadditive.comp_add, Preadditive.add_comp]
  map_smul' c e := by
    dsimp only [slideEndMap, monoidalComp]
    simp only [MonoidalLinear.smul_whiskerRight, Linear.comp_smul, Linear.smul_comp, RingHom.id_apply]

lemma originalResolution_slide (Z : RelativeCenter P) (U : C) (hU : P U) (j : ι)
    (hj : P (S.simpleObject j)) :
    (∑ i : ι, ∑ a : averagingSlots S U i j, J.leftDim (S.simpleObject j) •
      (slideEndMap Z U (S.simpleObject j) hU hj
        (averagingOriginalProjection S U i j a ≫ averagingOriginalInclusion S U i j a) ≫
          U ◁ inductionι S Z.1 (S.simpleObject j))) =
      J.leftDim (S.simpleObject j) • ((Z.2.β U hU).hom ≫
        U ◁ (sectionComponent Z (S.simpleObject j) hj ≫ inductionι S Z.1 (S.simpleObject j))) := by
  let L := slideOutputLinearMap S Z U (S.simpleObject j) hU hj
  change (∑ i : ι, ∑ a : averagingSlots S U i j,
    J.leftDim (S.simpleObject j) • L (averagingOriginalProjection S U i j a ≫
      averagingOriginalInclusion S U i j a)) = _
  calc
    _ = J.leftDim (S.simpleObject j) • L (∑ i : ι, ∑ a : averagingSlots S U i j,
        averagingOriginalProjection S U i j a ≫ averagingOriginalInclusion S U i j a) := by
      simp only [map_sum, Finset.smul_sum]
    _ = _ := by
      rw [averagingOriginalResolution]
      change J.leftDim (S.simpleObject j) •
        (slideEndMap Z U (S.simpleObject j) hU hj (𝟙 (U ⊗ S.simpleObject j)) ≫
          U ◁ inductionι S Z.1 (S.simpleObject j)) = _
      rw [slideEndMap_id, assoc, ← whiskerLeft_comp]

/-- The actual restricted section respects every actual half-braiding
against the specified actual fusion full subcategory. -/
lemma weightedSection_central (Z : RelativeCenter P) (U : C) (hU : P U) :
    (weightedSection S J Z ▷ U) ≫ inductionHalfBraidingHom S J Z.1 U =
      (Z.2.β U hU).hom ≫ U ◁ weightedSection S J Z := by
  calc
    _ = ∑ i : ι, if hi : P (S.simpleObject i) then
        ∑ a : averagingReciprocalIndex S U i, J.leftDim (S.simpleObject a.1) •
          (slideMap J Z U (S.simpleObject i) (S.simpleObject a.1) hi
            (averagingReciprocalInclusion S J U i a.1 a.2)
            (averagingReciprocalProjection S U i a.1 a.2) ≫
              U ◁ inductionι S Z.1 (S.simpleObject a.1)) else 0 := by
      simp only [weightedSection, sum_whiskerRight, Preadditive.sum_comp]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : P (S.simpleObject i)
      · simp only [dif_pos hi]
        rw [MonoidalLinear.smul_whiskerRight, Linear.smul_comp,
          comp_whiskerRight, assoc, inductionHalfBraidingHom_ι, J.rightDim_dual]
        exact section_tensor_coend_expansion S J Z U i hi
      · simp only [dif_neg hi, MonoidalPreadditive.zero_whiskerRight, zero_comp]
    _ = ∑ i : ι, ∑ j : ι, ∑ a : averagingSlots S U i j,
        if hj : P (S.simpleObject j) then J.leftDim (S.simpleObject j) •
          (slideEndMap Z U (S.simpleObject j) hU hj
            (averagingOriginalProjection S U i j a ≫ averagingOriginalInclusion S U i j a) ≫
              U ◁ inductionι S Z.1 (S.simpleObject j)) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : P (S.simpleObject i)
      · rw [dif_pos hi, Fintype.sum_sigma]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro a _
        have hj := (S.averagingSlots_property_iff J P hU i j a).mp hi
        rw [dif_pos hj, slideMap_eq_endMap (hU := hU) (hB := hj),
          averagingRotationDown_reciprocal, averagingRotationUp_reciprocal]
      · rw [dif_neg hi]
        symm
        apply Finset.sum_eq_zero
        intro j _
        apply Finset.sum_eq_zero
        intro a _
        have hj : ¬ P (S.simpleObject j) := fun hj =>
          hi ((S.averagingSlots_property_iff J P hU i j a).mpr hj)
        exact dif_neg hj
    _ = ∑ j : ι, if hj : P (S.simpleObject j) then J.leftDim (S.simpleObject j) •
        ((Z.2.β U hU).hom ≫ U ◁
          (sectionComponent Z (S.simpleObject j) hj ≫ inductionι S Z.1 (S.simpleObject j))) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : P (S.simpleObject j)
      · simp only [dif_pos hj]
        exact originalResolution_slide S J Z U hU j hj
      · simp only [dif_neg hj, Finset.sum_const_zero]
    _ = _ := by
      simp only [weightedSection, whiskerLeft_sum, Preadditive.comp_sum]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : P (S.simpleObject j)
      · simp only [dif_pos hj]
        rw [MonoidalLinear.whiskerLeft_smul, Linear.comp_smul, J.rightDim_dual]
      · simp only [dif_neg hj, MonoidalPreadditive.whiskerLeft_zero, comp_zero]

end Paper18.Category.RelativeCenter
