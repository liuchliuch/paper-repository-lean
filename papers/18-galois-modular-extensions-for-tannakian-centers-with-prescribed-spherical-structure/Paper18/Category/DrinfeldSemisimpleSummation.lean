import Paper18.Category.DrinfeldSemisimpleSliding
import Paper18.Category.DrinfeldSemisimpleDiagram

/-! # Actual weighted coend expansion in the averaging calculation -/
noncomputable section
universe v u w
namespace Paper18.Category.Drinfeld
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
open Classical
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

/-- The individual actual diagram appearing after the reciprocal resolution
of the tensor-dual coend index. -/
def averagingSlideMap (J : PivotalStructure C) (Z : Center C) (U A B : C)
    (u : B ⟶ dual C U ⊗ A) (p : dual C U ⊗ A ⟶ B) :
    Z.1 ⊗ U ⟶ U ⊗ ((B ⊗ Z.1) ⊗ dual C B) :=
  𝟙 (Z.1 ⊗ U) ⊗≫ (inductionSectionComponent Z A ▷ U) ⊗≫
    rigidInsertion J U ((A ⊗ Z.1) ⊗ dual C A) ⊗≫
    U ◁ inductionBraidingComparison Z.1 U A ⊗≫
    U ◁ (((p ▷ Z.1) ▷ dual C (dual C U ⊗ A)) ≫
      (B ⊗ Z.1) ◁ dualMap C u) ⊗≫ 𝟙 (U ⊗ ((B ⊗ Z.1) ⊗ dual C B))

/-- The resolved diagram after sliding, linear in the actual endomorphism
of the two adjacent strands. -/
def averagingSlideEndMap (Z : Center C) (U B : C) (e : U ⊗ B ⟶ U ⊗ B) :
    Z.1 ⊗ U ⟶ U ⊗ ((B ⊗ Z.1) ⊗ dual C B) :=
  𝟙 (Z.1 ⊗ U) ⊗≫ (Z.2.β U).hom ⊗≫ U ◁ inductionSectionComponent Z B ⊗≫
    (e ▷ Z.1) ▷ dual C B ⊗≫ 𝟙 (U ⊗ ((B ⊗ Z.1) ⊗ dual C B))

lemma averagingSlideEndMap_id (Z : Center C) (U B : C) :
    averagingSlideEndMap Z U B (𝟙 (U ⊗ B)) =
      (Z.2.β U).hom ≫ U ◁ inductionSectionComponent Z B := by
  dsimp only [averagingSlideEndMap]
  simp only [id_whiskerRight]
  monoidal

section Coend
variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι) (J : PivotalStructure C)

lemma inductionSection_tensor_coend_expansion (Z : Center C) (U : C) (i : ι) :
    J.leftDim (S.simpleObject i) •
      ((inductionSectionComponent Z (S.simpleObject i) ▷ U) ≫
        inductionHalfBraidingComponent S J Z.1 U (S.simpleObject i)) =
      ∑ a : averagingReciprocalIndex S U i, J.leftDim (S.simpleObject a.1) •
        (averagingSlideMap J Z U (S.simpleObject i) (S.simpleObject a.1)
          (averagingReciprocalInclusion S J U i a.1 a.2)
          (averagingReciprocalProjection S U i a.1 a.2) ≫
            U ◁ inductionι S Z.1 (S.simpleObject a.1)) := by
  let k := (inductionSectionComponent Z (S.simpleObject i) ▷ U) ≫
    rigidInsertion J U ((S.simpleObject i ⊗ Z.1) ⊗ dual C (S.simpleObject i)) ≫
    U ◁ inductionBraidingComparison Z.1 U (S.simpleObject i)
  calc
    _ = k ≫ U ◁ (J.leftDim (S.simpleObject i) •
        inductionι S Z.1 (dual C U ⊗ S.simpleObject i)) := by
      dsimp only [k, inductionHalfBraidingComponent]
      rw [← inductionBraidingComparison_ι]
      simp only [MonoidalLinear.whiskerLeft_smul, Linear.comp_smul,
        whiskerLeft_comp, assoc]
    _ = ∑ a : averagingReciprocalIndex S U i, J.leftDim (S.simpleObject a.1) •
        (k ≫ U ◁ ((((averagingReciprocalProjection S U i a.1 a.2) ▷ Z.1) ▷
          dual C (dual C U ⊗ S.simpleObject i)) ≫
          (S.simpleObject a.1 ⊗ Z.1) ◁ dualMap C
            (averagingReciprocalInclusion S J U i a.1 a.2) ≫
          inductionι S Z.1 (S.simpleObject a.1))) := by
      rw [inductionι_reciprocal_resolution]
      simp only [whiskerLeft_sum, Preadditive.comp_sum, MonoidalLinear.whiskerLeft_smul,
        Linear.comp_smul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      congr 1
      dsimp only [k, averagingSlideMap]
      monoidal

/-- The sliding endomorphism followed by its actual universal coend
inclusion is complex linear. -/
def averagingSlideOutputLinearMap (Z : Center C) (U B : C) :
    (U ⊗ B ⟶ U ⊗ B) →ₗ[ℂ] (Z.1 ⊗ U ⟶ U ⊗ inductionUnderlying S Z.1) where
  toFun e := averagingSlideEndMap Z U B e ≫ U ◁ inductionι S Z.1 B
  map_add' e f := by
    dsimp only [averagingSlideEndMap, monoidalComp]
    simp only [MonoidalPreadditive.add_whiskerRight, Preadditive.comp_add, Preadditive.add_comp]
  map_smul' c e := by
    dsimp only [averagingSlideEndMap, monoidalComp]
    simp only [MonoidalLinear.smul_whiskerRight, Linear.comp_smul, Linear.smul_comp,
      RingHom.id_apply]

lemma averagingOriginalResolution_slide (Z : Center C) (U : C) (j : ι) :
    (∑ i : ι, ∑ a : averagingSlots S U i j, J.leftDim (S.simpleObject j) •
      (averagingSlideEndMap Z U (S.simpleObject j)
        (averagingOriginalProjection S U i j a ≫ averagingOriginalInclusion S U i j a) ≫
          U ◁ inductionι S Z.1 (S.simpleObject j))) =
      J.leftDim (S.simpleObject j) • ((Z.2.β U).hom ≫
        U ◁ (inductionSectionComponent Z (S.simpleObject j) ≫
          inductionι S Z.1 (S.simpleObject j))) := by
  let L := averagingSlideOutputLinearMap S Z U (S.simpleObject j)
  change (∑ i : ι, ∑ a : averagingSlots S U i j, J.leftDim (S.simpleObject j) •
    L (averagingOriginalProjection S U i j a ≫ averagingOriginalInclusion S U i j a)) = _
  calc
    _ = J.leftDim (S.simpleObject j) • L (∑ i : ι, ∑ a : averagingSlots S U i j,
        averagingOriginalProjection S U i j a ≫ averagingOriginalInclusion S U i j a) := by
      simp only [map_sum, Finset.smul_sum]
    _ = _ := by
      rw [averagingOriginalResolution]
      change J.leftDim (S.simpleObject j) •
        (averagingSlideEndMap Z U (S.simpleObject j) (𝟙 (U ⊗ S.simpleObject j)) ≫
          U ◁ inductionι S Z.1 (S.simpleObject j)) = _
      rw [averagingSlideEndMap_id, assoc, ← whiskerLeft_comp]

/-- The full weighted commutation expression is the actual double sum of
the individual reciprocal diagrams. -/
lemma inductionWeightedSection_comm_expansion (Z : Center C) (U : C) :
    (inductionWeightedSection S J Z ▷ U) ≫ inductionHalfBraidingHom S J Z.1 U =
      ∑ i : ι, ∑ a : averagingReciprocalIndex S U i, J.leftDim (S.simpleObject a.1) •
        (averagingSlideMap J Z U (S.simpleObject i) (S.simpleObject a.1)
          (averagingReciprocalInclusion S J U i a.1 a.2)
          (averagingReciprocalProjection S U i a.1 a.2) ≫
            U ◁ inductionι S Z.1 (S.simpleObject a.1)) := by
  calc
    _ = ∑ i : ι, J.leftDim (S.simpleObject i) •
        ((inductionSectionComponent Z (S.simpleObject i) ▷ U) ≫
          inductionHalfBraidingComponent S J Z.1 U (S.simpleObject i)) := by
      simp only [inductionWeightedSection, J.rightDim_dual, sum_whiskerRight,
        MonoidalLinear.smul_whiskerRight, Preadditive.sum_comp, Linear.smul_comp,
        comp_whiskerRight, assoc, inductionHalfBraidingHom_ι]
    _ = _ := by simp_rw [inductionSection_tensor_coend_expansion]

lemma inductionWeightedSection_comm_target (Z : Center C) (U : C) :
    (∑ j : ι, J.leftDim (S.simpleObject j) • ((Z.2.β U).hom ≫
      U ◁ (inductionSectionComponent Z (S.simpleObject j) ≫
        inductionι S Z.1 (S.simpleObject j)))) =
      (Z.2.β U).hom ≫ U ◁ inductionWeightedSection S J Z := by
  simp only [inductionWeightedSection, J.rightDim_dual, whiskerLeft_sum,
    MonoidalLinear.whiskerLeft_smul, Preadditive.comp_sum, Linear.comp_smul]

end Coend
end Paper18.Category.Drinfeld
