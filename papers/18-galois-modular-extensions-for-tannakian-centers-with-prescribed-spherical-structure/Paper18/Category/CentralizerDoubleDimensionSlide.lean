import Paper18.Category.CentralizerDoubleDimensionBasic

/-! # Actual weighted centrality restricted to a fusion full subcategory -/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)] [BraidedCategory C]
  {ι : Type w} [Fintype ι]
namespace Drinfeld
variable (S : FiniteSemisimpleSkeleton C ι) (J : PivotalStructure C)

/-- The actual cup section weighted by an arbitrary scalar support. -/
def supportedInductionSection (c : ι → ℂ) (Z : Center C) : Z.1 ⟶ inductionUnderlying S Z.1 :=
  ∑ i, c i • (J.leftDim (S.simpleObject i) •
    (inductionSectionComponent Z (S.simpleObject i) ≫ inductionι S Z.1 (S.simpleObject i)))

/-- A support constant along the actual tensor-resolution graph passes
through the actual reciprocal slide. This is a morphism identity. -/
lemma supportedInductionSection_central (c : ι → ℂ) (Z : Center C) (U : C)
    (hc : ∀ i j, averagingSlots S U i j → c i = c j) :
    (supportedInductionSection S J c Z ▷ U) ≫ inductionHalfBraidingHom S J Z.1 U =
      (Z.2.β U).hom ≫ U ◁ supportedInductionSection S J c Z := by
  calc
    _ = ∑ i, c i • (J.leftDim (S.simpleObject i) •
        ((inductionSectionComponent Z (S.simpleObject i) ▷ U) ≫
          inductionHalfBraidingComponent S J Z.1 U (S.simpleObject i))) := by
      simp only [supportedInductionSection, sum_whiskerRight,
        MonoidalLinear.smul_whiskerRight, Preadditive.sum_comp, Linear.smul_comp,
        comp_whiskerRight, assoc, inductionHalfBraidingHom_ι]
    _ = ∑ i, c i • ∑ a : averagingReciprocalIndex S U i,
        J.leftDim (S.simpleObject a.1) •
          (averagingSlideMap J Z U (S.simpleObject i) (S.simpleObject a.1)
            (averagingReciprocalInclusion S J U i a.1 a.2)
            (averagingReciprocalProjection S U i a.1 a.2) ≫
              U ◁ inductionι S Z.1 (S.simpleObject a.1)) := by
      simp_rw [inductionSection_tensor_coend_expansion]
    _ = ∑ i : ι, ∑ j : ι, ∑ a : averagingSlots S U i j, c j •
        (J.leftDim (S.simpleObject j) •
          (averagingSlideEndMap Z U (S.simpleObject j)
            (averagingOriginalProjection S U i j a ≫ averagingOriginalInclusion S U i j a) ≫
              U ◁ inductionι S Z.1 (S.simpleObject j))) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Fintype.sum_sigma, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [hc i j a, averagingSlideMap_eq_endMap, averagingRotationDown_reciprocal,
        averagingRotationUp_reciprocal]
    _ = ∑ j : ι, c j • (∑ i : ι, ∑ a : averagingSlots S U i j,
        J.leftDim (S.simpleObject j) •
          (averagingSlideEndMap Z U (S.simpleObject j)
            (averagingOriginalProjection S U i j a ≫ averagingOriginalInclusion S U i j a) ≫
              U ◁ inductionι S Z.1 (S.simpleObject j))) := by
      rw [Finset.sum_comm]
      simp only [Finset.smul_sum]
    _ = ∑ j, c j • (J.leftDim (S.simpleObject j) • ((Z.2.β U).hom ≫
        U ◁ (inductionSectionComponent Z (S.simpleObject j) ≫
          inductionι S Z.1 (S.simpleObject j)))) := by
      simp_rw [averagingOriginalResolution_slide]
    _ = _ := by
      simp only [supportedInductionSection, whiskerLeft_sum, MonoidalLinear.whiskerLeft_smul,
        Preadditive.comp_sum, Linear.comp_smul]

/-- The actual section restricted to the simples of the actual full subcategory. -/
def restrictedInductionSection (P : ObjectProperty C) (Z : Center C) :
    Z.1 ⟶ inductionUnderlying S Z.1 :=
  supportedInductionSection S J (fun i => if P (S.simpleObject i) then 1 else 0) Z

/-- Actual restricted centrality follows from tensor, summand and dual
closure, with all reciprocal decompositions taken in the ambient category. -/
lemma restrictedInductionSection_central (P : ObjectProperty C)
    [IsAdditiveFullProperty P] [P.IsMonoidal] (Z : Center C) (U : C) (hU : P U) :
    (restrictedInductionSection S J P Z ▷ U) ≫ inductionHalfBraidingHom S J Z.1 U =
      (Z.2.β U).hom ≫ U ◁ restrictedInductionSection S J P Z := by
  apply supportedInductionSection_central S J
  intro i j a
  rw [propext (S.averagingSlots_property_iff J P hU i j a)]

end Drinfeld
end Paper18.Category
