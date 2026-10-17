import Paper18.Category.DrinfeldSemisimpleSlideDiagram
import Paper18.Category.DrinfeldSemisimpleNaturality

/-! # Actual centrality of the weighted induction section -/
noncomputable section
universe v u w
namespace Paper18.Category.Drinfeld
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
open Classical
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι) (J : PivotalStructure C)

/-- The weighted cup sum is central. The equality follows from actual
reciprocal decompositions, the proved rigid slide, and actual identity
resolutions; no centrality datum is supplied. -/
lemma inductionWeightedSection_central (Z : Center C) (U : C) :
    (inductionWeightedSection S J Z ▷ U) ≫ inductionHalfBraidingHom S J Z.1 U =
      (Z.2.β U).hom ≫ U ◁ inductionWeightedSection S J Z := by
  rw [inductionWeightedSection_comm_expansion]
  calc
    _ = ∑ i : ι, ∑ j : ι, ∑ a : averagingSlots S U i j, J.leftDim (S.simpleObject j) •
        (averagingSlideEndMap Z U (S.simpleObject j)
          (averagingOriginalProjection S U i j a ≫ averagingOriginalInclusion S U i j a) ≫
            U ◁ inductionι S Z.1 (S.simpleObject j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro a ha
      rw [averagingSlideMap_eq_endMap, averagingRotationDown_reciprocal,
        averagingRotationUp_reciprocal]
    _ = ∑ j : ι, ∑ i : ι, ∑ a : averagingSlots S U i j, J.leftDim (S.simpleObject j) •
        (averagingSlideEndMap Z U (S.simpleObject j)
          (averagingOriginalProjection S U i j a ≫ averagingOriginalInclusion S U i j a) ≫
            U ◁ inductionι S Z.1 (S.simpleObject j)) := Finset.sum_comm
    _ = ∑ j : ι, J.leftDim (S.simpleObject j) • ((Z.2.β U).hom ≫
        U ◁ (inductionSectionComponent Z (S.simpleObject j) ≫
          inductionι S Z.1 (S.simpleObject j))) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact averagingOriginalResolution_slide S J Z U j
    _ = _ := inductionWeightedSection_comm_target S J Z U

lemma inductionNormalizedSection_central (Z : Center C) (U : C) :
    (inductionNormalizedSection S J Z ▷ U) ≫ inductionHalfBraidingHom S J Z.1 U =
      (Z.2.β U).hom ≫ U ◁ inductionNormalizedSection S J Z := by
  simp only [inductionNormalizedSection, MonoidalLinear.smul_whiskerRight,
    Linear.smul_comp, inductionWeightedSection_central, MonoidalLinear.whiskerLeft_smul,
    Linear.comp_smul]

/-- The normalized weighted section is an actual morphism in the center. -/
def inductionNormalizedSectionHom (Z : Center C) : Z ⟶ inductionObj S J Z.1 where
  f := inductionNormalizedSection S J Z
  comm U := inductionNormalizedSection_central S J Z U

@[simp] lemma inductionNormalizedSectionHom_f (Z : Center C) :
    (inductionNormalizedSectionHom S J Z).f = inductionNormalizedSection S J Z := rfl

/-- The actual induction counit splits in the actual center. -/
@[reassoc (attr := simp)]
lemma inductionNormalizedSectionHom_counit (Z : Center C) :
    inductionNormalizedSectionHom S J Z ≫ inductionCounit S J Z = 𝟙 Z := by
  apply Center.ext
  exact inductionNormalizedSection_counit S J Z

lemma inductionNormalizedSectionHom_naturality {Z W : Center C} (f : Z ⟶ W) :
    f ≫ inductionNormalizedSectionHom S J W =
      inductionNormalizedSectionHom S J Z ≫ (inductionFunctor S J).map f.f := by
  apply Center.ext
  exact inductionNormalizedSection_naturality S J f

/-- Actual central averaging of an arbitrary underlying morphism. -/
def centerAverage {Z W : Center C} (f : Z.1 ⟶ W.1) : Z ⟶ W :=
  inductionNormalizedSectionHom S J Z ≫ (inductionFunctor S J).map f ≫ inductionCounit S J W

@[simp] lemma centerAverage_f {Z W : Center C} (f : Z.1 ⟶ W.1) :
    (centerAverage S J f).f = centerAverageUnderlying S J f := rfl

@[simp] lemma centerAverage_central_map {Z W : Center C} (f : Z ⟶ W) :
    centerAverage S J f.f = f := by
  apply Center.ext
  exact centerAverageUnderlying_central_map S J f

end Paper18.Category.Drinfeld
