import Paper18.Category.HopfLinkNondegenerateProjector
import Paper18.Category.PivotalPartialTrace

/-! # The actual weighted Hopf loop represented by central averaging -/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory CategoryTheory.Limits
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
namespace PivotalStructure
open Drinfeld
variable (J : PivotalStructure C) (S : FiniteSemisimpleSkeleton C ι)

/-- The positive-section/negative-cap component of actual central averaging. -/
def averagingHopfLoop (X T : C) : X ⟶ X :=
  inductionSectionComponent ((positive C).obj X) T ≫
    inductionAugmentationCap J ((negative C).obj X) T

/-- The actual averaging component is precisely an open positive Hopf loop:
insert the actual right cup, double-braid, and close the pivotal left cap. -/
lemma averagingHopfLoop_eq (X T : C) : J.averagingHopfLoop X T =
    (ρ_ X).inv ≫ X ◁ η_ T (dual C T) ≫ (α_ X T (dual C T)).inv ≫
      (doubleBraiding X T).hom ▷ dual C T ≫ (α_ X T (dual C T)).hom ≫
      X ◁ J.leftEvaluation T ≫ (ρ_ X).hom := by
  unfold averagingHopfLoop
  rw [inductionSectionComponent_transpose]
  calc
    _ = 𝟙 X ⊗≫ X ◁ η_ T (dual C T) ⊗≫
        ((β_ X T).hom ≫ (β_ T X).hom) ▷ dual C T ⊗≫
        X ◁ J.leftEvaluation T ⊗≫ 𝟙 X := by
      dsimp only [inductionAugmentationCap]
      monoidal
    _ = _ := by
      dsimp only [doubleBraiding, Iso.trans_hom]
      monoidal


/-- The actual averaging loop is the actual right partial trace of monodromy. -/
lemma averagingHopfLoop_eq_rightPartialTrace (X T : C) :
    J.averagingHopfLoop X T = J.rightPartialTrace T (doubleBraiding X T).hom := by
  rw [J.averagingHopfLoop_eq]
  rfl

/-- Closing the retained strand yields the actual categorical Hopf-link trace. -/
lemma rightTraceScalar_averagingHopfLoop (X T : C) :
    unitScalarEquiv (C := C) (J.rightTrace (J.averagingHopfLoop X T)) =
      J.hopfLink X T := by
  rw [J.averagingHopfLoop_eq_rightPartialTrace, J.rightTrace_rightPartialTrace]
  rfl

/-- Central averaging is the normalized sum of the actual open Hopf loops,
with weights given by the actual dimensions of the chosen dual simples. -/
lemma hopfProjector_weighted_loops (X : C) :
    J.hopfProjector S X = ((J.pivotalData S).globalDimension)⁻¹ •
      ∑ i, J.rightDim (dual C (S.simpleObject i)) • J.averagingHopfLoop X (S.simpleObject i) := by
  rw [J.hopfProjector_eq, inductionNormalizedSection, Linear.smul_comp]
  congr 1
  simp only [inductionWeightedSection, Preadditive.sum_comp, Linear.smul_comp,
    assoc, inductionCounit, inductionAugmentationHom_f, inductionι_augmentation,
    inductionAugmentationComponent, averagingHopfLoop]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  change inductionSectionComponent ((positive C).obj X) (S.simpleObject i) ≫
    ((S.simpleObject i ◁ 𝟙 X) ▷ dual C (S.simpleObject i)) ≫
      inductionAugmentationCap J ((negative C).obj X) (S.simpleObject i) = _
  rw [whiskerLeft_id, id_whiskerRight]
  exact congrArg (fun f => inductionSectionComponent ((positive C).obj X) (S.simpleObject i) ≫ f)
    (id_comp (inductionAugmentationCap J ((negative C).obj X) (S.simpleObject i)))

end PivotalStructure
end Paper18.Category
