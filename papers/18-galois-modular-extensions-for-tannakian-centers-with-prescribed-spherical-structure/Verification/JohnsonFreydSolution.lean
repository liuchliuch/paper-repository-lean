import Paper18.Category.PositiveGaloisExtensionRefinement
import Paper18.Category.TannakianBasic

/-! Independent completed Johnson--Freyd solutions. This module never imports the challenge. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Paper18.Category
universe v u w
namespace P18JohnsonFreyd
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)] [BraidedCategory C]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {G : Type} [Group G]

section LiteralProposition24
universe v' u' w'
variable {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [RightRigidCategory D] [Simple (𝟙_ D)] [BraidedCategory D]
  {κ : Type w'} [Fintype κ] (U : FiniteSemisimpleSkeleton D κ)

include S in
/-- Literal JF Proposition 2.4: source and actual centralizer positivity
imply positivity of the fixed actual nondegenerate ambient category.
No ambient pivotal structure is a premise. -/
theorem proposition2_4 (J : PivotalStructure C) (hJ : J.Positive)
    (F : C ⥤ D) [F.Additive] [F.Linear ℂ] [F.Braided] [F.Full] [F.Faithful]
    (hD : IsNondegenerate (C := D))
    (hcentralizer :
      letI := U.fullSubcategoryHasKernels (centralizerProperty (Set.range F.obj))
      letI := U.fullSubcategoryRightRigid (centralizerProperty (Set.range F.obj))
      letI := U.fullSubcategorySimpleUnit (centralizerProperty (Set.range F.obj))
      ∃ K : PivotalStructure (CentralizerCategory (Set.range F.obj)), K.Positive) :
    ∃ K : PivotalStructure D, K.Positive := by
  letI := U.fullSubcategoryHasKernels (centralizerProperty (Set.range F.obj))
  letI := U.fullSubcategoryRightRigid (centralizerProperty (Set.range F.obj))
  letI := U.fullSubcategorySimpleUnit (centralizerProperty (Set.range F.obj))
  obtain ⟨K, hK⟩ := hcentralizer
  exact U.exists_positive_of_positive_source_centralizer S J hJ F hD K hK

end LiteralProposition24

end P18JohnsonFreyd
