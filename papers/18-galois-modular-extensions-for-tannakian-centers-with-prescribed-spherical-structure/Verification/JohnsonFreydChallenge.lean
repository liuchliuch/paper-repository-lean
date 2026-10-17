import Paper18.Category.PositiveGaloisExtension
import Paper18.Category.TannakianBasic

/-! Independent contracts for the required Johnson--Freyd existence steps.
Challenge placeholders are isolated here and must never enter production
proofs or production solution import closures.
-/
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

include S in
/-- The required actual braided extension, with no pivotal structure
assumed on either the source or the resulting ambient category. -/
theorem proposition2_3 (T : TannakianCenter C G) :
    Nonempty (GaloisBraidedExtension.{v,u,max u v,max u (v+1),max (max u v) w} C) := by
  sorry

include S in
/-- The required positive refinement, retaining the source's actual
positive pivotal structure on its actual braided embedding. -/
theorem positive_extension (J : PivotalStructure C) (hJ : J.Positive)
    (T : TannakianCenter C G) :
    Nonempty (PositiveGaloisExtension.{v,u,max u v,max u (v+1),max (max u v) w} J) := by
  sorry


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
  sorry

end LiteralProposition24

end P18JohnsonFreyd
