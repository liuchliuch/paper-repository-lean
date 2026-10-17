import Paper18.Category.SphericalizationGlobalDimensionSubcategory
import Paper18.Category.SphericalizationCentralizerDimension
import Paper18.Category.CategoricalCentralizerGlobalDimensionSupport

/-! # Actual positive full supports under sphericalization -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category.Sphericalized
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [Simple (𝟙_ C)] [BraidedCategory C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (P : ObjectProperty C) [IsAdditiveFullProperty P] [P.IsMonoidal]

/-- Positivity of an actual full fusion subcategory induces positivity of
its entire actual inverse image in the canonical sphericalization. -/
theorem exists_positive_preimage
    (J : letI := S.fullSubcategoryRightRigid P; PivotalStructure P.FullSubcategory)
    (hJ : letI := S.fullSubcategoryRightRigid P
      letI := S.fullSubcategoryHasKernels P
      letI := S.fullSubcategorySimpleUnit P
      J.Positive) :
    letI := (skeleton S).fullSubcategoryRightRigid (preimageProperty P)
    letI := (skeleton S).fullSubcategoryHasKernels (preimageProperty P)
    letI := (skeleton S).fullSubcategorySimpleUnit (preimageProperty P)
    ∃ K : PivotalStructure (preimageProperty P).FullSubcategory, K.Positive := by
  letI := S.fullSubcategoryRightRigid P
  letI := S.fullSubcategoryHasKernels P
  letI := S.fullSubcategorySimpleUnit P
  letI := (skeleton S).fullSubcategoryRightRigid (preimageProperty P)
  letI := (skeleton S).fullSubcategoryHasKernels (preimageProperty P)
  letI := (skeleton S).fullSubcategorySimpleUnit (preimageProperty P)
  let T := S.fullSubcategorySkeleton P
  let E := (subcategoryLift S P).asEquivalence
  letI : E.functor.Monoidal := inferInstanceAs (subcategoryLift S P).Monoidal
  letI : E.functor.Additive := inferInstanceAs (subcategoryLift S P).Additive
  letI : E.functor.Linear ℂ := inferInstanceAs ((subcategoryLift S P).Linear ℂ)
  letI : E.inverse.Monoidal := E.inverseMonoidal
  letI : E.inverse.Additive := Equivalence.inverse_additive E
  letI : E.inverse.Linear ℂ := Equivalence.inverseLinear ℂ E
  let L := inducedPositivePivotal T J hJ
  refine ⟨pivotalPullbackMonoidal E.inverse L, ?_⟩
  exact pivotalPullbackMonoidal_positive E.inverse L (skeleton T)
    (inducedPositivePivotal_positive T J hJ)

/-- The actual canonical spherical trace on this full inverse image has
squared global dimension twice the original actual FP support. -/
theorem supportGlobalDimension_preimage_eq_twice_of_positive
    (J : letI := S.fullSubcategoryRightRigid P; PivotalStructure P.FullSubcategory)
    (hJ : letI := S.fullSubcategoryRightRigid P
      letI := S.fullSubcategoryHasKernels P
      letI := S.fullSubcategorySimpleUnit P
      J.Positive) :
    (skeleton S).supportGlobalDimension pivotalStructure (preimageProperty P) =
      2 * (S.supportFPdim P : ℂ) := by
  letI := (skeleton S).fullSubcategoryRightRigid (preimageProperty P)
  letI := (skeleton S).fullSubcategoryHasKernels (preimageProperty P)
  letI := (skeleton S).fullSubcategorySimpleUnit (preimageProperty P)
  obtain ⟨K,hK⟩ := exists_positive_preimage S P J hJ
  rw [(skeleton S).supportGlobalDimension_eq_supportFPdim_of_positive
    (preimageProperty P) pivotalStructure K hK]
  change (((skeleton S).supportFPdim (fun X => P (forget.obj X)) : ℝ) : ℂ) = _
  rw [supportFPdim_preimage_eq_twice S P]
  push_cast
  rfl

end Paper18.Category.Sphericalized
