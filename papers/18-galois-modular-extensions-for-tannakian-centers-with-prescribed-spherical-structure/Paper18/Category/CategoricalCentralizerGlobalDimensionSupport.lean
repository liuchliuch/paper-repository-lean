import Paper18.Category.CategoricalCentralizerGlobalDimension
import Paper18.Category.SphericalizationGlobalDimensionBasic
import Paper18.Category.FusionSubcategoryPivotal
import Paper18.Category.ModuleBalancingPositive

/-! # Intrinsic squared dimensions of actual full fusion subcategories -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category.FiniteSemisimpleSkeleton
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [Simple (𝟙_ C)] [BraidedCategory C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (P : ObjectProperty C) [IsAdditiveFullProperty P] [P.IsMonoidal]

lemma fullSubcategory_globalDimension_eq (J : PivotalStructure C) :
    (letI := S.fullSubcategoryRightRigid P
     letI := S.fullSubcategoryHasKernels P
     letI := S.fullSubcategorySimpleUnit P
     ((S.fullSubcategoryPivotal P J).pivotalData (S.fullSubcategorySkeleton P)).globalDimension) =
      S.supportGlobalDimension J P := by
  letI := S.fullSubcategoryRightRigid P
  letI := S.fullSubcategoryHasKernels P
  letI := S.fullSubcategorySimpleUnit P
  let T := S.fullSubcategorySkeleton P
  have hd (i : {i : ι // P (S.simpleObject i)}) :
      ((S.fullSubcategoryPivotal P J).pivotalData T).ndim i = (J.pivotalData S).ndim i.val := by
    rw [Paper18.PivotalData.ndim_eq_normSq, Paper18.PivotalData.ndim_eq_normSq]
    have h := (S.fullSubcategory_preservesPivotal P J).rightDim_scalar (T.simpleObject i)
    change J.rightDim (S.simpleObject i.val) =
      (S.fullSubcategoryPivotal P J).rightDim (T.simpleObject i) at h
    exact congrArg (fun z : ℂ => (Complex.normSq z : ℂ)) h.symm
  change (∑ i, ((S.fullSubcategoryPivotal P J).pivotalData T).ndim i) = _
  simp_rw [hd]
  rw [supportGlobalDimension, ← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter (fun i => P (S.simpleObject i)))
    (fun i => by simp) (fun i => (J.pivotalData S).ndim i)).symm

/-- Any actual positive pivotal structure on the full subcategory identifies
its intrinsic squared dimension with its FP dimension; no compatibility with
the ambient pivotal structure is required. -/
lemma supportGlobalDimension_eq_supportFPdim_of_positive (J : PivotalStructure C)
    (K : letI := S.fullSubcategoryRightRigid P; PivotalStructure P.FullSubcategory)
    (hK : letI := S.fullSubcategoryRightRigid P
      letI := S.fullSubcategoryHasKernels P
      letI := S.fullSubcategorySimpleUnit P
      K.Positive) :
    S.supportGlobalDimension J P = (S.supportFPdim P : ℂ) := by
  letI := S.fullSubcategoryRightRigid P
  letI := S.fullSubcategoryHasKernels P
  letI := S.fullSubcategorySimpleUnit P
  rw [← S.fullSubcategory_globalDimension_eq P J,
    (S.fullSubcategoryPivotal P J).globalDimension_pivotalData_eq K (S.fullSubcategorySkeleton P),
    K.globalDimension_eq_totalFPdim_of_positive (S.fullSubcategorySkeleton P) hK,
    S.fullSubcategory_totalFPdim_eq P]

end Paper18.Category.FiniteSemisimpleSkeleton
