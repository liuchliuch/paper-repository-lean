import Paper18.Category.FusionJoinIntegralBasic
import Paper18.Category.CentralizerJoinImage
import Paper18.Category.FusionSubcategoryIntegral

/-! # Actual integrality of fusion joins -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u w
namespace Paper18.Category.FiniteSemisimpleSkeleton
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (J : PivotalStructure C) (P Q : ObjectProperty C)
  [P.IsMonoidal] [Q.IsMonoidal] [IsAdditiveFullProperty P] [IsAdditiveFullProperty Q]

include J in
/-- The actual fusion join of two integral full fusion subcategories is
integral. The actual strong tensor functor from their actual Deligne
product is retract-dominant; actual Lemma 3.1 transfers integrality. -/
theorem fusionJoinIntegral (hC : IsNondegenerate (C := C))
    (hP : S.FullSubcategoryIntegral P) (hQ : S.FullSubcategoryIntegral Q) :
    S.FullSubcategoryIntegral (fusionJoin P Q) := by
  letI := S.fullSubcategoryHasKernels P
  letI := S.fullSubcategoryRightRigid P
  letI := S.fullSubcategorySimpleUnit P
  letI := S.fullSubcategoryHasKernels Q
  letI := S.fullSubcategoryRightRigid Q
  letI := S.fullSubcategorySimpleUnit Q
  letI := S.fullSubcategoryHasKernels (fusionJoin P Q)
  letI := S.fullSubcategoryRightRigid (fusionJoin P Q)
  letI := S.fullSubcategorySimpleUnit (fusionJoin P Q)
  letI : ∀ X Y : P.FullSubcategory, FiniteDimensional ℂ (X ⟶ Y) :=
    fun X Y => inferInstanceAs (FiniteDimensional ℂ (X.obj ⟶ Y.obj))
  letI : ∀ X Y : Q.FullSubcategory, FiniteDimensional ℂ (X ⟶ Y) :=
    fun X Y => inferInstanceAs (FiniteDimensional ℂ (X.obj ⟶ Y.obj))
  letI : ∀ X Y : (fusionJoin P Q).FullSubcategory, FiniteDimensional ℂ (X ⟶ Y) :=
    fun X Y => inferInstanceAs (FiniteDimensional ℂ (X.obj ⟶ Y.obj))
  let U := S.fullSubcategorySkeleton P
  let V := S.fullSubcategorySkeleton Q
  let W := S.fullSubcategorySkeleton (fusionJoin P Q)
  letI := DeligneProduct.hasKernels U V
  letI := DeligneProduct.simpleUnit U V
  exact (DeligneProduct.skeleton U V).integral_of_dominant W
    (FusionJoin.tensorToJoin P Q) (FusionJoin.tensorToJoin_dominant P Q S J hC)
    (DeligneProduct.integral_of_integral U V hP hQ)

end Paper18.Category.FiniteSemisimpleSkeleton
