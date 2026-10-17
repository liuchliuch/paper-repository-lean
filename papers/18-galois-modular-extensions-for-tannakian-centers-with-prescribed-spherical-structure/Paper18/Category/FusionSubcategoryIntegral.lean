import Paper18.Category.FusionSubcategoryRigid
import Paper18.Category.Integrality

/-! # FP dimensions and integrality in actual full fusion subcategories -/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u w
namespace Paper18.Category.FiniteSemisimpleSkeleton
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (P : ObjectProperty C) [IsAdditiveFullProperty P] [P.IsMonoidal]

/-- FP dimension computed intrinsically in the inherited actual fusion
subcategory, using its derived fusion rules and positive character. -/
def fullSubcategoryFPdim (X : P.FullSubcategory) : ℝ :=
  letI := S.fullSubcategoryHasKernels P
  letI := S.fullSubcategoryRightRigid P
  letI := S.fullSubcategorySimpleUnit P
  (S.fullSubcategorySkeleton P).fpdim X

/-- Intrinsic and ambient FP dimensions coincide, by the actual tensor
inclusion and the derived uniqueness of positive dimension characters. -/
lemma fullSubcategoryFPdim_eq (X : P.FullSubcategory) :
    S.fullSubcategoryFPdim P X = S.fpdim X.obj := by
  letI := S.fullSubcategoryHasKernels P
  letI := S.fullSubcategoryRightRigid P
  letI := S.fullSubcategorySimpleUnit P
  exact ((S.fullSubcategorySkeleton P).fpdim_map S P.ι X).symm

/-- Actual integrality of the inherited full fusion subcategory. -/
def FullSubcategoryIntegral : Prop :=
  letI := S.fullSubcategoryHasKernels P
  letI := S.fullSubcategoryRightRigid P
  letI := S.fullSubcategorySimpleUnit P
  (S.fullSubcategorySkeleton P).Integral

/-- Integrality may be checked using ambient FP dimensions of the actual
simple representatives in the subcategory. -/
lemma fullSubcategoryIntegral_iff : S.FullSubcategoryIntegral P ↔
    ∀ i, P (S.simpleObject i) → ∃ n : ℤ, S.fpdim (S.simpleObject i) = n := by
  letI := S.fullSubcategoryHasKernels P
  letI := S.fullSubcategoryRightRigid P
  letI := S.fullSubcategorySimpleUnit P
  let T := S.fullSubcategorySkeleton P
  have hd (i : {i : ι // P (S.simpleObject i)}) :
      T.fusionBasis.fpdim i = S.fpdim (S.simpleObject i.val) := by
    rw [← T.fpdim_simple]
    exact S.fullSubcategoryFPdim_eq P (T.simpleObject i)
  change T.Integral ↔ _
  rw [T.integral_iff_basis]
  constructor
  · intro h i hi
    simpa only [hd] using h ⟨i, hi⟩
  · intro h i
    rw [hd]
    exact h i.val i.property

/-- Every actual full fusion subcategory of an integral fusion category is
integral, with all inherited structures constructed above. -/
lemma fullSubcategoryIntegral_of_integral (h : S.Integral) : S.FullSubcategoryIntegral P := by
  apply (S.fullSubcategoryIntegral_iff P).mpr
  intro i _
  exact h _ (S.simple i)

end Paper18.Category.FiniteSemisimpleSkeleton
