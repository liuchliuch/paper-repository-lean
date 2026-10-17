import Paper18.Category.TannakianDeequivariantFusion
import Paper18.Category.Integrality

/-! # Actual integrality equivalence for Tannakian de-equivariantization -/
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe v u w
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [HasCoequalizers C] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {G : Type} [Group G] [Fintype G] (T : TannakianCenter C G)

/-- The actual dominant free-module tensor functor identifies ambient
integrality with integrality of the actual de-equivariant fusion category. -/
theorem TannakianCenter.deequivariant_integral_iff :
    letI := T.deequivariantRightRigid
    letI := T.deequivariantSimpleUnit S
    S.Integral ↔ (T.deequivariantSkeleton S).Integral := by
  letI := T.deequivariantRightRigid
  letI := T.deequivariantSimpleUnit S
  exact S.integral_iff_of_dominant (T.deequivariantSkeleton S) T.deequivariantFree
    T.deequivariantFree_retract_dominant

/-- The actual Frobenius--Perron dimensions of free de-equivariant
objects are the dimensions of their actual original objects. -/
theorem TannakianCenter.fpdim_deequivariantFree (X : C) :
    letI := T.deequivariantRightRigid
    letI := T.deequivariantSimpleUnit S
    (T.deequivariantSkeleton S).fpdim (T.deequivariantFree.obj X) = S.fpdim X := by
  letI := T.deequivariantRightRigid
  letI := T.deequivariantSimpleUnit S
  exact S.fpdim_map (T.deequivariantSkeleton S) T.deequivariantFree X

end Paper18.Category
