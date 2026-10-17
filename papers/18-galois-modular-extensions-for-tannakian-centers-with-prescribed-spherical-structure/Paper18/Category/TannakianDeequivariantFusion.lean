import Paper18.Category.TannakianDeequivariantSemisimple
import Paper18.Category.RelativeTensorFree
import Paper18.Category.DominantRigidity

/-! # The actual fusion structure on Tannakian de-equivariant modules -/
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe v u w
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [HasCoequalizers C]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {G : Type} [Group G] [Fintype G] (T : TannakianCenter C G)

/-- The actual de-equivariant free functor preserves tensor products by the
proved balanced comparison of actual free modules. -/
instance TannakianCenter.deequivariantFreeMonoidal : T.deequivariantFree.Monoidal := by
  dsimp [TannakianCenter.deequivariantFree]
  infer_instance

/-- Right duals of actual de-equivariant modules are constructed by
splitting dual idempotents of actual free-module retracts. -/
def TannakianCenter.deequivariantRightRigid : RightRigidCategory T.Deequivariantization :=
  rightRigidOfDominantOfKernels T.deequivariantFree T.deequivariantFree_retract_dominant

/-- Transparency of the actual regular algebra makes its actual module
category braided under relative tensor product. -/
def TannakianCenter.deequivariantBraided : BraidedCategory T.Deequivariantization :=
  moduleBraidedOfTransparent T.regularAlgebra_transparent

/-- The actual de-equivariant free functor preserves the descended braiding. -/
def TannakianCenter.deequivariantFreeBraided :
    letI := T.deequivariantBraided
    T.deequivariantFree.Braided :=
  RelativeTensor.freeFunctorBraidedOfTransparent T.regularAlgebra_transparent

include S in
/-- Connectedness of the actual regular algebra makes the actual regular
module a simple monoidal unit. -/
theorem TannakianCenter.deequivariantSimpleUnit : Simple (𝟙_ T.Deequivariantization) := by
  apply (T.deequivariantSkeleton S).simple_of_finrank_end_eq_one
  rw [(RelativeTensor.unitEndLinearEquiv (A := T.regularAlgebra)).finrank_eq]
  exact T.regularAlgebra_connected

end Paper18.Category
