import Paper18.Category.SphericalizationGlobalDimensionBasic
import Paper18.Category.PositiveMonoidalFunctorEquivariant
import Paper18.Category.SphericalizationGlobalDimensionEquivalence

/-! # Global dimension of sphericalization of an actual positive category -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category.Sphericalized
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [Simple (𝟙_ C)] [BraidedCategory C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (J : PivotalStructure C) (hJ : J.Positive)

/-- An actual positive structure on the original category induces an
actual positive structure on its canonical sphericalization through the
constructed order-two equivariantization equivalence. -/
def inducedPositivePivotal : PivotalStructure (Sphericalized C) :=
  pivotalPullbackMonoidal toEquivariant
    ((sphericalizationAction C).positivePivotal S J hJ)

lemma inducedPositivePivotal_positive : (inducedPositivePivotal S J hJ).Positive := by
  apply pivotalPullbackMonoidal_positive toEquivariant _
    ((sphericalizationAction C).equivariantSkeleton S)
  exact (sphericalizationAction C).positivePivotal_positive S J hJ

include J hJ

/-- The canonical spherical structure has the full squared global dimension,
even though its transparent negative generator has negative dimension. -/
lemma canonical_globalDimension_eq_totalFPdim_of_positive :
    ((pivotalStructure (C := C)).pivotalData (skeleton S)).globalDimension =
      ((skeleton S).fusionBasis.totalFPdim : ℂ) := by
  rw [(pivotalStructure (C := C)).globalDimension_pivotalData_eq
    (inducedPositivePivotal S J hJ) (skeleton S)]
  exact (inducedPositivePivotal S J hJ).globalDimension_eq_totalFPdim_of_positive
    (skeleton S) (inducedPositivePivotal_positive S J hJ)

lemma noPivotalGlobalDimension_eq_totalFPdim_of_positive :
    noPivotalGlobalDimension S = (S.fusionBasis.totalFPdim : ℂ) := by
  unfold noPivotalGlobalDimension
  rw [canonical_globalDimension_eq_totalFPdim_of_positive S J hJ, totalFPdim_eq_twice S]
  push_cast
  ring

end Paper18.Category.Sphericalized
