import Paper18.Category.DrinfeldSemisimple
import Paper18.Category.FactorizationEssentialSurjective

/-!
# Genuine Deligne factorization of a nondegenerate braided fusion category

The source is the actual linear Deligne product. Full faithfulness follows
from actual Müger nondegeneracy. The center skeleton is constructed by
central induction and averaging, so the dimension comparison and essential
surjectivity give an actual equivalence with no center-existence premise.
-/
noncomputable section
universe v u w
namespace Paper18.Category.Drinfeld
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι) (J : PivotalStructure C)

/-- Actual essential surjectivity of the canonical Deligne factorization,
using the independently constructed actual finite center skeleton. -/
def factorizationEssSurj (hC : IsNondegenerate (C := C)) :
    (deligneFactorization C).EssSurj :=
  factorizationEssSurjOfCenterSkeleton S J (centerSkeleton S J) hC

/-- The canonical Deligne factorization is an actual equivalence. -/
def factorizationIsEquivalence (hC : IsNondegenerate (C := C)) :
    (deligneFactorization C).IsEquivalence :=
  factorizationIsEquivalenceOfCenterSkeleton S J (centerSkeleton S J) hC

/-- The genuine factorization equivalence. Its forward functor sends a
pair to the tensor product of the positive and negative central embeddings,
and extends bilinearly and additively over the actual Deligne product. -/
def factorizationEquivalence (hC : IsNondegenerate (C := C)) :
    DeligneProduct C C ≌ Center C :=
  factorizationEquivalenceOfCenterSkeleton S J (centerSkeleton S J) hC

@[simp] lemma factorizationEquivalence_functor (hC : IsNondegenerate (C := C)) :
    (factorizationEquivalence S J hC).functor = deligneFactorization C := rfl

end Paper18.Category.Drinfeld
