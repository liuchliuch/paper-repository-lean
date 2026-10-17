import Paper18.Category.FactorizationEssentialSurjectiveBasic
import Paper18.Category.FactorizationEssentialSurjectiveProduct
import Paper18.Category.FactorizationFullyFaithful
import Paper18.Category.FactorizationDeligneMonoidal
import Paper18.Category.DrinfeldDimension
import Paper18.Category.DrinfeldExact
import Paper18.Category.DrinfeldRigid

/-!
# Actual factorization equivalence from an actual center skeleton

The constructed canonical functor is fully faithful by actual nondegeneracy.
Its source has the proved product dimension, and the actual induction
adjunction gives the center's dimension square. The general equal-dimension
theorem then constructs essential surjectivity and an actual equivalence.
The actual center skeleton remains an explicit parameter until its independent
semisimplicity construction is supplied.
-/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w t
namespace Paper18.Category.Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (J : PivotalStructure C)
  {κ : Type t} [Fintype κ] (T : FiniteSemisimpleSkeleton (Center C) κ)
include S J T

/-- Actual Müger nondegeneracy and an actual center skeleton imply actual
essential surjectivity of the canonical Deligne factorization functor. -/
def factorizationEssSurjOfCenterSkeleton (hC : IsNondegenerate (C := C)) :
    (deligneFactorization C).EssSurj := by
  letI := DeligneProduct.hasKernels S S
  letI := DeligneProduct.simpleUnit S S
  letI := (deligneFactorizationFullyFaithful S hC).full
  letI := (deligneFactorizationFullyFaithful S hC).faithful
  apply (DeligneProduct.skeleton S S).essSurjOfTotalFPdimEq T (deligneFactorization C)
  rw [DeligneProduct.totalFPdim_product, center_totalFPdim S J T, pow_two]

/-- Full faithfulness and the proved essential surjectivity make the actual
canonical functor an equivalence. -/
def factorizationIsEquivalenceOfCenterSkeleton (hC : IsNondegenerate (C := C)) :
    (deligneFactorization C).IsEquivalence where
  faithful := (deligneFactorizationFullyFaithful S hC).faithful
  full := (deligneFactorizationFullyFaithful S hC).full
  essSurj := factorizationEssSurjOfCenterSkeleton S J T hC

/-- The resulting actual equivalence has the canonical factorization as
its forward functor. The available strong monoidal structure is retained. -/
def factorizationEquivalenceOfCenterSkeleton (hC : IsNondegenerate (C := C)) :
    DeligneProduct C C ≌ Center C := by
  letI := factorizationIsEquivalenceOfCenterSkeleton S J T hC
  exact (deligneFactorization C).asEquivalence

@[simp]
lemma factorizationEquivalenceOfCenterSkeleton_functor (hC : IsNondegenerate (C := C)) :
    (factorizationEquivalenceOfCenterSkeleton S J T hC).functor = deligneFactorization C := rfl

end Paper18.Category.Drinfeld
