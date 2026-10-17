import Paper18.Category.DrinfeldNoPivotalDimension
import Paper18.Category.FactorizationFullyFaithful
import Paper18.Category.FactorizationEssentialSurjectiveBasic
import Paper18.Category.FactorizationEssentialSurjectiveProduct
import Paper18.Category.FactorizationDeligneMonoidal

/-! # Actual nondegenerate factorization without pivotal data -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u w
namespace Paper18.Category.Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)

/-- The actual canonical factorization is essentially surjective by
actual full faithfulness and the proved actual center dimension square. -/
def factorizationEssSurjNoPivotal (hD : IsNondegenerate (C := D)) :
    (deligneFactorization D).EssSurj := by
  letI := DeligneProduct.hasKernels S S
  letI := DeligneProduct.simpleUnit S S
  letI := (deligneFactorizationFullyFaithful S hD).full
  letI := (deligneFactorizationFullyFaithful S hD).faithful
  apply (DeligneProduct.skeleton S S).essSurjOfTotalFPdimEq
    (DrinfeldCoendModules.centerSkeletonNoPivotal S) (deligneFactorization D)
  rw [DeligneProduct.totalFPdim_product,
    DrinfeldCoendModules.constructed_center_totalFPdim_noPivotal S, pow_two]

/-- Actual factorization is an equivalence without a pivotal assumption
or an externally supplied center semisimplicity assertion. -/
def factorizationIsEquivalenceNoPivotal (hD : IsNondegenerate (C := D)) :
    (deligneFactorization D).IsEquivalence where
  faithful := (deligneFactorizationFullyFaithful S hD).faithful
  full := (deligneFactorizationFullyFaithful S hD).full
  essSurj := factorizationEssSurjNoPivotal S hD

def factorizationEquivalenceNoPivotal (hD : IsNondegenerate (C := D)) :
    DeligneProduct D D ≌ Center D := by
  letI := factorizationIsEquivalenceNoPivotal S hD
  exact (deligneFactorization D).asEquivalence

/-- The constructed equivalence retains the actual strong tensor functor. -/
def factorizationEquivalenceNoPivotalMonoidal (hD : IsNondegenerate (C := D)) :
    (factorizationEquivalenceNoPivotal S hD).functor.Monoidal :=
  inferInstanceAs (deligneFactorization D).Monoidal

end Paper18.Category.Drinfeld
