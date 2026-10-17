import Paper18.Category.GraphLagrangianDimension
import Paper18.Category.Factorization

/-! # Actual separability of a graph algebra from an actual spherical structure -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category.GraphLagrangian
attribute [local instance 2000] RightRigidCategory.rightDual
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)
  (α : D ⥤ D) [α.Braided] [α.Additive] [α.Linear ℂ] [α.IsEquivalence]

/-- The actual graph multiplication is separable when an actual spherical
structure is available: the actual diagonal section and both bimodule laws
are transported by the actual graph tensor functor. -/
def separable (J : PivotalStructure D) (hJ : J.Spherical) :
    SeparableAlgebra (algebra S α) :=
  DiagonalAlgebra.mappedCanonicalSeparable S (graphFunctor α) J hJ

/-- The actual graph functor is an equivalence under actual Müger
nondegeneracy when the actual pivotal construction of the center is available. -/
def graphFunctorIsEquivalence (J : PivotalStructure D)
    (hD : IsNondegenerate (C := D)) : (graphFunctor α).IsEquivalence := by
  letI := DeligneProduct.hasKernels S S
  letI := DeligneProduct.simpleUnit S S
  let P := DeligneProduct.skeleton S S
  letI : (DeligneProduct.map (𝟭 D) α).IsEquivalence :=
    P.isEquivalenceOfTotalFPdimEq P (DeligneProduct.map (𝟭 D) α) rfl
  letI := Drinfeld.factorizationIsEquivalence S J hD
  unfold graphFunctor
  infer_instance

end Paper18.Category.GraphLagrangian
