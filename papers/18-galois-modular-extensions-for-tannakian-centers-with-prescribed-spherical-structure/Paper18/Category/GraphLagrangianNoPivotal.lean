import Paper18.Category.GraphLagrangianSphericalizationSeparable
import Paper18.Category.DeligneTensorProductMap
import Paper18.Category.GraphLagrangianBasic

/-! # Canonical diagonal and graph separability without a pivotal input

The actual sphericalization forgetful tensor functor supplies an actual
monoidal tensor-product square. Its actual diagonal algebra comparison is
an algebra epimorphism. Descending the mapped sphericalization section
constructs canonical diagonal separability for every braided fusion category.
-/
noncomputable section
set_option maxHeartbeats 2000000
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category
attribute [local instance 2000] RightRigidCategory.rightDual
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)

namespace DiagonalAlgebra
/-- The actual canonical diagonal algebra has an actual bimodule
separability section, without a prescribed or assumed pivotal structure. -/
def canonicalSeparableNoPivotal : SeparableAlgebra (canonicalAlgebra S) :=
  GraphLagrangian.canonicalSeparableViaSphericalization S
    (DeligneTensorProductMap.comparison Sphericalized.forget)
    (DeligneTensorProductMap.comparison_pair Sphericalized.forget)
end DiagonalAlgebra

namespace GraphLagrangian
variable (α : D ⥤ D) [α.Braided] [α.Additive] [α.Linear ℂ] [α.IsEquivalence]

/-- The actual central graph algebra is separable without a pivotal input.
The section is transported from the proved canonical diagonal section. -/
def separableNoPivotal : SeparableAlgebra (algebra S α) :=
  (DiagonalAlgebra.canonicalSeparableNoPivotal S).map (graphFunctor α)

/-- The actual underlying graph algebra in the original category. -/
def underlyingAlgebra : D := (Center.forget D).obj (algebra S α)

instance underlyingAlgebraMonObj : MonObj (underlyingAlgebra S α) :=
  Functor.monObjObj (F := Center.forget D) (algebra S α)

/-- Forgetting the graph algebra's central structure supplies an actual
separable algebra in the original category, without a pivotal input. -/
def underlyingSeparableNoPivotal : SeparableAlgebra (underlyingAlgebra S α) :=
  (separableNoPivotal S α).map (Center.forget D)

end GraphLagrangian
end Paper18.Category
