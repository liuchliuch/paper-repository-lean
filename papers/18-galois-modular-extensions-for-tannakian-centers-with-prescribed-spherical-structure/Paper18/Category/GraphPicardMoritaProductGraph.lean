import Paper18.Category.GraphPicardMoritaProductModel
import Paper18.Category.GraphLagrangianModuleOrbit
import Paper18.Category.BimoduleRelativeTensorBlockOrbit

/-! # The actual balanced-product model for two chosen graph components

The actual quotient-block algebra of each chosen graph orbit is
constructed from the regular-bimodule summand. The previously constructed
block equivalence supplies the two input categories, without replacing a
chosen orbit by the whole original graph module category.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj
universe v u w
namespace Paper18.Category.GraphPicard.MoritaProduct
attribute [local instance 2000] RightRigidCategory.rightDual
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)
  (α : D ⥤ D) [α.Braided] [α.Additive] [α.Linear ℂ] [α.IsEquivalence]

/-- The actual block algebra selected by the actual simple graph orbit. -/
def graphBlockAlgebra : Mon D :=
  Mon.mk (BimoduleRelativeTensor.BlockOrbit.algebra
    (GraphLagrangian.underlyingSeparableNoPivotal S α) S
    ((GraphLagrangian.underlyingSeparableNoPivotal S α).orbitLabel S
      (GraphLagrangian.underlying_id_ne_zero S α)))

/-- The actual quotient-block section makes the actual graph block
algebra separable. -/
def graphBlockSeparable : SeparableAlgebra (graphBlockAlgebra S α).X :=
  BimoduleRelativeTensor.BlockOrbit.separable
    (GraphLagrangian.underlyingSeparableNoPivotal S α) S
    ((GraphLagrangian.underlyingSeparableNoPivotal S α).orbitLabel S
      (GraphLagrangian.underlying_id_ne_zero S α))

/-- Actual block modules are equivalent to the chosen actual graph
component, rather than to an assumed indecomposable whole module category. -/
def graphBlockEquivalence : LeftModules (graphBlockAlgebra S α) ≌
    GraphLagrangian.ModuleOrbit S α :=
  BimoduleRelativeTensor.BlockOrbit.equivalence
    (GraphLagrangian.underlyingSeparableNoPivotal S α) S
    ((GraphLagrangian.underlyingSeparableNoPivotal S α).orbitLabel S
      (GraphLagrangian.underlying_id_ne_zero S α))

instance graphBlockEquivalence_functor_additive :
    (graphBlockEquivalence S α).functor.Additive := by
  exact BimoduleRelativeTensor.BlockOrbit.equivalence_functorAdditive
    (GraphLagrangian.underlyingSeparableNoPivotal S α) S
    ((GraphLagrangian.underlyingSeparableNoPivotal S α).orbitLabel S
      (GraphLagrangian.underlying_id_ne_zero S α))

instance graphBlockEquivalence_functor_linear :
    (graphBlockEquivalence S α).functor.Linear ℂ := by
  exact BimoduleRelativeTensor.BlockOrbit.equivalence_functorLinear
    (GraphLagrangian.underlyingSeparableNoPivotal S α) S
    ((GraphLagrangian.underlyingSeparableNoPivotal S α).orbitLabel S
      (GraphLagrangian.underlying_id_ne_zero S α))

instance graphBlockEquivalence_inverse_additive :
    (graphBlockEquivalence S α).inverse.Additive :=
  (graphBlockEquivalence S α).inverse_additive

instance graphBlockEquivalence_inverse_linear :
    (graphBlockEquivalence S α).inverse.Linear ℂ :=
  Equivalence.inverseLinear ℂ (graphBlockEquivalence S α)

variable (β : D ⥤ D) [β.Braided] [β.Additive] [β.Linear ℂ] [β.IsEquivalence]

/-- The actual two-sided-module category modelling the balanced product
of the two actual chosen graph components. -/
abbrev GraphModel := Model (graphBlockAlgebra S α) (graphBlockAlgebra S β)

/-- The actual external pair starts on the actual selected graph orbits.
Both block changes and the left/right conversion are actual functors. -/
def graphExternal : GraphLagrangian.ModuleOrbit S α × GraphLagrangian.ModuleOrbit S β ⥤
    GraphModel S α β :=
  (graphBlockEquivalence S α).inverse.prod (graphBlockEquivalence S β).inverse ⋙
    external (graphBlockAlgebra S α) (graphBlockAlgebra S β)

/-- Actual simple labels of the two-sided-module product model. -/
abbrev GraphModelSimpleIndex := ModelSimpleIndex
  (graphBlockAlgebra S α) (graphBlockAlgebra S β)
  (graphBlockSeparable S α) (graphBlockSeparable S β) S

/-- Finite semisimplicity of the actual graph-product model follows
from the actual two graph-block separability sections. -/
def graphModelSkeleton : FiniteSemisimpleSkeleton (GraphModel S α β)
    (GraphModelSimpleIndex S α β) :=
  modelSkeleton (graphBlockAlgebra S α) (graphBlockAlgebra S β)
    (graphBlockSeparable S α) (graphBlockSeparable S β) S

def graphModelHasKernels : HasKernels (GraphModel S α β) :=
  modelHasKernels (graphBlockAlgebra S α) (graphBlockAlgebra S β)

end Paper18.Category.GraphPicard.MoritaProduct
