import Paper18.Category.GraphLagrangianModuleOrbit
import Paper18.Category.GraphPicardFaithful
import Paper18.Category.ModuleFunctorSemisimpleOrbit

/-! # The actual fusion category of endomorphisms of the graph component

The component is chosen from an actual simple summand of the actual
regular graph module.  Faithfulness of its two genuine alpha-induction
functors follows from the actual nonzero underlying generator.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u w
namespace Paper18.Category.GraphPicard
attribute [local instance 2000] RightRigidCategory.rightDual
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)
  (α : D ⥤ D) [α.Braided] [α.Additive] [α.Linear ℂ] [α.IsEquivalence]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

/-- The actual two native alpha-induction functors are defined on the
actual simple orbit component of the actual graph module category. -/
abbrev graphPositive :=
  ModuleAlphaInduction.positive Dᴹᵒᵖ (GraphLagrangian.ModuleOrbit S α)
abbrev graphNegative :=
  ModuleAlphaInduction.negative Dᴹᵒᵖ (GraphLagrangian.ModuleOrbit S α)

/-- Actual faithfulness does not require any Azumaya equivalence premise. -/
def graphPositiveFaithful : (graphPositive S α).Faithful :=
  componentPositiveFaithful S (GraphLagrangian.moduleSkeleton S α)
    ((GraphLagrangian.underlyingSeparableNoPivotal S α).orbitLabel S
      (GraphLagrangian.underlying_id_ne_zero S α))

def graphNegativeFaithful : (graphNegative S α).Faithful :=
  componentNegativeFaithful S (GraphLagrangian.moduleSkeleton S α)
    ((GraphLagrangian.underlyingSeparableNoPivotal S α).orbitLabel S
      (GraphLagrangian.underlying_id_ne_zero S α))

/-- The finite actual set of simple module-endofunctors of this actual
component is constructed through actual fully faithful Watts evaluation. -/
abbrev GraphEndSimpleIndex :=
  (GraphLagrangian.underlyingSeparableNoPivotal S α).OrbitEndSimpleIndex S
    (GraphLagrangian.underlying_id_ne_zero S α)

/-- The genuine finite semisimple skeleton of endomorphisms of the graph
component; no semisimplicity or module representation is supplied. -/
def graphEndSkeleton : FiniteSemisimpleSkeleton
    (ModuleAlphaInduction.End Dᴹᵒᵖ (GraphLagrangian.ModuleOrbit S α))
    (GraphEndSimpleIndex S α) :=
  (GraphLagrangian.underlyingSeparableNoPivotal S α).orbitEndSkeleton S
    (GraphLagrangian.underlying_id_ne_zero S α)

def graphEndRightRigid : RightRigidCategory
    (ModuleAlphaInduction.End Dᴹᵒᵖ (GraphLagrangian.ModuleOrbit S α)) :=
  (GraphLagrangian.underlyingSeparableNoPivotal S α).orbitEndRightRigid S
    (GraphLagrangian.underlying_id_ne_zero S α)

def graphEndSimpleUnit : Simple
    (𝟙_ (ModuleAlphaInduction.End Dᴹᵒᵖ (GraphLagrangian.ModuleOrbit S α))) :=
  (GraphLagrangian.underlyingSeparableNoPivotal S α).orbitEndSimpleUnit S
    (GraphLagrangian.underlying_id_ne_zero S α)

end Paper18.Category.GraphPicard
