import Paper18.Category.GraphPicardOrbit
import Paper18.Category.ModuleFunctorDualDimensionOrbitTotal

/-! # The actual total FP dimension of the graph orbit dual -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
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

/-- The actual selected graph orbit End category has actual kernels. -/
def graphEndHasKernels : HasKernels
    (ModuleAlphaInduction.End Dᴹᵒᵖ (GraphLagrangian.ModuleOrbit S α)) :=
  (GraphLagrangian.underlyingSeparableNoPivotal S α).orbitEndHasKernels S
    (GraphLagrangian.underlying_id_ne_zero S α)

/-- The actual selected graph orbit End category has finite actual Homs. -/
def graphEndFiniteHom (F G : ModuleAlphaInduction.End Dᴹᵒᵖ
    (GraphLagrangian.ModuleOrbit S α)) : FiniteDimensional ℂ (F ⟶ G) :=
  (GraphLagrangian.underlyingSeparableNoPivotal S α).orbitEndFiniteHom S
    (GraphLagrangian.underlying_id_ne_zero S α) F G

/-- The actual graph orbit End fusion basis, derived from its genuine
finite semisimple skeleton and actual rigid category. -/
def graphEndFusionBasis : FusionBasis (GraphEndSimpleIndex S α) :=
  (GraphLagrangian.underlyingSeparableNoPivotal S α).orbitEndFusionBasis S
    (GraphLagrangian.underlying_id_ne_zero S α)

/-- The graph orbit dual's actual total FP dimension is the ambient
one. This uses the proved block quotient, actual module equivalence and
true connected-dual weighted formula; no pivotal structure or dimension
equality is supplied. -/
theorem graphEnd_totalFPdim :
    (graphEndFusionBasis S α).totalFPdim = S.fusionBasis.totalFPdim :=
  (GraphLagrangian.underlyingSeparableNoPivotal S α).orbitEnd_totalFPdim_fusion S
    (GraphLagrangian.underlying_id_ne_zero S α)

end Paper18.Category.GraphPicard
