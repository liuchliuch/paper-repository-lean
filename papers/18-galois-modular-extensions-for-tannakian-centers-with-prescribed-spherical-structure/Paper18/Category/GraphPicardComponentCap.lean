import Paper18.Category.GraphPicardComponentTransformation
import Paper18.Category.GraphPicardOrbit

/-! # The actual graph cap comparison on the chosen genuine orbit -/
noncomputable section
set_option maxHeartbeats 2000000
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

/-- The actual raw graph cap transformation restricts to the genuinely
constructed nonempty simple orbit. No orbit or comparison is assumed. -/
def graphOrbitCapComparison :
    α ⋙ Drinfeld.negative D ⋙ rightCentralAction D (GraphLagrangian.ModuleOrbit S α) ⟶
      Drinfeld.positive D ⋙ rightCentralAction D (GraphLagrangian.ModuleOrbit S α) where
  app X := componentCentralHom (GraphLagrangian.moduleSkeleton S α)
    ((GraphLagrangian.underlyingSeparableNoPivotal S α).orbitLabel S
      (GraphLagrangian.underlying_id_ne_zero S α)) ((graphCapComparison S α).app X)
  naturality {X Y} f := by
    apply ModuleFunctor.bundled_hom_ext
    ext m
    exact congrArg (fun t => t.val.app m.obj) ((graphCapComparison S α).naturality f)

end Paper18.Category.GraphPicard
