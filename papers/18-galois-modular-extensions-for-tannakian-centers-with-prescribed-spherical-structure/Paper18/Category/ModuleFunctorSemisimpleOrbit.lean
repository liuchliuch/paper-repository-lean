import Paper18.Category.ModuleFunctorSemisimpleComponent
import Paper18.Category.ModuleFunctorSemisimpleComponentUnit
import Paper18.Category.ModuleFunctorSemisimpleWatts
import Paper18.Category.SeparableModuleOrbit

/-! # Actual finite semisimple endofunctors on a separable algebra orbit -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u w
namespace Paper18.Category.SeparableAlgebra
variable {D : Type u} [Category.{v} D] [Preadditive D] [Linear ℂ D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  [BraidedCategory D] [RightRigidCategory D]
  {R : D} [MonObj R] (S : SeparableAlgebra R)
  {ι : Type w} [Fintype ι] (T : FiniteSemisimpleSkeleton D ι)
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
attribute [local instance] MonoidalOppositeFusion.rightRigidCategory

/-- Actual simple classes for the endofunctors of any specified actual
simple-orbit component of separable modules. -/
abbrev ModuleComponentEndSimpleIndex (i : S.SimpleIndex T) :=
  ModuleFunctor.ComponentEndSimpleIndex (S.skeleton T) i (ModuleFunctor.braidedWattsEndSkeleton S T)

/-- The actual finite semisimple skeleton of module endofunctors of any
specified actual simple-orbit component. -/
def moduleComponentEndSkeleton (i : S.SimpleIndex T) : FiniteSemisimpleSkeleton
    (ModuleFunctor.Bundled Dᴹᵒᵖ
      (ModuleComponent.Component (C := Dᴹᵒᵖ) (S.skeleton T) i)
      (ModuleComponent.Component (C := Dᴹᵒᵖ) (S.skeleton T) i))
    (S.ModuleComponentEndSimpleIndex T i) :=
  ModuleFunctor.componentEndSkeleton (S.skeleton T) i (ModuleFunctor.braidedWattsEndSkeleton S T)

/-- Actual simple classes for the actual nonempty chosen graph-module orbit. -/
abbrev OrbitEndSimpleIndex (hR : (𝟙 R : R ⟶ R) ≠ 0) :=
  S.ModuleComponentEndSimpleIndex T (S.orbitLabel T hR)

/-- An actual nonzero separable algebra has an actual nonempty orbit
whose module endofunctors have this derived actual finite simple skeleton. -/
def orbitEndSkeleton (hR : (𝟙 R : R ⟶ R) ≠ 0) : FiniteSemisimpleSkeleton
    (ModuleFunctor.Bundled Dᴹᵒᵖ (S.OrbitComponent T hR) (S.OrbitComponent T hR))
    (S.OrbitEndSimpleIndex T hR) := S.moduleComponentEndSkeleton T (S.orbitLabel T hR)

/-- Actual kernels on the orbit module-endofunctor category. -/
def orbitEndHasKernels (hR : (𝟙 R : R ⟶ R) ≠ 0) :
    HasKernels (ModuleAlphaInduction.End Dᴹᵒᵖ (S.OrbitComponent T hR)) := by
  letI := S.orbitHasKernels T hR
  letI : HasEqualizers (S.OrbitComponent T hR) := Preadditive.hasEqualizers_of_hasKernels
  letI : HasFiniteLimits (S.OrbitComponent T hR) :=
    hasFiniteLimits_of_hasEqualizers_and_finite_products
  infer_instance

/-- Actual finite Hom spaces on the orbit module-endofunctor category. -/
def orbitEndFiniteHom (hR : (𝟙 R : R ⟶ R) ≠ 0)
    (F G : ModuleAlphaInduction.End Dᴹᵒᵖ (S.OrbitComponent T hR)) :
    FiniteDimensional ℂ (F ⟶ G) := ModuleFunctor.finiteDimensionalHom (S.orbitSkeleton T hR) F G

/-- The actual right adjoints give actual right duals of the actual
module endofunctors on the chosen nonempty orbit. -/
def orbitEndRightRigid (hR : (𝟙 R : R ⟶ R) ≠ 0) :
    RightRigidCategory (ModuleAlphaInduction.End Dᴹᵒᵖ (S.OrbitComponent T hR)) := by
  letI := S.orbitHasKernels T hR
  exact ModuleFunctor.endRightRigidCategory (S.orbitSkeleton T hR)

/-- The tensor unit on the chosen nonempty actual orbit is actually simple. -/
def orbitEndSimpleUnit (hR : (𝟙 R : R ⟶ R) ≠ 0) :
    Simple (𝟙_ (ModuleAlphaInduction.End Dᴹᵒᵖ (S.OrbitComponent T hR))) :=
  ModuleFunctor.componentEndUnit_simple (S.skeleton T) (S.orbitLabel T hR) (S.orbitEndSkeleton T hR)

end Paper18.Category.SeparableAlgebra
