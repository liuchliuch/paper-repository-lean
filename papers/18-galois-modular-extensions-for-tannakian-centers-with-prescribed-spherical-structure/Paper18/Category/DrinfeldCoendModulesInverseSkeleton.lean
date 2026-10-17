import Paper18.Category.DrinfeldCoendModulesInverseEquivalence
import Paper18.Category.DrinfeldBiproducts
import Paper18.Category.DrinfeldCoendModulesInverseTransport

/-! # Actual finite center semisimplicity from the separable coend, without pivotal data -/
noncomputable section
set_option maxHeartbeats 2000000
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj
universe v u w
namespace Paper18.Category.DrinfeldCoendModules
attribute [local instance 2000] RightRigidCategory.rightDual
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)

/-- The actual equivalence preserves categorical simplicity, by lifting
arbitrary target monomorphisms through its full and faithful functor. -/
lemma fromModules_simple (M : Mod_ D (algebra S)) [Simple M] :
    Simple ((fromModules S).obj M) := SkeletonTransport.simple_image (fromModules S) M

/-- The actual finite simple index inherited from modules over the
proved separable coend algebra. -/
def CenterSimpleIndexNoPivotal := (separable S).SimpleIndex S

instance centerSimpleIndexNoPivotal_fintype : Fintype (CenterSimpleIndexNoPivotal S) := by
  unfold CenterSimpleIndexNoPivotal
  infer_instance

/-- The actual finite semisimple skeleton of the actual center of a
braided fusion category. All objects and decompositions are transported
through the proved coend-module equivalence, without any pivotal input. -/
def centerSkeletonNoPivotal :
    FiniteSemisimpleSkeleton (Center D) (CenterSimpleIndexNoPivotal S) :=
  SkeletonTransport.skeleton (fromModules S) (moduleSkeleton S)

end Paper18.Category.DrinfeldCoendModules
