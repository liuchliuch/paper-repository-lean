import Paper18.Category.RelativeTensorFree
import Paper18.Category.SeparableModulesSemisimple
import Paper18.Category.DominantRigidity

/-! # Actual rigidity and simple unit of separable modules -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped MonObj
universe v u w
namespace Paper18.Category.SeparableAlgebra
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [RightRigidCategory C] [HasCoequalizers C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {A : C} [MonObj A] [IsCommMonObj A] (S : SeparableAlgebra A)
  {ι : Type w} [Fintype ι] (T : FiniteSemisimpleSkeleton C ι)

/-- Actual module duals are obtained by splitting the dual idempotents of
actual free-module retracts. -/
def moduleRightRigid : RightRigidCategory (Mod_ C A) :=
  rightRigidOfDominantOfKernels (InternalModule.freeFunctor (A := A)) S.free_retract_dominant

include S T in
/-- Connectedness makes the actual regular module a simple tensor unit. -/
theorem moduleSimpleUnit (hconnected : Module.finrank ℂ (𝟙_ C ⟶ A) = 1) :
    Simple (𝟙_ (Mod_ C A)) := by
  apply (S.skeleton T).simple_of_finrank_end_eq_one
  rw [(RelativeTensor.unitEndLinearEquiv (A := A)).finrank_eq]
  exact hconnected

end Paper18.Category.SeparableAlgebra
