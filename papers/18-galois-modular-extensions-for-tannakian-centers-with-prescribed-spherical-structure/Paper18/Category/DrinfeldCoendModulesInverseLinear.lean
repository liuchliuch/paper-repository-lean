import Paper18.Category.DrinfeldCoendModulesInverseComparison
import Paper18.Category.DrinfeldLinear

/-! # Linearity of the actual coend-module inverse -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category.DrinfeldCoendModules
attribute [local instance 2000] RightRigidCategory.rightDual
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)

instance fromModules_additive : (fromModules S).Additive where
  map_add := by intro M N f g; apply Center.Hom.ext; rfl

instance fromModules_linear : (fromModules S).Linear ℂ where
  map_smul := by intro M N f c; apply Center.Hom.ext; rfl

end Paper18.Category.DrinfeldCoendModules
