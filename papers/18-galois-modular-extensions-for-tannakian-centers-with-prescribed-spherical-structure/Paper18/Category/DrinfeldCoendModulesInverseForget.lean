import Paper18.Category.DrinfeldCoendModulesInverseLinear

/-! # The actual coend-module inverse retains the underlying object and morphism -/
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

/-- The inverse functor's underlying functor is exactly the actual
module forgetful functor, on both objects and morphisms. -/
def fromModulesForgetIso :
    fromModules S ⋙ Center.forget D ≅ Mod_.forget (D := D) (algebra S) := Iso.refl _

@[simp] lemma fromModulesForgetIso_hom_app (M : Mod_ D (algebra S)) :
    (fromModulesForgetIso S).hom.app M = 𝟙 M.X := rfl

end Paper18.Category.DrinfeldCoendModules
