import Paper18.Category.ModuleFunctorSemisimpleSeparableSkeleton
import Paper18.Category.InternalModuleAmbientActionLinear
import Paper18.Category.ModuleFunctorFiniteInternalHomRightModulesBasic
import Paper18.Category.SeparableModulesSemisimple

/-! # Actual finite semisimple bimodules over a separable algebra

The two algebra actions are native module structures. Separability of
the right algebra follows by reversing the actual bimodule section.
The finite simple skeleton is obtained by iterating actual separable
averaging and actual free-module generation.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalOpposite
open scoped MonObj
universe v u w
namespace Paper18.Category.ModuleFunctor
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  {R : D} [MonObj R]

/-- The same actual bimodule section is separable in the monoidal opposite. -/
def separableMop (S : SeparableAlgebra R) : SeparableAlgebra (mop R) where
  section_ := S.section_.mop
  section_mul := by apply Quiver.Hom.unmop_inj; exact S.section_mul
  left_linear := by apply Quiver.Hom.unmop_inj; exact S.right_linear
  right_linear := by apply Quiver.Hom.unmop_inj; exact S.left_linear

attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

/-- Actual bimodules: the right action is a module action inside the
category of actual left modules. -/
abbrev Bimodules (R : D) [MonObj R] := Mod_ (Mod_ D R) (mop R)

variable [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [CategoryTheory.Limits.HasKernels D] [CategoryTheory.Limits.HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  (S : SeparableAlgebra R) {ι : Type w} [Fintype ι]
  (T : FiniteSemisimpleSkeleton D ι)

/-- The derived finite set of actual simple bimodule classes. -/
abbrev BimoduleSimpleIndex := SeparableAction.SimpleIndex (separableMop S) (S.skeleton T)

/-- Finite semisimplicity of actual bimodules is derived from the two
actual separable splittings; it uses no pivotal structure or braiding. -/
def bimoduleSkeleton : FiniteSemisimpleSkeleton (Bimodules R) (BimoduleSimpleIndex S T) :=
  SeparableAction.skeleton (separableMop S) (S.skeleton T)

end Paper18.Category.ModuleFunctor
