import Paper18.Category.BimoduleRelativeTensorFunctorCompositionModule
import Paper18.Category.BimoduleRelativeTensorFusion
import Mathlib.CategoryTheory.Monoidal.Opposite

/-! # The actual reversed Eilenberg--Watts tensor comparison -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u
namespace Paper18.Category.BimoduleRelativeTensor
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [HasCoequalizers D] [LeftRigidCategory D] [RightRigidCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
variable (R : D) [MonObj R]

abbrev ModuleEnd := ModuleAlphaInduction.End Dᴹᵒᵖ (Mod_ D R)

/-- Relative tensor has reversed composition order in the actual
endofunctor monoidal convention. -/
def reverseRepresentation : Native R R ⥤ (ModuleEnd R)ᴹᵒᵖ :=
  tensorRepresentation ⋙ mopFunctor (ModuleEnd R)

def bundledCompositionIso (P Q : Native R R) :
    tensorBundled (tensor P Q) ≅
      (tensorBundled Q : ModuleEnd R) ⊗ tensorBundled P :=
  ModuleFunctor.isoMk (tensorCompositionIso P Q)

def bundledUnitIso : (tensorBundled (regular R) : ModuleEnd R) ≅ 𝟙_ (ModuleEnd R) :=
  ModuleFunctor.isoMk (tensorUnitIso R)

local instance nativeMonoidal : MonoidalCategory (Native R R) := monoidal R

/-- The actual tensor comparison before reversing the direction of its
isomorphism: it is exactly the actual quotient associator. -/
def reverseTensorIso (P Q : Native R R) :
    (reverseRepresentation R).obj (P ⊗ Q) ≅
      (reverseRepresentation R).obj P ⊗ (reverseRepresentation R).obj Q :=
  (bundledCompositionIso R P Q).mop

def reverseUnitIso : (reverseRepresentation R).obj (𝟙_ (Native R R)) ≅
    𝟙_ ((ModuleEnd R)ᴹᵒᵖ) := (bundledUnitIso R).mop

end Paper18.Category.BimoduleRelativeTensor
