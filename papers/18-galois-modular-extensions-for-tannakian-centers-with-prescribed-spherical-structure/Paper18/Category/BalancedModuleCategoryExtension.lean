import Paper18.Category.BalancedModuleCategoryActionAssociativity
import Paper18.Category.BalancedModuleCategoryAlgebras
import Paper18.Category.BalancedModuleCategoryMonadDescent

/-! # Actual object extension obtained from balancing and coequalizers

The monad action laws are theorems derived from balancing. The extension
below is therefore defined from a balanced functor itself, rather than
from an assumed extension or a universal-property certificate.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
open MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u vE uE
namespace Paper18.Category.BalancedModuleCategory
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  {A B : D} [MonObj A] [MonObj B]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
variable {E : Type uE} [Category.{vE} E]
namespace BalancedFunctor
variable (F : BalancedFunctor (A := A) (B := B) E)

/-- An actual right monad module derived entirely from the balancing. -/
def rightMonadModule : RightMonadModule (E := E) (outerMonad (A := A) (B := B)) where
  toFunctor := F.regularSlice
  action := F.rightActionMap
  unit := F.rightActionMap_unit
  assoc := F.rightActionMap_assoc

variable [HasCoequalizers E]

/-- The constructed extension on actual native bimodules. -/
def extension : BimoduleRelativeTensor.Native A B ⥤ E :=
  toAlgebras ⋙ F.rightMonadModule.descent

/-- The native outer-free object has precisely the actual free monad
algebra structure, including its actual multiplication map. -/
def outerFreeAlgebraIso (M : Mod_ D A) :
    toAlgebraObj ((outerFree (A := A) (B := B)).obj M) ≅
      (Monad.free (outerMonad (A := A) (B := B))).obj M :=
  Monad.Algebra.isoMk (Iso.refl _) (by
    simp only [Iso.refl_hom, Category.comp_id]
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
    apply Mod_.Hom.ext
    change ((outerMonad (A := A) (B := B)).μ.app M).hom =
      γ[mop B, ((outerFree (A := A) (B := B)).obj M).X].hom
    rw [outerMonad_multiplication_hom]
    exact (congrArg Mod_.Hom.hom
      (ModuleFunctor.SeparableAction.free_smul (A := mop B) M)).symm)

/-- The constructed extension agrees with the balanced functor at every
actual outer-free object, not only on selected simple generators. -/
def extensionFreeIso (M : Mod_ D A) :
    F.extension.obj ((outerFree (A := A) (B := B)).obj M) ≅ F.regularSlice.obj M :=
  F.rightMonadModule.descent.mapIso (outerFreeAlgebraIso (B := B) M) ≪≫ F.rightMonadModule.freeIso M

end BalancedFunctor
end Paper18.Category.BalancedModuleCategory
