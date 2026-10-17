import Paper18.Category.BalancedModuleCategoryFreeMaps
import Mathlib.CategoryTheory.Monad.Adjunction

/-! # The actual outer free-forget adjunction and its monad

The right algebra acts in the genuine category of left modules. Its
native free-module Hom equivalence constructs the adjunction; the monad
and all its laws are then supplied by that actual adjunction.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalOpposite MonoidalLeftAction
open scoped MonObj
universe v u
namespace Paper18.Category.BalancedModuleCategory
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  {A B : D} [MonObj A] [MonObj B]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

/-- The native free-module Hom equivalence gives the actual adjunction. -/
def outerFreeForgetAdjunction : (outerFree (A := A) (B := B)) ⊣ Mod_.forget (D := Mod_ D A) (mop B) :=
  Adjunction.mkOfHomEquiv
    { homEquiv M P := (BimoduleRelativeTensor.ExternalFree.homLinearEquiv (A := mop B) M P).toEquiv
      homEquiv_naturality_left_symm {X' X P} f g := by
        apply Mod_.Hom.ext
        change ((mop B) ⊴ₗ (f ≫ g)) ≫ γ[mop B,P.X] =
          ((mop B) ⊴ₗ f) ≫ ((mop B) ⊴ₗ g) ≫ γ[mop B,P.X]
        rw [actionHomRight_comp, assoc]
      homEquiv_naturality_right f g := by
        change BimoduleRelativeTensor.ExternalFree.unit _ ≫ f.hom ≫ g.hom =
          (BimoduleRelativeTensor.ExternalFree.unit _ ≫ f.hom) ≫ g.hom
        exact (assoc _ _ _).symm }

@[simp]
lemma outerFreeForgetAdjunction_unit (M : Mod_ D A) :
    (outerFreeForgetAdjunction (A := A) (B := B)).unit.app M =
      BimoduleRelativeTensor.ExternalFree.unit (A := mop B) M := by
  change BimoduleRelativeTensor.ExternalFree.unit M ≫ 𝟙 _ = _
  exact comp_id _

@[simp]
lemma outerFreeForgetAdjunction_counit (P : BimoduleRelativeTensor.Native A B) :
    (outerFreeForgetAdjunction (A := A) (B := B)).counit.app P =
      ModuleFunctor.SeparableAction.actionHom P := rfl

/-- The actual monad on left A-modules has underlying object M ⊗ B. -/
def outerMonad : Monad (Mod_ D A) := (outerFreeForgetAdjunction (A := A) (B := B)).toMonad

@[simp] lemma outerMonad_obj (M : Mod_ D A) :
    ((outerMonad (A := A) (B := B)).obj M).X = M.X ⊗ B := rfl

@[simp] lemma outerMonad_unit_hom (M : Mod_ D A) :
    ((outerMonad (A := A) (B := B)).η.app M).hom = (ρ_ M.X).inv ≫ M.X ◁ η[B] := by
  change ((outerFreeForgetAdjunction (A := A) (B := B)).unit.app M).hom = _
  rw [outerFreeForgetAdjunction_unit]
  rfl

@[simp] lemma outerMonad_multiplication_hom (M : Mod_ D A) :
    ((outerMonad (A := A) (B := B)).μ.app M).hom =
      (α_ M.X B B).hom ≫ M.X ◁ μ[B] := by
  change (ModuleFunctor.SeparableAction.actionHom
    ((outerFree (A := A) (B := B)).obj M)).hom.hom = _
  rw [ModuleFunctor.SeparableAction.actionHom_hom]
  exact congrArg Mod_.Hom.hom (ModuleFunctor.SeparableAction.free_smul (A := mop B) M)

end Paper18.Category.BalancedModuleCategory
