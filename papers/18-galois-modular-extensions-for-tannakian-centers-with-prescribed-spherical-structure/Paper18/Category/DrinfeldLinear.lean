import Paper18.Category.DrinfeldBasic
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Data.Complex.Basic

/-!
# Actual linear structure of the Drinfeld center

Central morphisms form a submodule of the underlying Hom space. The forgetful
functor is faithful and linear; finite dimensionality is inherited from the
underlying category. The additive tensor structure is inherited as well.
-/

noncomputable section
universe v u

namespace Paper18.Category.Drinfeld

open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

instance forget_faithful : (Center.forget C).Faithful where
  map_injective h := Center.ext _ _ h

variable [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- The actual subspace of morphisms commuting with every half-braiding. -/
def homSubmodule (X Y : Center C) : Submodule ℂ (X.1 ⟶ Y.1) where
  carrier := {f | ∀ U : C, (f ▷ U) ≫ (Y.2.β U).hom =
    (X.2.β U).hom ≫ (U ◁ f)}
  zero_mem' := by intro U; simp
  add_mem' := by intro f g hf hg U; simp [hf U, hg U]
  smul_mem' := by intro c f hf U; simp [hf U]

/-- Central Hom is identified with its genuine underlying subspace. -/
def homEquivSubmodule (X Y : Center C) : (X ⟶ Y) ≃ homSubmodule X Y where
  toFun f := ⟨f.f, f.comm⟩
  invFun f := ⟨f.val, f.property⟩
  left_inv f := by cases f; rfl
  right_inv f := by cases f; rfl

instance homAddCommGroup (X Y : Center C) : AddCommGroup (X ⟶ Y) :=
  (homEquivSubmodule X Y).addCommGroup

instance homModule (X Y : Center C) : Module ℂ (X ⟶ Y) :=
  Equiv.module ℂ (homEquivSubmodule X Y)

@[simp] lemma zero_f (X Y : Center C) : (0 : X ⟶ Y).f = 0 := rfl
@[simp] lemma add_f {X Y : Center C} (f g : X ⟶ Y) : (f + g).f = f.f + g.f := rfl
@[simp] lemma smul_f {X Y : Center C} (c : ℂ) (f : X ⟶ Y) :
    (c • f).f = c • f.f := rfl

instance preadditive : Preadditive (Center C) where
  add_comp := by intro X Y Z f g h; apply Center.ext; simp [Preadditive.add_comp]
  comp_add := by intro X Y Z f g h; apply Center.ext; simp [Preadditive.comp_add]

instance linear : Linear ℂ (Center C) where
  smul_comp := by intro X Y Z c f g; apply Center.ext; simp
  comp_smul := by intro X Y Z f c g; apply Center.ext; simp

instance forget_additive : (Center.forget C).Additive where
  map_add := by intros; rfl

instance forget_linear : (Center.forget C).Linear ℂ where
  map_smul _ _ := rfl

instance monoidalPreadditive : MonoidalPreadditive (Center C) :=
  monoidalPreadditive_of_faithful (Center.forget C)

instance monoidalLinear : MonoidalLinear ℂ (Center C) :=
  monoidalLinearOfFaithful ℂ (Center.forget C)

/-- The subspace identification is a complex linear equivalence. -/
def homLinearEquivSubmodule (X Y : Center C) :
    (X ⟶ Y) ≃ₗ[ℂ] homSubmodule X Y where
  toEquiv := homEquivSubmodule X Y
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance hom_finiteDimensional [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
    (X Y : Center C) : FiniteDimensional ℂ (X ⟶ Y) :=
  (homLinearEquivSubmodule X Y).symm.finiteDimensional

variable [BraidedCategory C]

instance positive_additive : (positive C).Additive where
  map_add := by intros; ext; rfl

instance positive_linear : (positive C).Linear ℂ where
  map_smul _ _ := by ext; rfl

instance negative_additive : (negative C).Additive where
  map_add := by intros; ext; rfl

instance negative_linear : (negative C).Linear ℂ where
  map_smul _ _ := by ext; rfl

end Paper18.Category.Drinfeld
