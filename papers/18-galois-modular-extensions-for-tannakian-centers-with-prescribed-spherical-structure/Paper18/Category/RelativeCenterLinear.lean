import Paper18.Category.RelativeCenterMonoidal
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

namespace Paper18.Category.RelativeCenter

open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {P : ObjectProperty C} [P.IsMonoidal]

variable [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- The actual subspace of morphisms commuting with every half-braiding. -/
def homSubmodule (X Y : RelativeCenter P) : Submodule ℂ (X.1 ⟶ Y.1) where
  carrier := {f | ∀ (U : C) (hU : P U), (f ▷ U) ≫ (Y.2.β U hU).hom =
    (X.2.β U hU).hom ≫ (U ◁ f)}
  zero_mem' := by intro U hU; simp
  add_mem' := by intro f g hf hg U hU; simp [hf U hU, hg U hU]
  smul_mem' := by intro c f hf U hU; simp [hf U hU]

/-- Central Hom is identified with its genuine underlying subspace. -/
def homEquivSubmodule (X Y : RelativeCenter P) : (X ⟶ Y) ≃ homSubmodule X Y where
  toFun f := ⟨f.f, f.comm⟩
  invFun f := ⟨f.val, f.property⟩
  left_inv f := by cases f; rfl
  right_inv f := by cases f; rfl

instance homAddCommGroup (X Y : RelativeCenter P) : AddCommGroup (X ⟶ Y) :=
  (homEquivSubmodule X Y).addCommGroup

instance homModule (X Y : RelativeCenter P) : Module ℂ (X ⟶ Y) :=
  Equiv.module ℂ (homEquivSubmodule X Y)

@[simp] lemma zero_f (X Y : RelativeCenter P) : (0 : X ⟶ Y).f = 0 := rfl
@[simp] lemma add_f {X Y : RelativeCenter P} (f g : X ⟶ Y) : (f + g).f = f.f + g.f := rfl
@[simp] lemma smul_f {X Y : RelativeCenter P} (c : ℂ) (f : X ⟶ Y) :
    (c • f).f = c • f.f := rfl

instance preadditive : Preadditive (RelativeCenter P) where
  add_comp := by intro X Y Z f g h; apply ext P; simp [Preadditive.add_comp]
  comp_add := by intro X Y Z f g h; apply ext P; simp [Preadditive.comp_add]

instance linear : Linear ℂ (RelativeCenter P) where
  smul_comp := by intro X Y Z c f g; apply ext P; simp
  comp_smul := by intro X Y Z f c g; apply ext P; simp

instance forget_additive : (forget P).Additive where
  map_add := by intros; rfl

instance forget_linear : (forget P).Linear ℂ where
  map_smul _ _ := rfl

instance monoidalPreadditive : MonoidalPreadditive (RelativeCenter P) :=
  monoidalPreadditive_of_faithful (forget P)

instance monoidalLinear : MonoidalLinear ℂ (RelativeCenter P) :=
  monoidalLinearOfFaithful ℂ (forget P)

/-- The subspace identification is a complex linear equivalence. -/
def homLinearEquivSubmodule (X Y : RelativeCenter P) :
    (X ⟶ Y) ≃ₗ[ℂ] homSubmodule X Y where
  toEquiv := homEquivSubmodule X Y
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance hom_finiteDimensional [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
    (X Y : RelativeCenter P) : FiniteDimensional ℂ (X ⟶ Y) :=
  (homLinearEquivSubmodule X Y).symm.finiteDimensional

instance restriction_additive : (restriction P).Additive where
  map_add := by intros; rfl

instance restriction_linear : (restriction P).Linear ℂ where
  map_smul _ _ := rfl

end Paper18.Category.RelativeCenter
