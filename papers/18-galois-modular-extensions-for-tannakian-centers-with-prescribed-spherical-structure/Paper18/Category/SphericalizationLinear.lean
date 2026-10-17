import Paper18.Category.SphericalizationAction
import Mathlib.CategoryTheory.Linear.Basic

/-! # Actual additive and complex-linear structure of sphericalization -/
noncomputable section
universe v u
namespace Paper18.Category
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
namespace Pivotalized

/-- The commuting actual morphisms form a linear subspace of ambient Hom. -/
def homSubmodule (X Y : Pivotalized C) : Submodule ℂ (X.obj ⟶ Y.obj) where
  carrier := { f | f ≫ Y.phi.hom = X.phi.hom ≫ (doubleDualFunctor C).map f }
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    change f ≫ Y.phi.hom = X.phi.hom ≫ (doubleDualFunctor C).map f at hf
    change g ≫ Y.phi.hom = X.phi.hom ≫ (doubleDualFunctor C).map g at hg
    simp [hf, hg]
  smul_mem' := by
    intro c f hf
    change f ≫ Y.phi.hom = X.phi.hom ≫ (doubleDualFunctor C).map f at hf
    simp [hf]

def homEquivSubmodule (X Y : Pivotalized C) : (X ⟶ Y) ≃ homSubmodule X Y where
  toFun f := ⟨f.hom, f.comm⟩
  invFun f := ⟨f.val, f.property⟩
  left_inv f := by cases f; rfl
  right_inv f := by cases f; rfl

instance (X Y : Pivotalized C) : AddCommGroup (X ⟶ Y) := (homEquivSubmodule X Y).addCommGroup
instance (X Y : Pivotalized C) : Module ℂ (X ⟶ Y) := Equiv.module ℂ (homEquivSubmodule X Y)

@[simp] lemma zero_hom (X Y : Pivotalized C) : (0 : X ⟶ Y).hom = 0 := rfl
@[simp] lemma add_hom {X Y : Pivotalized C} (f g : X ⟶ Y) : (f + g).hom = f.hom + g.hom := rfl
@[simp] lemma smul_hom {X Y : Pivotalized C} (c : ℂ) (f : X ⟶ Y) : (c • f).hom = c • f.hom := rfl

instance preadditive : Preadditive (Pivotalized C) where
  add_comp := by intro X Y Z f g h; apply Hom.ext; simp [Preadditive.add_comp]
  comp_add := by intro X Y Z f g h; apply Hom.ext; simp [Preadditive.comp_add]

instance linear : CategoryTheory.Linear ℂ (Pivotalized C) where
  smul_comp := by intro X Y Z c f g; apply Hom.ext; simp
  comp_smul := by intro X Y Z f c g; apply Hom.ext; simp

def homLinearEquivSubmodule (X Y : Pivotalized C) : (X ⟶ Y) ≃ₗ[ℂ] homSubmodule X Y where
  toEquiv := homEquivSubmodule X Y
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] (X Y : Pivotalized C) :
    FiniteDimensional ℂ (X ⟶ Y) := (homLinearEquivSubmodule X Y).symm.finiteDimensional

instance forget_additive : (forget (C := C)).Additive where
  map_add := by intros; rfl
instance forget_linear : (forget (C := C)).Linear ℂ where
  map_smul _ _ := rfl

instance monoidalPreadditive : MonoidalPreadditive (Pivotalized C) where
  whiskerLeft_zero := by intro X Y Z; apply Hom.ext; simp
  zero_whiskerRight := by intro X Y Z; apply Hom.ext; simp
  whiskerLeft_add := by intro X Y Z f g; apply Hom.ext; simp
  add_whiskerRight := by intro X Y f g Z; apply Hom.ext; simp

instance monoidalLinear : MonoidalLinear ℂ (Pivotalized C) :=
  CategoryTheory.monoidalLinearOfFaithful ℂ forget

end Pivotalized
namespace Sphericalized

instance inclusion_additive : (inclusion (C := C)).Additive :=
  inferInstanceAs (radfordSquareProperty (C := C)).ι.Additive
instance inclusion_linear : (inclusion (C := C)).Linear ℂ :=
  inferInstanceAs ((radfordSquareProperty (C := C)).ι.Linear ℂ)
instance forget_additive : (forget (C := C)).Additive :=
  inferInstanceAs (inclusion ⋙ Pivotalized.forget).Additive
instance forget_linear : (forget (C := C)).Linear ℂ :=
  inferInstanceAs ((inclusion ⋙ Pivotalized.forget).Linear ℂ)

end Sphericalized
end Paper18.Category
