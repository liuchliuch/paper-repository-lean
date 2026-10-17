import Paper18.Category.SeparableModules
import Paper18.Category.Semisimple
import Mathlib.Algebra.Module.TransferInstance

/-! # Actual complex-linear internal module categories -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory
open scoped MonObj
universe v u
namespace Paper18.Category.InternalModule
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  {A : C} [MonObj A]

/-- Module intertwiners form an actual linear subspace of the ambient Hom. -/
def homSubmodule (M N : Mod_ C A) : Submodule ℂ (M.X ⟶ N.X) where
  carrier := {f | γ[A,M.X] ≫ f = (A ◁ f) ≫ γ[A,N.X]}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    change γ[A,M.X] ≫ f = (A ◁ f) ≫ γ[A,N.X] at hf
    change γ[A,M.X] ≫ g = (A ◁ g) ≫ γ[A,N.X] at hg
    simp [hf, hg, Preadditive.comp_add, Preadditive.add_comp]
  smul_mem' := by
    intro c f hf
    change γ[A,M.X] ≫ f = (A ◁ f) ≫ γ[A,N.X] at hf
    simp [hf]

/-- Actual module morphisms identified with their intertwiner subspace. -/
def homEquivSubmodule (M N : Mod_ C A) : (M ⟶ N) ≃ homSubmodule M N where
  toFun f := ⟨f.hom, IsMod_Hom.smul_hom (A := A) (f := f.hom)⟩
  invFun f := Mod_.Hom.mk' f.val f.property
  left_inv f := by cases f; rfl
  right_inv f := by cases f; rfl

instance (M N : Mod_ C A) : AddCommGroup (M ⟶ N) :=
  (homEquivSubmodule M N).addCommGroup
instance (M N : Mod_ C A) : Module ℂ (M ⟶ N) :=
  Equiv.module ℂ (homEquivSubmodule M N)

@[simp] theorem zero_hom (M N : Mod_ C A) : (0 : M ⟶ N).hom = 0 := rfl
@[simp] theorem add_hom {M N : Mod_ C A} (f g : M ⟶ N) :
    (f + g).hom = f.hom + g.hom := rfl
@[simp] theorem smul_hom {M N : Mod_ C A} (c : ℂ) (f : M ⟶ N) :
    (c • f).hom = c • f.hom := rfl

instance : Preadditive (Mod_ C A) where
  add_comp := by intros; apply Mod_.Hom.ext; simp [Preadditive.add_comp]
  comp_add := by intros; apply Mod_.Hom.ext; simp [Preadditive.comp_add]

instance : CategoryTheory.Linear ℂ (Mod_ C A) where
  smul_comp := by intros; apply Mod_.Hom.ext; simp
  comp_smul := by intros; apply Mod_.Hom.ext; simp

/-- The intertwiner-subspace correspondence preserves the actual linear
structures. -/
def homLinearEquivSubmodule (M N : Mod_ C A) :
    (M ⟶ N) ≃ₗ[ℂ] homSubmodule M N where
  toEquiv := homEquivSubmodule M N
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] (M N : Mod_ C A) :
    FiniteDimensional ℂ (M ⟶ N) :=
  (homLinearEquivSubmodule M N).symm.finiteDimensional

instance forget_additive : (Mod_.forget (D := C) A).Additive where
  map_add := by intros; rfl
instance forget_linear : (Mod_.forget (D := C) A).Linear ℂ where
  map_smul _ _ := rfl

/-- The actual free-module construction as a functor. -/
def freeFunctor : C ⥤ Mod_ C A where
  obj := free A
  map f := freeMap f
  map_id _ := by apply Mod_.Hom.ext; change A ◁ 𝟙 _ = 𝟙 _; simp
  map_comp f g := by
    apply Mod_.Hom.ext
    change A ◁ (f ≫ g) = (A ◁ f) ≫ (A ◁ g)
    exact whiskerLeft_comp A f g

instance freeFunctor_additive : (freeFunctor (A := A)).Additive where
  map_add := by
    intro X Y f g
    apply Mod_.Hom.ext
    change A ◁ (f + g) = (A ◁ f) + (A ◁ g)
    simp

instance freeFunctor_linear : (freeFunctor (A := A)).Linear ℂ where
  map_smul f c := by
    apply Mod_.Hom.ext
    change A ◁ (c • f) = c • (A ◁ f)
    simp

end Paper18.Category.InternalModule
