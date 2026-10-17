import Paper18.Category.ModuleFunctorSemisimpleSeparableAction
import Paper18.Category.Semisimple
import Mathlib.Algebra.Module.TransferInstance

/-! # Actual linear structure for modules in a native action category -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped MonObj MonoidalLeftAction
universe v u v' u'
namespace Paper18.Category.ModuleFunctor.SeparableAction
open MonoidalLeftAction
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {M : Type u'} [Category.{v'} M] [Preadditive M] [Linear ℂ M]
  [MonoidalLeftAction C M]
  [∀ c : C, (actionLeft M c).Additive]
  [∀ c : C, (actionLeft M c).Linear ℂ]
  {A : C} [MonObj A]

omit [Linear ℂ M] [∀ c : C, (actionLeft M c).Linear ℂ] in
@[simp] lemma action_zero (c : C) (X Y : M) : c ⊴ₗ (0 : X ⟶ Y) = 0 :=
  (actionLeft M c).map_zero X Y
omit [Linear ℂ M] [∀ c : C, (actionLeft M c).Linear ℂ] in
@[simp] lemma action_add (c : C) {X Y : M} (f g : X ⟶ Y) :
    c ⊴ₗ (f + g) = c ⊴ₗ f + c ⊴ₗ g := (actionLeft M c).map_add
omit [∀ c : C, (actionLeft M c).Additive] in
@[simp] lemma action_smul (c : C) {X Y : M} (z : ℂ) (f : X ⟶ Y) :
    c ⊴ₗ (z • f) = z • (c ⊴ₗ f) := (actionLeft M c).map_smul z f

omit [Preadditive M] [Linear ℂ M] [∀ c : C, (actionLeft M c).Additive] [∀ c : C, (actionLeft M c).Linear ℂ] in
@[reassoc]
lemma action_assoc_naturality (c d : C) {X Y : M} (f : X ⟶ Y) :
    ((c ⊗ d) ⊴ₗ f) ≫ (αₗ c d Y).hom =
      (αₗ c d X).hom ≫ (c ⊴ₗ d ⊴ₗ f) := by
  rw [tensor_actionHomRight]
  simp

/-- The actual external intertwiners form a linear subspace. -/
def homSubmodule (X Y : Mod_ M A) : Submodule ℂ (X.X ⟶ Y.X) where
  carrier := {f | γ[A,X.X] ≫ f = (A ⊴ₗ f) ≫ γ[A,Y.X]}
  zero_mem' := by simp
  add_mem' {f g} hf hg := by
    change γ[A,X.X] ≫ f = (A ⊴ₗ f) ≫ γ[A,Y.X] at hf
    change γ[A,X.X] ≫ g = (A ⊴ₗ g) ≫ γ[A,Y.X] at hg
    simp [hf, hg, Preadditive.comp_add, Preadditive.add_comp]
  smul_mem' z f hf := by
    change γ[A,X.X] ≫ f = (A ⊴ₗ f) ≫ γ[A,Y.X] at hf
    simp [hf]

def homEquivSubmodule (X Y : Mod_ M A) : (X ⟶ Y) ≃ homSubmodule X Y where
  toFun f := ⟨f.hom, IsMod_Hom.smul_hom (A := A) (f := f.hom)⟩
  invFun f := Mod_.Hom.mk' f.val f.property
  left_inv f := by cases f; rfl
  right_inv f := by cases f; rfl

instance (priority := 100) homAddCommGroup (X Y : Mod_ M A) : AddCommGroup (X ⟶ Y) :=
  (homEquivSubmodule X Y).addCommGroup
instance (priority := 100) homModule (X Y : Mod_ M A) : Module ℂ (X ⟶ Y) :=
  Equiv.module ℂ (homEquivSubmodule X Y)

@[simp] lemma zero_hom (X Y : Mod_ M A) : (0 : X ⟶ Y).hom = 0 := rfl
@[simp] lemma add_hom {X Y : Mod_ M A} (f g : X ⟶ Y) :
    (f + g).hom = f.hom + g.hom := rfl
@[simp] lemma smul_hom {X Y : Mod_ M A} (z : ℂ) (f : X ⟶ Y) :
    (z • f).hom = z • f.hom := rfl

instance (priority := 100) preadditive : Preadditive (Mod_ M A) where
  add_comp := by intros; apply Mod_.Hom.ext; simp [Preadditive.add_comp]
  comp_add := by intros; apply Mod_.Hom.ext; simp [Preadditive.comp_add]

instance (priority := 100) linear : Linear ℂ (Mod_ M A) where
  smul_comp := by intros; apply Mod_.Hom.ext; simp
  comp_smul := by intros; apply Mod_.Hom.ext; simp

def homLinearEquivSubmodule (X Y : Mod_ M A) :
    (X ⟶ Y) ≃ₗ[ℂ] homSubmodule X Y where
  toEquiv := homEquivSubmodule X Y
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance (priority := 100) finiteDimensionalHom
    [∀ X Y : M, FiniteDimensional ℂ (X ⟶ Y)] (X Y : Mod_ M A) :
    FiniteDimensional ℂ (X ⟶ Y) := (homLinearEquivSubmodule X Y).symm.finiteDimensional

instance (priority := 100) forget_additive : (Mod_.forget (D := M) A).Additive where
  map_add := by intros; rfl
instance (priority := 100) forget_linear : (Mod_.forget (D := M) A).Linear ℂ where
  map_smul _ _ := rfl

instance freeFunctor_additive : (freeFunctor (M := M) (A := A)).Additive where
  map_add := by
    intros; apply Mod_.Hom.ext
    exact (actionLeft M A).map_add
instance freeFunctor_linear : (freeFunctor (M := M) (A := A)).Linear ℂ where
  map_smul f z := by
    apply Mod_.Hom.ext
    exact (actionLeft M A).map_smul z f

end Paper18.Category.ModuleFunctor.SeparableAction
