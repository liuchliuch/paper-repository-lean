import Paper18.Category.Semisimple
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-! # The complex-linear tensor product of two categories

Objects are pairs and Hom spaces are tensor products of actual Hom spaces.
Composition is the bilinear extension of componentwise composition. The
additive envelope of this category is the next step toward the Deligne
product of finite semisimple categories.
-/
noncomputable section
open CategoryTheory
open scoped TensorProduct
universe v u v' u'
namespace Paper18.Category

structure LinearTensor (C : Type u) (D : Type u') where
  left : C
  right : D

namespace LinearTensor
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]

abbrev Hom (X Y : LinearTensor C D) := (X.left ⟶ Y.left) ⊗[ℂ] (X.right ⟶ Y.right)

/-- Composition on actual tensor-product Hom spaces. -/
def compLinear (X Y Z : LinearTensor C D) : Hom X Y →ₗ[ℂ] Hom Y Z →ₗ[ℂ] Hom X Z :=
  TensorProduct.curry
    ((TensorProduct.map
      (TensorProduct.lift (CategoryTheory.Linear.comp X.left Y.left Z.left))
      (TensorProduct.lift (CategoryTheory.Linear.comp X.right Y.right Z.right))).comp
      (TensorProduct.tensorTensorTensorComm ℂ _ _ _ _).toLinearMap)

@[simp] lemma compLinear_tmul (X Y Z : LinearTensor C D)
    (f : X.left ⟶ Y.left) (g : X.right ⟶ Y.right)
    (h : Y.left ⟶ Z.left) (k : Y.right ⟶ Z.right) :
    compLinear X Y Z (f ⊗ₜ[ℂ] g) (h ⊗ₜ[ℂ] k) = (f ≫ h) ⊗ₜ[ℂ] (g ≫ k) := by
  simp [compLinear, CategoryTheory.Linear.comp]

instance : Category (LinearTensor C D) where
  Hom := Hom
  id X := (𝟙 X.left) ⊗ₜ[ℂ] (𝟙 X.right)
  comp {X Y Z} f g := compLinear X Y Z f g
  id_comp {X Y} f := by
    induction f using TensorProduct.induction_on with
    | zero => simp
    | tmul f g => simp
    | add f g hf hg => simp_all
  comp_id {X Y} f := by
    induction f using TensorProduct.induction_on with
    | zero => simp
    | tmul f g => simp
    | add f g hf hg => simp_all
  assoc {X Y Z W} f g h := by
    induction f using TensorProduct.induction_on with
    | zero => simp
    | tmul f₁ f₂ =>
      induction g using TensorProduct.induction_on with
      | zero => simp
      | tmul g₁ g₂ =>
        induction h using TensorProduct.induction_on with
        | zero => simp
        | tmul h₁ h₂ => simp [Category.assoc]
        | add a b ha hb => simp_all
      | add a b ha hb => simp_all
    | add a b ha hb => simp_all

instance (X Y : LinearTensor C D) : AddCommGroup (X ⟶ Y) :=
  inferInstanceAs (AddCommGroup (Hom X Y))
instance (X Y : LinearTensor C D) : Module ℂ (X ⟶ Y) :=
  inferInstanceAs (Module ℂ (Hom X Y))

@[simp] lemma id_def (X : LinearTensor C D) :
    (𝟙 X : X ⟶ X) = (𝟙 X.left) ⊗ₜ[ℂ] (𝟙 X.right) := rfl

@[simp] lemma comp_def {X Y Z : LinearTensor C D} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ g = compLinear X Y Z f g := rfl

instance : Preadditive (LinearTensor C D) where
  add_comp X Y Z f g h := by simp
  comp_add X Y Z f g h := by simp

instance : Linear ℂ (LinearTensor C D) where
  smul_comp X Y Z a f g := by simp
  comp_smul X Y Z f a g := by simp

instance [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
    [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] (X Y : LinearTensor C D) :
    FiniteDimensional ℂ (X ⟶ Y) :=
  inferInstanceAs (FiniteDimensional ℂ (Hom X Y))

/-- The ordinary pairing functor, landing in the linear tensor category.
It is complex-linear in each variable separately. -/
def pairing : C × D ⥤ LinearTensor C D where
  obj X := ⟨X.1, X.2⟩
  map f := f.1 ⊗ₜ[ℂ] f.2
  map_id X := rfl
  map_comp {X Y Z} f g := by
    change (f.1 ≫ g.1) ⊗ₜ[ℂ] (f.2 ≫ g.2) =
      compLinear (⟨X.1, X.2⟩ : LinearTensor C D) ⟨Y.1, Y.2⟩ ⟨Z.1, Z.2⟩
        (f.1 ⊗ₜ[ℂ] f.2) (g.1 ⊗ₜ[ℂ] g.2)
    exact (compLinear_tmul (⟨X.1, X.2⟩ : LinearTensor C D)
      ⟨Y.1, Y.2⟩ ⟨Z.1, Z.2⟩ f.1 f.2 g.1 g.2).symm

end LinearTensor
end Paper18.Category
