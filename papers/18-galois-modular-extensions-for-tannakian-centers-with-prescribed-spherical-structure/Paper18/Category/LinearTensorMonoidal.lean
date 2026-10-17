import Paper18.Category.LinearTensorBasic
import Mathlib.CategoryTheory.Monoidal.Linear

/-! # The actual monoidal structure on the linear tensor category -/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct
universe v u v' u'
namespace Paper18.Category.LinearTensor

section Bilinear
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

def factorTensorLinear (X X' Y Y' : C) :
    (X ⟶ X') →ₗ[ℂ] (Y ⟶ Y') →ₗ[ℂ] (X ⊗ Y ⟶ X' ⊗ Y') where
  toFun f :=
    { toFun := fun g => f ⊗ₘ g
      map_add' := by intros; simp [tensorHom_def]
      map_smul' := by intros; simp [tensorHom_def] }
  map_add' := by intros; ext; simp [tensorHom_def]
  map_smul' := by intros; ext; simp [tensorHom_def]
end Bilinear

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]

def tensorObject (X Y : LinearTensor C D) : LinearTensor C D :=
  ⟨X.left ⊗ Y.left, X.right ⊗ Y.right⟩

def tensorLinear (X Y X' Y' : LinearTensor C D) :
    Hom X X' →ₗ[ℂ] Hom Y Y' →ₗ[ℂ] Hom (tensorObject X Y) (tensorObject X' Y') :=
  TensorProduct.curry
    ((TensorProduct.map
      (TensorProduct.lift (factorTensorLinear X.left X'.left Y.left Y'.left))
      (TensorProduct.lift (factorTensorLinear X.right X'.right Y.right Y'.right))).comp
      (TensorProduct.tensorTensorTensorComm ℂ _ _ _ _).toLinearMap)

@[simp] lemma tensorLinear_tmul (X Y X' Y' : LinearTensor C D)
    (f : X.left ⟶ X'.left) (g : X.right ⟶ X'.right)
    (h : Y.left ⟶ Y'.left) (k : Y.right ⟶ Y'.right) :
    tensorLinear X Y X' Y' (f ⊗ₜ[ℂ] g) (h ⊗ₜ[ℂ] k) =
      (f ⊗ₘ h) ⊗ₜ[ℂ] (g ⊗ₘ k) := by
  rfl

def isoOfPair {X Y : LinearTensor C D} (e : X.left ≅ Y.left) (f : X.right ≅ Y.right) :
    X ≅ Y where
  hom := e.hom ⊗ₜ[ℂ] f.hom
  inv := e.inv ⊗ₜ[ℂ] f.inv
  hom_inv_id := by
    change compLinear X Y X _ _ = _
    rw [compLinear_tmul]
    simp [id_def]
  inv_hom_id := by
    change compLinear Y X Y _ _ = _
    rw [compLinear_tmul]
    simp [id_def]

def monoidalStruct : MonoidalCategoryStruct (LinearTensor C D) where
  tensorObj := tensorObject
  tensorHom := fun {X X' Y Y'} f g => tensorLinear X Y X' Y' f g
  whiskerLeft := fun X {Y Y'} f => tensorLinear X Y X Y' (𝟙 X) f
  whiskerRight := fun {X X'} f Y => tensorLinear X Y X' Y f (𝟙 Y)
  tensorUnit := ⟨𝟙_ C, 𝟙_ D⟩
  associator X Y Z := isoOfPair (α_ X.left Y.left Z.left) (α_ X.right Y.right Z.right)
  leftUnitor X := isoOfPair (λ_ X.left) (λ_ X.right)
  rightUnitor X := isoOfPair (ρ_ X.left) (ρ_ X.right)

attribute [local instance] monoidalStruct

@[simp] lemma tensorHom_def {X Y X' Y' : LinearTensor C D} (f : X ⟶ X') (g : Y ⟶ Y') :
    f ⊗ₘ g = tensorLinear X Y X' Y' f g := rfl

lemma tensorLinear_comp {X Y Z X' Y' Z' : LinearTensor C D}
    (f : X ⟶ Y) (g : X' ⟶ Y') (h : Y ⟶ Z) (k : Y' ⟶ Z') :
    (f ⊗ₘ g) ≫ (h ⊗ₘ k) = (f ≫ h) ⊗ₘ (g ≫ k) := by
  induction f using TensorProduct.induction_on with
  | zero => simp
  | tmul f₁ f₂ =>
    induction g using TensorProduct.induction_on with
    | zero => simp
    | tmul g₁ g₂ =>
      induction h using TensorProduct.induction_on with
      | zero => simp
      | tmul h₁ h₂ =>
        induction k using TensorProduct.induction_on with
        | zero => simp
        | tmul k₁ k₂ =>
          change ((f₁ ⊗ₘ g₁) ≫ (h₁ ⊗ₘ k₁)) ⊗ₜ[ℂ]
            ((f₂ ⊗ₘ g₂) ≫ (h₂ ⊗ₘ k₂)) =
            ((f₁ ≫ h₁) ⊗ₘ (g₁ ≫ k₁)) ⊗ₜ[ℂ] ((f₂ ≫ h₂) ⊗ₘ (g₂ ≫ k₂))
          rw [MonoidalCategory.tensorHom_comp_tensorHom,
            MonoidalCategory.tensorHom_comp_tensorHom]
        | add a b ha hb => simp_all [Preadditive.comp_add]
      | add a b ha hb => simp_all [Preadditive.add_comp]
    | add a b ha hb => simp_all [Preadditive.add_comp, Preadditive.comp_add]
  | add a b ha hb => simp_all [Preadditive.add_comp, Preadditive.comp_add]

lemma associator_natural {X₁ X₂ X₃ Y₁ Y₂ Y₃ : LinearTensor C D}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (h : X₃ ⟶ Y₃) :
    ((f ⊗ₘ g) ⊗ₘ h) ≫ (α_ Y₁ Y₂ Y₃).hom =
      (α_ X₁ X₂ X₃).hom ≫ (f ⊗ₘ (g ⊗ₘ h)) := by
  induction f using TensorProduct.induction_on with
  | zero => simp [monoidalStruct]
  | tmul f₁ f₂ =>
    induction g using TensorProduct.induction_on with
    | zero => simp [monoidalStruct]
    | tmul g₁ g₂ =>
      induction h using TensorProduct.induction_on with
      | zero => simp [monoidalStruct]
      | tmul h₁ h₂ =>
        change (((f₁ ⊗ₘ g₁) ⊗ₘ h₁) ≫ (α_ Y₁.left Y₂.left Y₃.left).hom) ⊗ₜ[ℂ]
          (((f₂ ⊗ₘ g₂) ⊗ₘ h₂) ≫ (α_ Y₁.right Y₂.right Y₃.right).hom) =
          ((α_ X₁.left X₂.left X₃.left).hom ≫ (f₁ ⊗ₘ (g₁ ⊗ₘ h₁))) ⊗ₜ[ℂ]
          ((α_ X₁.right X₂.right X₃.right).hom ≫ (f₂ ⊗ₘ (g₂ ⊗ₘ h₂)))
        rw [CategoryTheory.MonoidalCategory.associator_naturality,
          CategoryTheory.MonoidalCategory.associator_naturality]
      | add a b ha hb => simp_all [Preadditive.add_comp, Preadditive.comp_add]
    | add a b ha hb => simp_all [Preadditive.add_comp, Preadditive.comp_add]
  | add a b ha hb => simp_all [Preadditive.add_comp, Preadditive.comp_add]

instance monoidalCategory : MonoidalCategory (LinearTensor C D) :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := by
      intro X Y
      change ((𝟙 X.left) ⊗ₘ (𝟙 Y.left)) ⊗ₜ[ℂ] ((𝟙 X.right) ⊗ₘ (𝟙 Y.right)) =
        (𝟙 (X.left ⊗ Y.left)) ⊗ₜ[ℂ] (𝟙 (X.right ⊗ Y.right))
      simp)
    (id_tensorHom := by intros; rfl)
    (tensorHom_id := by intros; rfl)
    (tensorHom_comp_tensorHom := tensorLinear_comp)
    (associator_naturality := associator_natural)
    (leftUnitor_naturality := by
      intro X Y f
      induction f using TensorProduct.induction_on with
      | zero => simp [monoidalStruct]
      | tmul f g =>
        change ((𝟙 (𝟙_ C) ⊗ₘ f) ≫ (λ_ Y.left).hom) ⊗ₜ[ℂ]
          ((𝟙 (𝟙_ D) ⊗ₘ g) ≫ (λ_ Y.right).hom) =
          ((λ_ X.left).hom ≫ f) ⊗ₜ[ℂ] ((λ_ X.right).hom ≫ g)
        simp
      | add a b ha hb => simp_all [Preadditive.add_comp, Preadditive.comp_add])
    (rightUnitor_naturality := by
      intro X Y f
      induction f using TensorProduct.induction_on with
      | zero => simp [monoidalStruct]
      | tmul f g =>
        change ((f ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ Y.left).hom) ⊗ₜ[ℂ]
          ((g ⊗ₘ 𝟙 (𝟙_ D)) ≫ (ρ_ Y.right).hom) =
          ((ρ_ X.left).hom ≫ f) ⊗ₜ[ℂ] ((ρ_ X.right).hom ≫ g)
        simp
      | add a b ha hb => simp_all [Preadditive.add_comp, Preadditive.comp_add])
    (pentagon := by
      intro W X Y Z
      change (((α_ W.left X.left Y.left).hom ⊗ₘ 𝟙 Z.left) ≫
        (α_ W.left (X.left ⊗ Y.left) Z.left).hom ≫
        (𝟙 W.left ⊗ₘ (α_ X.left Y.left Z.left).hom)) ⊗ₜ[ℂ]
        (((α_ W.right X.right Y.right).hom ⊗ₘ 𝟙 Z.right) ≫
        (α_ W.right (X.right ⊗ Y.right) Z.right).hom ≫
        (𝟙 W.right ⊗ₘ (α_ X.right Y.right Z.right).hom)) =
        ((α_ (W.left ⊗ X.left) Y.left Z.left).hom ≫
        (α_ W.left X.left (Y.left ⊗ Z.left)).hom) ⊗ₜ[ℂ]
        ((α_ (W.right ⊗ X.right) Y.right Z.right).hom ≫
        (α_ W.right X.right (Y.right ⊗ Z.right)).hom)
      simpa only [tensorHom_id, id_tensorHom] using congrArg₂ (TensorProduct.tmul ℂ)
        (MonoidalCategory.pentagon W.left X.left Y.left Z.left)
        (MonoidalCategory.pentagon W.right X.right Y.right Z.right))
    (triangle := by
      intro X Y
      change ((α_ X.left (𝟙_ C) Y.left).hom ≫
        (𝟙 X.left ⊗ₘ (λ_ Y.left).hom)) ⊗ₜ[ℂ]
        ((α_ X.right (𝟙_ D) Y.right).hom ≫
        (𝟙 X.right ⊗ₘ (λ_ Y.right).hom)) =
        ((ρ_ X.left).hom ⊗ₘ 𝟙 Y.left) ⊗ₜ[ℂ] ((ρ_ X.right).hom ⊗ₘ 𝟙 Y.right)
      simpa only [tensorHom_id, id_tensorHom] using congrArg₂ (TensorProduct.tmul ℂ)
        (MonoidalCategory.triangle X.left Y.left)
        (MonoidalCategory.triangle X.right Y.right))

instance : MonoidalPreadditive (LinearTensor C D) where
  whiskerLeft_zero := by intros; change tensorLinear _ _ _ _ _ 0 = 0; simp
  zero_whiskerRight := by intros; change tensorLinear _ _ _ _ 0 _ = 0; simp
  whiskerLeft_add := by intros; change tensorLinear _ _ _ _ _ (_ + _) = _; simp; rfl
  add_whiskerRight := by intros; change tensorLinear _ _ _ _ (_ + _) _ = _; simp; rfl

instance : MonoidalLinear ℂ (LinearTensor C D) where
  whiskerLeft_smul := by intros; change tensorLinear _ _ _ _ _ (_ • _) = _; simp; rfl
  smul_whiskerRight := by intros; change tensorLinear _ _ _ _ (_ • _) _ = _; simp; rfl

@[simp] lemma whiskerLeft_raw (X : LinearTensor C D) {Y Z : LinearTensor C D}
    (f : Y ⟶ Z) : X ◁ f = tensorLinear X Y X Z (𝟙 X) f := rfl

@[simp] lemma whiskerRight_raw {X Y : LinearTensor C D} (f : X ⟶ Y)
    (Z : LinearTensor C D) : f ▷ Z = tensorLinear X Z Y Z f (𝟙 Z) := rfl

end Paper18.Category.LinearTensor
