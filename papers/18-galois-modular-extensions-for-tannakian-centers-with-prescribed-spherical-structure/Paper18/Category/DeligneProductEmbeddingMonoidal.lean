import Paper18.Category.DeligneProductEmbeddingBasic
import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-! # Coherent actual strong monoidal unit-factor embeddings -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory
open scoped TensorProduct
universe v u v' u'
namespace Paper18.Category.DeligneProduct
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]

def rawLeftTensorIso (X Y : C) :
    (rawLeft (D := D)).obj X ⊗ (rawLeft (D := D)).obj Y ≅ (rawLeft (D := D)).obj (X ⊗ Y) :=
  LinearTensor.isoOfPair (Iso.refl _) (λ_ (𝟙_ D))

def rawLeftCoreMonoidal : (rawLeft (C := C) (D := D)).CoreMonoidal where
  εIso := Iso.refl _
  μIso := rawLeftTensorIso
  μIso_hom_natural_left := by
    intro X Y f Z
    change (((f ⊗ₘ 𝟙 Z) ≫ 𝟙 _) ⊗ₜ[ℂ]
      ((𝟙 (𝟙_ D) ⊗ₘ 𝟙 (𝟙_ D)) ≫ (λ_ (𝟙_ D)).hom)) =
        (𝟙 _ ≫ (f ▷ Z)) ⊗ₜ[ℂ] ((λ_ (𝟙_ D)).hom ≫ 𝟙 _)
    simp
  μIso_hom_natural_right := by
    intro X Y Z f
    change (((𝟙 Z ⊗ₘ f) ≫ 𝟙 _) ⊗ₜ[ℂ]
      ((𝟙 (𝟙_ D) ⊗ₘ 𝟙 (𝟙_ D)) ≫ (λ_ (𝟙_ D)).hom)) =
        (𝟙 _ ≫ (Z ◁ f)) ⊗ₜ[ℂ] ((λ_ (𝟙_ D)).hom ≫ 𝟙 _)
    simp
  associativity X Y Z := by
    change (((𝟙 (X ⊗ Y) ⊗ₘ 𝟙 Z) ≫ 𝟙 _ ≫ (α_ X Y Z).hom) ⊗ₜ[ℂ]
      (((λ_ (𝟙_ D)).hom ⊗ₘ 𝟙 (𝟙_ D)) ≫ (λ_ (𝟙_ D)).hom ≫ 𝟙 _)) =
        ((α_ X Y Z).hom ≫ (𝟙 X ⊗ₘ 𝟙 (Y ⊗ Z)) ≫ 𝟙 _) ⊗ₜ[ℂ]
          ((α_ (𝟙_ D) (𝟙_ D) (𝟙_ D)).hom ≫
            (𝟙 (𝟙_ D) ⊗ₘ (λ_ (𝟙_ D)).hom) ≫ (λ_ (𝟙_ D)).hom)
    congr 1
    · simp
    · monoidal
  left_unitality X := by
    change (λ_ X).hom ⊗ₜ[ℂ] (λ_ (𝟙_ D)).hom =
      ((𝟙 (𝟙_ C) ⊗ₘ 𝟙 X) ≫ 𝟙 _ ≫ (λ_ X).hom) ⊗ₜ[ℂ]
        ((𝟙 (𝟙_ D) ⊗ₘ 𝟙 (𝟙_ D)) ≫ (λ_ (𝟙_ D)).hom ≫ 𝟙 _)
    simp
  right_unitality X := by
    change (ρ_ X).hom ⊗ₜ[ℂ] (ρ_ (𝟙_ D)).hom =
      ((𝟙 X ⊗ₘ 𝟙 (𝟙_ C)) ≫ 𝟙 _ ≫ (ρ_ X).hom) ⊗ₜ[ℂ]
        ((𝟙 (𝟙_ D) ⊗ₘ 𝟙 (𝟙_ D)) ≫ (λ_ (𝟙_ D)).hom ≫ 𝟙 _)
    simp [unitors_equal]

instance rawLeft_monoidal : (rawLeft (C := C) (D := D)).Monoidal :=
  (rawLeftCoreMonoidal (C := C) (D := D)).toMonoidal

def rawRightTensorIso (X Y : D) :
    (rawRight (C := C)).obj X ⊗ (rawRight (C := C)).obj Y ≅ (rawRight (C := C)).obj (X ⊗ Y) :=
  LinearTensor.isoOfPair (λ_ (𝟙_ C)) (Iso.refl _)

def rawRightCoreMonoidal : (rawRight (C := C) (D := D)).CoreMonoidal where
  εIso := Iso.refl _
  μIso := rawRightTensorIso
  μIso_hom_natural_left := by
    intro X Y f Z
    change (((𝟙 (𝟙_ C) ⊗ₘ 𝟙 (𝟙_ C)) ≫ (λ_ (𝟙_ C)).hom) ⊗ₜ[ℂ]
      ((f ⊗ₘ 𝟙 Z) ≫ 𝟙 _)) =
        ((λ_ (𝟙_ C)).hom ≫ 𝟙 _) ⊗ₜ[ℂ] (𝟙 _ ≫ (f ▷ Z))
    simp
  μIso_hom_natural_right := by
    intro X Y Z f
    change (((𝟙 (𝟙_ C) ⊗ₘ 𝟙 (𝟙_ C)) ≫ (λ_ (𝟙_ C)).hom) ⊗ₜ[ℂ]
      ((𝟙 Z ⊗ₘ f) ≫ 𝟙 _)) =
        ((λ_ (𝟙_ C)).hom ≫ 𝟙 _) ⊗ₜ[ℂ] (𝟙 _ ≫ (Z ◁ f))
    simp
  associativity X Y Z := by
    change ((((λ_ (𝟙_ C)).hom ⊗ₘ 𝟙 (𝟙_ C)) ≫ (λ_ (𝟙_ C)).hom ≫ 𝟙 _) ⊗ₜ[ℂ]
      ((𝟙 (X ⊗ Y) ⊗ₘ 𝟙 Z) ≫ 𝟙 _ ≫ (α_ X Y Z).hom)) =
        ((α_ (𝟙_ C) (𝟙_ C) (𝟙_ C)).hom ≫
          (𝟙 (𝟙_ C) ⊗ₘ (λ_ (𝟙_ C)).hom) ≫ (λ_ (𝟙_ C)).hom) ⊗ₜ[ℂ]
            ((α_ X Y Z).hom ≫ (𝟙 X ⊗ₘ 𝟙 (Y ⊗ Z)) ≫ 𝟙 _)
    congr 1
    · monoidal
    · simp
  left_unitality X := by
    change (λ_ (𝟙_ C)).hom ⊗ₜ[ℂ] (λ_ X).hom =
      ((𝟙 (𝟙_ C) ⊗ₘ 𝟙 (𝟙_ C)) ≫ (λ_ (𝟙_ C)).hom ≫ 𝟙 _) ⊗ₜ[ℂ]
        ((𝟙 (𝟙_ D) ⊗ₘ 𝟙 X) ≫ 𝟙 _ ≫ (λ_ X).hom)
    simp
  right_unitality X := by
    change (ρ_ (𝟙_ C)).hom ⊗ₜ[ℂ] (ρ_ X).hom =
      ((𝟙 (𝟙_ C) ⊗ₘ 𝟙 (𝟙_ C)) ≫ (λ_ (𝟙_ C)).hom ≫ 𝟙 _) ⊗ₜ[ℂ]
        ((𝟙 X ⊗ₘ 𝟙 (𝟙_ D)) ≫ 𝟙 _ ≫ (ρ_ X).hom)
    simp [unitors_equal]

instance rawRight_monoidal : (rawRight (C := C) (D := D)).Monoidal :=
  (rawRightCoreMonoidal (C := C) (D := D)).toMonoidal

variable [BraidedCategory C] [BraidedCategory D]

instance rawLeft_braided : (rawLeft (C := C) (D := D)).Braided where
  braided X Y := by
    change (𝟙 (X ⊗ Y) ≫ (β_ X Y).hom) ⊗ₜ[ℂ] ((λ_ (𝟙_ D)).hom ≫ 𝟙 _) =
      ((β_ X Y).hom ≫ 𝟙 (Y ⊗ X)) ⊗ₜ[ℂ]
        ((β_ (𝟙_ D) (𝟙_ D)).hom ≫ (λ_ (𝟙_ D)).hom)
    rw [Category.id_comp, Category.comp_id, Category.comp_id, braiding_leftUnitor,
      ← unitors_equal]

instance rawRight_braided : (rawRight (C := C) (D := D)).Braided where
  braided X Y := by
    change ((λ_ (𝟙_ C)).hom ≫ 𝟙 _) ⊗ₜ[ℂ] (𝟙 (X ⊗ Y) ≫ (β_ X Y).hom) =
      ((β_ (𝟙_ C) (𝟙_ C)).hom ≫ (λ_ (𝟙_ C)).hom) ⊗ₜ[ℂ]
        ((β_ X Y).hom ≫ 𝟙 (Y ⊗ X))
    rw [Category.comp_id, Category.id_comp, Category.comp_id, braiding_leftUnitor,
      ← unitors_equal]

end Paper18.Category.DeligneProduct
