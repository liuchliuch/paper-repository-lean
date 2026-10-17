import Mathlib.CategoryTheory.Monoidal.Linear
import Paper18.Category.FiniteCohomologyKillingBasic

/-! # Actual homogeneous tensor data before the pentagon is imposed

These structures record actual objects, morphisms, tensor products and
associators. No module-category realization or obstruction-existence
statement is supplied as a field.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u w
namespace Paper18.Category.GradedQuasiCancellation
variable {C : Type u} [Category.{v} C] [MonoidalCategoryStruct C]

/-- The ordinary tensor and unitor coherence equations, excluding the
pentagon. The associator is an actual natural family of isomorphisms. -/
structure TensorCoherence : Prop where
  tensorHom_def : ∀ {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂),
    f ⊗ₘ g = f ▷ X₂ ≫ Y₁ ◁ g
  id_tensorHom_id : ∀ X₁ X₂ : C, 𝟙 X₁ ⊗ₘ 𝟙 X₂ = 𝟙 (X₁ ⊗ X₂)
  tensorHom_comp_tensorHom :
    ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
      (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂),
      (f₁ ⊗ₘ f₂) ≫ (g₁ ⊗ₘ g₂) = (f₁ ≫ g₁) ⊗ₘ (f₂ ≫ g₂)
  whiskerLeft_id : ∀ X Y : C, X ◁ 𝟙 Y = 𝟙 (X ⊗ Y)
  id_whiskerRight : ∀ X Y : C, 𝟙 X ▷ Y = 𝟙 (X ⊗ Y)
  associator_naturality :
    ∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃),
      ((f₁ ⊗ₘ f₂) ⊗ₘ f₃) ≫ (α_ Y₁ Y₂ Y₃).hom =
        (α_ X₁ X₂ X₃).hom ≫ (f₁ ⊗ₘ (f₂ ⊗ₘ f₃))
  leftUnitor_naturality : ∀ {X Y : C} (f : X ⟶ Y),
    𝟙_ C ◁ f ≫ (λ_ Y).hom = (λ_ X).hom ≫ f
  rightUnitor_naturality : ∀ {X Y : C} (f : X ⟶ Y),
    f ▷ 𝟙_ C ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f
  triangle : ∀ X Y : C,
    (α_ X (𝟙_ C) Y).hom ≫ X ◁ (λ_ Y).hom = (ρ_ X).hom ▷ Y

variable [Preadditive C] [Linear ℂ C]

/-- Bilinearity of the actual tensor maps, stated before a genuine
monoidal category is available. -/
structure TensorLinearity : Prop where
  whiskerLeft_zero : ∀ {X Y Z : C}, X ◁ (0 : Y ⟶ Z) = 0
  zero_whiskerRight : ∀ {X Y Z : C}, (0 : Y ⟶ Z) ▷ X = 0
  whiskerLeft_add : ∀ {X Y Z : C} (f g : Y ⟶ Z), X ◁ (f + g) = X ◁ f + X ◁ g
  add_whiskerRight : ∀ {X Y Z : C} (f g : Y ⟶ Z), (f + g) ▷ X = f ▷ X + g ▷ X
  whiskerLeft_smul : ∀ (X : C) {Y Z : C} (r : ℂ) (f : Y ⟶ Z),
    X ◁ (r • f) = r • (X ◁ f)
  smul_whiskerRight : ∀ (r : ℂ) {Y Z : C} (f : Y ⟶ Z) (X : C),
    (r • f) ▷ X = r • (f ▷ X)

/-- A genuine group grading on a category of homogeneous objects. Distinct
degrees have only the zero linear map. Finite additive completion can later
supply mixed-degree objects. -/
structure HomogeneousGrading (G : Type w) [Group G] where
  degree : C → G
  degree_unit : degree (𝟙_ C) = 1
  degree_tensor : ∀ X Y : C, degree (X ⊗ Y) = degree X * degree Y
  hom_zero : ∀ {X Y : C}, degree X ≠ degree Y → ∀ f : X ⟶ Y, f = 0

/-- Multiplication of an actual categorical isomorphism by a nonzero
complex scalar, with the actual reciprocal inverse. -/
def scalarIso {X Y : C} (s : ℂˣ) (e : X ≅ Y) : X ≅ Y where
  hom := (s : ℂ) • e.hom
  inv := ((s⁻¹ : ℂˣ) : ℂ) • e.inv
  hom_inv_id := by
    simp only [Linear.smul_comp, Linear.comp_smul, smul_smul, Iso.hom_inv_id,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  inv_hom_id := by
    simp only [Linear.smul_comp, Linear.comp_smul, smul_smul, Iso.inv_hom_id,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]

namespace TensorLinearity
variable (T : TensorCoherence (C := C)) (L : TensorLinearity (C := C))
include T L

lemma tensor_zero {W X Y Z : C} (f : W ⟶ X) : f ⊗ₘ (0 : Y ⟶ Z) = 0 := by
  rw [T.tensorHom_def, L.whiskerLeft_zero, comp_zero]

lemma zero_tensor {W X Y Z : C} (f : Y ⟶ Z) : (0 : W ⟶ X) ⊗ₘ f = 0 := by
  rw [T.tensorHom_def, L.zero_whiskerRight, zero_comp]

end TensorLinearity

namespace HomogeneousGrading
variable {G : Type w} [Group G] (P : HomogeneousGrading (C := C) G)

omit [Linear ℂ C] in
lemma degree_eq_of_ne_zero {X Y : C} {f : X ⟶ Y} (hf : f ≠ 0) : P.degree X = P.degree Y := by
  by_contra h
  exact hf (P.hom_zero h f)

end HomogeneousGrading
end Paper18.Category.GradedQuasiCancellation
