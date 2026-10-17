import Paper18.Category.SeparableModules

/-! # Actual separability sections from central separability elements -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped MonObj
universe v u
namespace Paper18.Category.SeparableAlgebra
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {A : C} [MonObj A]

/-- Multiplying the input into the first leg of an actual tensor element. -/
def sectionLeft (e : 𝟙_ C ⟶ A ⊗ A) : A ⟶ A ⊗ A :=
  (ρ_ A).inv ≫ (A ◁ e) ≫ (α_ A A A).inv ≫ (μ[A] ▷ A)

/-- Multiplying the input into the second leg of an actual tensor element. -/
def sectionRight (e : 𝟙_ C ⟶ A ⊗ A) : A ⟶ A ⊗ A :=
  (λ_ A).inv ≫ e ▷ A ≫ (α_ A A A).hom ≫ (A ◁ μ[A])

/-- The left expression is always left linear, by actual associativity. -/
lemma sectionLeft_left_linear (e : 𝟙_ C ⟶ A ⊗ A) :
    μ[A] ≫ sectionLeft e =
      (A ◁ sectionLeft e) ≫ (α_ A A A).inv ≫ (μ[A] ▷ A) := by
  calc
    _ = (ρ_ (A ⊗ A)).inv ≫ (A ⊗ A) ◁ e ≫
        (α_ (A ⊗ A) A A).inv ≫ ((μ[A] ▷ A) ≫ μ[A]) ▷ A := by
      dsimp [sectionLeft]
      rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc,
        associator_inv_naturality_left_assoc, ← comp_whiskerRight]
    _ = _ := by
      rw [MonObj.mul_assoc]
      dsimp [sectionLeft]
      monoidal

/-- The right expression is always right linear, by actual associativity. -/
lemma sectionRight_right_linear (e : 𝟙_ C ⟶ A ⊗ A) :
    μ[A] ≫ sectionRight e =
      (sectionRight e ▷ A) ≫ (α_ A A A).hom ≫ (A ◁ μ[A]) := by
  calc
    _ = (λ_ (A ⊗ A)).inv ≫ e ▷ (A ⊗ A) ≫
        (α_ A A (A ⊗ A)).hom ≫ A ◁ ((A ◁ μ[A]) ≫ μ[A]) := by
      dsimp [sectionRight]
      rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc,
        associator_naturality_right_assoc, ← whiskerLeft_comp]
    _ = _ := by
      rw [MonObj.mul_assoc_flip]
      dsimp [sectionRight]
      monoidal

/-- A normalized actual element gives a section of multiplication. -/
lemma sectionLeft_mul (e : 𝟙_ C ⟶ A ⊗ A) (he : e ≫ μ[A] = η[A]) :
    sectionLeft e ≫ μ[A] = 𝟙 A := by
  dsimp [sectionLeft]
  simp only [assoc]
  rw [MonObj.mul_assoc]
  simp only [Iso.inv_hom_id_assoc]
  rw [← whiskerLeft_comp_assoc, he, MonObj.mul_one]
  simp

/-- Normalization and centrality of the actual element construct a genuine
bimodule splitting of multiplication. -/
def ofElement (e : 𝟙_ C ⟶ A ⊗ A) (he : e ≫ μ[A] = η[A])
    (hc : sectionLeft e = sectionRight e) : SeparableAlgebra A where
  section_ := sectionLeft e
  section_mul := sectionLeft_mul e he
  left_linear := sectionLeft_left_linear e
  right_linear := by
    rw [hc]
    exact sectionRight_right_linear e

/-- Every actual separability section has the required central element. -/
lemma element_central (S : SeparableAlgebra A) :
    sectionLeft S.element = sectionRight S.element :=
  S.element_left.trans S.element_right.symm

end Paper18.Category.SeparableAlgebra
