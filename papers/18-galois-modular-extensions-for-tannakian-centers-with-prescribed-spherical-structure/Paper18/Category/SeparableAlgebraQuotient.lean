import Paper18.Category.SeparableAlgebraElement

/-! # Separability descends through actual algebra epimorphisms

The actual separability element is pushed through the algebra morphism.
Its centrality descends by epimorphism cancellation. No pivotal structure,
choice of a module splitting, or separability certificate for the quotient
is supplied.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped MonObj
universe v u
namespace Paper18.Category.SeparableAlgebra
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {A B : C} [MonObj A] [MonObj B] (q : A ⟶ B) [IsMonHom q]

/-- Actual transport of the left element expression through multiplication. -/
lemma sectionLeft_map (e : 𝟙_ C ⟶ A ⊗ A) :
    q ≫ sectionLeft (e ≫ (q ⊗ₘ q)) = sectionLeft e ≫ (q ⊗ₘ q) := by
  dsimp only [sectionLeft]
  simp only [assoc]
  rw [← rightUnitor_inv_comp_tensorHom_assoc,
    ← whiskerLeft_comp_tensorHom_assoc,
    associator_inv_naturality_assoc,
    tensorHom_comp_whiskerRight, ← IsMonHom.mul_hom q,
    ← whiskerRight_comp_tensorHom]

/-- Actual transport of the right element expression through multiplication. -/
lemma sectionRight_map (e : 𝟙_ C ⟶ A ⊗ A) :
    q ≫ sectionRight (e ≫ (q ⊗ₘ q)) = sectionRight e ≫ (q ⊗ₘ q) := by
  dsimp only [sectionRight]
  simp only [assoc]
  rw [← leftUnitor_inv_comp_tensorHom_assoc,
    ← whiskerRight_comp_tensorHom_assoc,
    associator_naturality_assoc,
    tensorHom_comp_whiskerLeft, ← IsMonHom.mul_hom q,
    ← whiskerLeft_comp_tensorHom]

/-- Every actual quotient algebra of an actual separable algebra is
separable. This works in any monoidal category. -/
def quotient [Epi q] (S : SeparableAlgebra A) : SeparableAlgebra B :=
  ofElement (S.element ≫ (q ⊗ₘ q)) (by
    rw [assoc, ← IsMonHom.mul_hom q, ← assoc, S.element_mul,
      IsMonHom.one_hom]) (by
    apply (cancel_epi q).mp
    rw [sectionLeft_map, sectionRight_map, S.element_central])

end Paper18.Category.SeparableAlgebra
