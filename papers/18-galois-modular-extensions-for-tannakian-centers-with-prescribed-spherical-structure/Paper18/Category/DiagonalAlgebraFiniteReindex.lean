import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Finite biproduct reindexing across arbitrary index universes -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe v u w w'
namespace Paper18.Category.DiagonalAlgebra
variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Actual finite biproduct reindexing permits the large simple-label
universe to be replaced by a finite ordinal before applying a functor. -/
def biproductReindex {β : Type} {γ : Type w'} [Fintype β]
    (e : β ≃ γ) (f : γ → C) [HasBiproduct f] [HasBiproduct (f ∘ e)] :
    ⨁ (f ∘ e) ≅ ⨁ f where
  hom := biproduct.desc fun b => biproduct.ι f (e b)
  inv := biproduct.lift fun b => biproduct.π f (e b)
  hom_inv_id := by
    classical
    ext b b'
    by_cases h : b' = b
    · subst h; simp
    · have he : e b' ≠ e b := by intro hh; exact h (e.injective hh)
      simp [biproduct.ι_π_ne _ h, biproduct.ι_π_ne _ he]
  inv_hom_id := by
    classical
    ext g g'
    by_cases h : g' = g <;>
      simp [Preadditive.sum_comp, biproduct.lift_desc,
        biproduct.ι_π, comp_dite, Equiv.apply_eq_iff_eq_symm_apply, h]

section Functor
variable {D : Type*} [Category D] [Preadditive D]
  [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  (F : C ⥤ D) [F.Additive]

/-- Actual additive functors preserve finite biproducts with arbitrary
finite index universes, by reindexing through a finite ordinal. -/
def mapFiniteBiproductIso {α : Type w} [Fintype α] (f : α → C)
    [HasBiproduct f] [HasBiproduct (fun a => F.obj (f a))] :
    F.obj (⨁ f) ≅ ⨁ fun a => F.obj (f a) :=
  F.mapIso (biproductReindex (Fintype.equivFin α).symm f).symm ≪≫
    F.mapBiproduct (fun a : Fin (Fintype.card α) => f ((Fintype.equivFin α).symm a)) ≪≫
      biproductReindex (Fintype.equivFin α).symm (fun a => F.obj (f a))
end Functor

end Paper18.Category.DiagonalAlgebra
