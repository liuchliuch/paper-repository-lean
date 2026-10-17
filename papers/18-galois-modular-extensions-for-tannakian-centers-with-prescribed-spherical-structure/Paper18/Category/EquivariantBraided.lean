import Paper18.Category.EquivariantMonoidal
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-! # Actual braiding on equivariant objects for a braided weak action -/

noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal
universe v u w
namespace Paper18.Category.WeakAction
variable {G : Type w} [Group G] {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] (A : WeakAction G C)
  [∀ g : G, (A.ρ g).Monoidal] [A.IsMonoidal]

/-- A braided weak action: each translating strong monoidal functor
preserves the actual ambient braiding, with its specified tensorator. -/
class IsBraided : Prop where
  braided (g : G) (X Y : C) :
    μ (A.ρ g) X Y ≫ (A.ρ g).map (β_ X Y).hom =
      (β_ ((A.ρ g).obj X) ((A.ρ g).obj Y)).hom ≫ μ (A.ρ g) Y X

variable [A.IsBraided]

/-- The action functors have the standard mathlib braided interface, using
the same monoidal structure as the weak action. -/
instance rho_braided (g : G) : (A.ρ g).Braided where
  toMonoidal := inferInstance
  braided X Y := IsBraided.braided g X Y

namespace Equivariant

/-- The ambient braiding is an actual equivariant isomorphism, because each
translating functor is braided. -/
def braiding (X Y : A.Equivariant) : X ⊗ Y ≅ Y ⊗ X :=
  mkIso A (β_ X.obj Y.obj) (by
    intro g
    change (A.ρ g).map (β_ X.obj Y.obj).hom ≫
      (δ (A.ρ g) Y.obj X.obj ≫ ((Y.structureIso g).hom ⊗ₘ (X.structureIso g).hom)) =
      (δ (A.ρ g) X.obj Y.obj ≫ ((X.structureIso g).hom ⊗ₘ (Y.structureIso g).hom)) ≫
        (β_ X.obj Y.obj).hom
    rw [Functor.map_braiding]
    simp only [Category.assoc]
    erw [Functor.Monoidal.μ_δ_assoc]
    rw [← BraidedCategory.braiding_naturality])

/-- Braiding coherence is inherited through the faithful actual forgetful
functor. -/
instance equivariant_braidedCategory : BraidedCategory A.Equivariant :=
  BraidedCategory.ofFaithful A.forget (braiding A) (by
    intro X Y
    simp only [forget_μ]
    erw [Category.id_comp, Category.comp_id]
    rfl)

end Equivariant

/-- The actual forgetful functor preserves the braiding. -/
instance forget_braided : A.forget.Braided where
  braided X Y := by
    simp only [forget_μ]
    erw [Category.id_comp, Category.comp_id]
    rfl

end Paper18.Category.WeakAction
