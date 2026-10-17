import Paper18.Category.ModuleFunctorFiniteContraction
import Mathlib.CategoryTheory.Monoidal.Center

/-! # The actual normalized matrix-action contraction diagram

This is a generic monoidal diagram: the cup is an actual section of the
cap. No braiding, rigidity or pivotal structure is assumed in the diagram.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u
namespace Paper18.Category.ModuleAlphaInduction
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  {n p A B : D}

/-- The actual matrix action associated to a cap, on the object n. -/
def capAction (cap : p ⊗ n ⟶ 𝟙_ D) : (n ⊗ p) ⊗ n ⟶ n :=
  (α_ n p n).hom ≫ n ◁ cap ≫ (ρ_ n).hom

/-- Insert an actual reversed cup between the two actual tensor factors. -/
def cupInsertion (cup : 𝟙_ D ⟶ p ⊗ n) (A : D) :
    n ⊗ A ⟶ (n ⊗ p) ⊗ (n ⊗ A) :=
  (ρ_ n).inv ▷ A ≫ (n ◁ cup) ▷ A ≫
    (α_ n p n).inv ▷ A ≫ (α_ (n ⊗ p) n A).hom

/-- A normalized cup makes the actual matrix action retract insertion. -/
@[reassoc] theorem cupInsertion_capAction
    (cup : 𝟙_ D ⟶ p ⊗ n) (cap : p ⊗ n ⟶ 𝟙_ D)
    (h : cup ≫ cap = 𝟙 (𝟙_ D)) (A : D) :
    cupInsertion cup A ≫ (α_ (n ⊗ p) n A).inv ≫ capAction cap ▷ A = 𝟙 (n ⊗ A) := by
  calc
    _ = (ρ_ n).inv ▷ A ≫ (n ◁ (cup ≫ cap)) ▷ A ≫ (ρ_ n).hom ▷ A := by
      dsimp only [cupInsertion, capAction]
      monoidal
    _ = _ := by rw [h]; simp

/-- Closing the actual matrix action after an arbitrary actual morphism
is the actual left partial contraction. This is a monoidal coherence identity. -/
@[reassoc] theorem cupInsertion_capAction_closure
    (cup : 𝟙_ D ⟶ p ⊗ n) (cap : p ⊗ n ⟶ 𝟙_ D)
    (g : n ⊗ A ⟶ n ⊗ B) :
    cupInsertion cup A ≫ (n ⊗ p) ◁ g ≫
      (α_ (n ⊗ p) n B).inv ≫ capAction cap ▷ B =
        n ◁ ModuleFunctor.leftClosure cup cap g := by
  dsimp only [cupInsertion, capAction, ModuleFunctor.leftClosure]
  monoidal

/-- The genuine matrix-action intertwiner equation forces an actual
morphism to be the left tensor of its normalized actual partial contraction. -/
theorem eq_whiskerLeft_leftClosure_of_capAction
    (cup : 𝟙_ D ⟶ p ⊗ n) (cap : p ⊗ n ⟶ 𝟙_ D)
    (hnorm : cup ≫ cap = 𝟙 (𝟙_ D)) (g : n ⊗ A ⟶ n ⊗ B)
    (h : (α_ (n ⊗ p) n A).inv ≫ capAction cap ▷ A ≫ g =
      (n ⊗ p) ◁ g ≫ (α_ (n ⊗ p) n B).inv ≫ capAction cap ▷ B) :
    g = n ◁ ModuleFunctor.leftClosure cup cap g := by
  calc
    g = cupInsertion cup A ≫ (α_ (n ⊗ p) n A).inv ≫ capAction cap ▷ A ≫ g := by
      simpa only [Category.assoc, Category.id_comp] using
        (congrArg (fun k => k ≫ g) (cupInsertion_capAction cup cap hnorm A)).symm
    _ = cupInsertion cup A ≫ (n ⊗ p) ◁ g ≫
        (α_ (n ⊗ p) n B).inv ≫ capAction cap ▷ B := by rw [h]
    _ = n ◁ ModuleFunctor.leftClosure cup cap g := cupInsertion_capAction_closure cup cap g

end Paper18.Category.ModuleAlphaInduction
