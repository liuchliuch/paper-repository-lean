import Paper18.Category.DrinfeldBasic

/-!
# The canonical factorization bifunctor into the Drinfeld center

This is the ordinary bifunctor `(X,Y) ↦ X⁺ ⊗ Y⁻`, with its actual strong
monoidal structure. Its domain here is the ordinary product category. No
equivalence with the center is claimed: the Deligne tensor product and the
nondegenerate factorization theorem require further constructions.
-/
noncomputable section
universe v u
namespace Paper18.Category.Drinfeld

open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory CategoryTheory.Functor.LaxMonoidal

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- The actual canonical factorization bifunctor. -/
def factorizationBifunctor : C × C ⥤ Center C :=
  ((positive C).prod (negative C)) ⋙ tensor (Center C)

instance factorizationBifunctor_monoidal : (factorizationBifunctor C).Monoidal := by
  unfold factorizationBifunctor
  infer_instance

@[simp] lemma factorizationBifunctor_obj (X Y : C) :
    (factorizationBifunctor C).obj (X, Y) =
      (positive C).obj X ⊗ (negative C).obj Y := rfl

@[simp] lemma factorizationBifunctor_obj_fst (X Y : C) :
    ((factorizationBifunctor C).obj (X, Y)).1 = X ⊗ Y := rfl

@[simp] lemma factorizationBifunctor_map_f {X X' Y Y' : C}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    ((factorizationBifunctor C).map
      (show (X, Y) ⟶ (X', Y') from (f, g))).f = f ⊗ₘ g := rfl

/-- Forgetting the factorization bifunctor gives the actual tensor functor. -/
def factorizationForget : factorizationBifunctor C ⋙ Center.forget C ≅ tensor C :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by simp [factorizationBifunctor])

/-- The half-braiding of a factored object, expressed entirely using the
original braiding and associators. -/
lemma factorizationHalfBraiding (X Y U : C) :
    (((factorizationBifunctor C).obj (X, Y)).2.β U).hom =
      (α_ X Y U).hom ≫ (X ◁ (β_ U Y).inv) ≫ (α_ X U Y).inv ≫
        ((β_ X U).hom ▷ Y) ≫ (α_ U X Y).hom := rfl

/-- The underlying tensorator crosses the second factor of the first pair
under the first factor of the second pair. -/
lemma factorizationTensorator (X Y X' Y' : C) :
    (μ (factorizationBifunctor C) (X, Y) (X', Y')).f =
      (tensorμ ((positive C).obj X) ((negative C).obj Y)
        ((positive C).obj X') ((negative C).obj Y')).f := by
  simp [factorizationBifunctor, Functor.LaxMonoidal.comp_μ]

end Paper18.Category.Drinfeld
