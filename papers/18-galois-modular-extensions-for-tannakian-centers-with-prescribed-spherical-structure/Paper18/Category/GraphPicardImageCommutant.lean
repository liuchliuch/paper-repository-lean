import Paper18.Category.Braided
import Mathlib.CategoryTheory.Monoidal.Center
import Mathlib.CategoryTheory.Retract

/-! # Actual image morphisms commute with the genuine central action

Two actual central actions have opposite crossings, and their underlying
functors are actually naturally isomorphic. Every actual map between
positive image objects therefore commutes with the positive crossing on
all actual retracts of image objects. No fullness is an input.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u v' u'
namespace Paper18.Category.GraphPicard
variable {C : Type u} [Category.{v} C]
  {E : Type u'} [Category.{v'} E] [MonoidalCategory E]
  (A B : C ⥤ Center E)
  (e : B ⋙ Center.forget E ≅ A ⋙ Center.forget E)
  (hc : ∀ X Y : C, Centralizes (A.obj X) (B.obj Y))

include hc in
/-- Naturality of the negative half-braiding gives actual commutation
of every positive-image map against every negative-image object. -/
@[reassoc] theorem image_cross_commutant {X Y : C}
    (f : (A.obj X).1 ⟶ (A.obj Y).1) (Z : C) :
    f ▷ (B.obj Z).1 ≫ ((A.obj Y).2.β (B.obj Z).1).hom =
      ((A.obj X).2.β (B.obj Z).1).hom ≫ (B.obj Z).1 ◁ f := by
  have hX := congrArg Center.Hom.f (hc X Z)
  have hY := congrArg Center.Hom.f (hc Y Z)
  change ((A.obj X).2.β (B.obj Z).1).hom ≫
    ((B.obj Z).2.β (A.obj X).1).hom = 𝟙 _ at hX
  change ((A.obj Y).2.β (B.obj Z).1).hom ≫
    ((B.obj Z).2.β (A.obj Y).1).hom = 𝟙 _ at hY
  apply (cancel_mono ((B.obj Z).2.β (A.obj Y).1).hom).mp
  rw [assoc, hY, comp_id, assoc, (B.obj Z).2.naturality, ← assoc, hX, id_comp]

include e hc in
/-- The actual ordinary natural isomorphism transports this commutation
to every positive image object. Monoidality of that isomorphism is not
needed for this morphism-level fact. -/
@[reassoc] theorem image_self_commutant {X Y : C}
    (f : (A.obj X).1 ⟶ (A.obj Y).1) (Z : C) :
    f ▷ (A.obj Z).1 ≫ ((A.obj Y).2.β (A.obj Z).1).hom =
      ((A.obj X).2.β (A.obj Z).1).hom ≫ (A.obj Z).1 ◁ f := by
  let ez : (B.obj Z).1 ≅ (A.obj Z).1 := e.app Z
  apply (cancel_epi ((A.obj X).1 ◁ ez.hom)).mp
  rw [reassoc_of% (whisker_exchange f ez.hom),
    (A.obj Y).2.naturality ez.hom,
    (A.obj X).2.naturality_assoc ez.hom,
    ← whisker_exchange ez.hom f,
    image_cross_commutant_assoc A B hc f Z]

include e hc in
/-- Actual retract dominance extends the genuine commutation equation
from image objects to every object of their summand closure. -/
@[reassoc] theorem image_retract_commutant {X Y : C}
    (f : (A.obj X).1 ⟶ (A.obj Y).1) (Z : C) {V : E}
    (r : Retract V (A.obj Z).1) :
    f ▷ V ≫ ((A.obj Y).2.β V).hom =
      ((A.obj X).2.β V).hom ≫ V ◁ f := by
  let rr := r.map (tensorRight (A.obj Y).1)
  apply (cancel_mono rr.i).mp
  change (f ▷ V ≫ ((A.obj Y).2.β V).hom) ≫ r.i ▷ (A.obj Y).1 =
    (((A.obj X).2.β V).hom ≫ V ◁ f) ≫ r.i ▷ (A.obj Y).1
  simp only [assoc]
  rw [← (A.obj Y).2.naturality, ← whisker_exchange_assoc,
    image_self_commutant A B e hc f Z, whisker_exchange r.i f,
    (A.obj X).2.naturality_assoc]

end Paper18.Category.GraphPicard
