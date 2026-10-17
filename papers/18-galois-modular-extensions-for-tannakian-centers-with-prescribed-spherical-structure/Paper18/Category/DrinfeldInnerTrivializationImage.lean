import Paper18.Category.DrinfeldInnerTrivializationTransport

/-! # Actual tensor equivalences transport the inner half-braiding equation -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal
open CategoryTheory.Functor.Monoidal
universe v u v' u'
namespace Paper18.Category.DrinfeldInner
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal] [F.IsEquivalence]

/-- The inverse crossing on an actual functor image is obtained by
applying the tensor equivalence to the actual inverse crossing. -/
lemma image_halfBraiding_inv (Z : Center C) (L : C) :
    μ F L Z.1 ≫ F.map (Z.2.β L).inv ≫ δ F Z.1 L =
      (((DrinfeldEquivalence.map F).obj Z).2.β (F.obj L)).inv := by
  apply (cancel_mono (((DrinfeldEquivalence.map F).obj Z).2.β (F.obj L)).hom).mp
  rw [Iso.inv_hom_id]
  change _ ≫ (DrinfeldEquivalence.halfIso F.asEquivalence Z (F.obj L)).hom = _
  rw [DrinfeldEquivalence.halfIso_functor_image F Z L]
  simp only [Category.assoc, δ_μ_assoc, ← F.map_comp_assoc, Iso.inv_hom_id,
    F.map_id, id_comp, μ_δ]

/-- Applying an actual tensor equivalence to an intertwining equation
gives the corresponding equation for its actual lifted center object. -/
lemma imageComponent_intertwines (Z : Center C) (L A : C)
    (γ : L ⊗ Z.1 ⟶ A ⊗ L) (a : A ⟶ Z.1)
    (h : γ ≫ a ▷ L = (Z.2.β L).inv) :
    μ F L Z.1 ≫ F.map γ ≫ δ F A L ≫ F.map a ▷ F.obj L =
      (((DrinfeldEquivalence.map F).obj Z).2.β (F.obj L)).inv := by
  rw [δ_natural_left F a L, ← F.map_comp_assoc, h]
  exact image_halfBraiding_inv F Z L

end Paper18.Category.DrinfeldInner
