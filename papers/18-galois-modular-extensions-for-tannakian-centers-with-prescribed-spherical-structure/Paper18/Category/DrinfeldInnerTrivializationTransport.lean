import Paper18.Category.DrinfeldInnerTrivializationProduct

/-! # Actual functor and line comparisons preserve inner trivializations -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u
namespace Paper18.Category.DrinfeldInner
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- An actual comparison of the functor image and conjugating line
transports the actual half-braiding equation, component by component. -/
lemma transportComponent_intertwines (Z : Center C) (A B L N : C)
    (γ : L ⊗ Z.1 ⟶ A ⊗ L) (η : N ⊗ Z.1 ⟶ B ⊗ N)
    (a : A ⟶ B) (r : L ≅ N) (u : B ⟶ Z.1)
    (hγ : r.inv ▷ Z.1 ≫ γ ≫ a ▷ L ≫ B ◁ r.hom = η)
    (hη : η ≫ u ▷ N = (Z.2.β N).inv) :
    γ ≫ (a ≫ u) ▷ L = (Z.2.β L).inv := by
  have he := congrArg (fun q => r.hom ▷ Z.1 ≫ q) hγ
  simp only [Category.assoc, ← comp_whiskerRight_assoc, Iso.hom_inv_id,
    id_whiskerRight, id_comp] at he
  have he' := congrArg (fun q => q ≫ B ◁ r.inv) he
  simp only [Category.assoc, ← whiskerLeft_comp, Iso.hom_inv_id,
    whiskerLeft_id, comp_id] at he'
  simp only [comp_whiskerRight]
  rw [reassoc_of% he', whisker_exchange, reassoc_of% hη,
    reassoc_of% (Drinfeld.halfBraiding_inv_naturality Z.2 r.hom)]
  simp only [← whiskerLeft_comp, Iso.hom_inv_id, whiskerLeft_id, comp_id]

variable (F H : C ⥤ C) [F.Monoidal] [H.Monoidal] [F.IsEquivalence] [H.IsEquivalence]
  (L N : C) (γ : tensorLeft L ≅ F ⋙ tensorRight L)
  (η : tensorLeft N ≅ H ⋙ tensorRight N) (a : F ≅ H) (r : L ≅ N)
  (τH : DrinfeldEquivalence.map H ≅ 𝟭 (Center C))

/-- The actual comparison of the conjugating functor and line transports
the actual half-braiding intertwining equation. -/
lemma transport_intertwines
    (hγ : ∀ X, r.inv ▷ X ≫ γ.hom.app X ≫ a.hom.app X ▷ L ≫ H.obj X ◁ r.hom = η.hom.app X)
    (hH : ∀ Z : Center C, η.hom.app Z.1 ≫ (τH.hom.app Z).f ▷ N = (Z.2.β N).inv)
    (Z : Center C) :
    γ.hom.app Z.1 ≫ (a.hom.app Z.1 ≫ (τH.hom.app Z).f) ▷ L = (Z.2.β L).inv :=
  transportComponent_intertwines Z (F.obj Z.1) (H.obj Z.1) L N
    (γ.hom.app Z.1) (η.hom.app Z.1) (a.hom.app Z.1) r
    (τH.hom.app Z).f (hγ Z.1) (hH Z)

/-- Uniqueness of the half-braiding intertwiner proves the actual
comparison law between the resulting center trivializations. -/
lemma trivialization_transport (E : TensorInverse L)
    (τF : DrinfeldEquivalence.map F ≅ 𝟭 (Center C))
    (hγ : ∀ X, r.inv ▷ X ≫ γ.hom.app X ≫ a.hom.app X ▷ L ≫ H.obj X ◁ r.hom = η.hom.app X)
    (hF : ∀ Z : Center C, γ.hom.app Z.1 ≫ (τF.hom.app Z).f ▷ L = (Z.2.β L).inv)
    (hH : ∀ Z : Center C, η.hom.app Z.1 ≫ (τH.hom.app Z).f ▷ N = (Z.2.β N).inv)
    (Z : Center C) :
    a.hom.app Z.1 ≫ (τH.hom.app Z).f = (τF.hom.app Z).f :=
  intertwining_unique F L γ E Z _ _
    (transport_intertwines F H L N γ η a r τH hγ hH Z) (hF Z)

end Paper18.Category.DrinfeldInner
