import Paper18.Category.DrinfeldInnerTrivializationImage
import Paper18.Category.InvertibleFunctor

/-! # Actual uniqueness proves multiplication and conjugation comparisons -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.Monoidal
universe v u v' u'
namespace Paper18.Category.DrinfeldInner
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Tensor cancellation gives uniqueness for a single actual invertible
intertwiner, independently of how the ambient functor was presented. -/
lemma component_intertwining_unique (Z : Center C) (A L : C)
    (γ : L ⊗ Z.1 ≅ A ⊗ L) (E : TensorInverse L) (a b : A ⟶ Z.1)
    (ha : γ.hom ≫ a ▷ L = (Z.2.β L).inv)
    (hb : γ.hom ≫ b ▷ L = (Z.2.β L).inv) : a = b := by
  letI : (tensorRight L).IsEquivalence := (tensorRightEquivalence E).isEquivalence_functor
  apply (tensorRight L).map_injective
  change a ▷ L = b ▷ L
  exact (cancel_epi γ.hom).mp (ha.trans hb.symm)

section Image
variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal] [F.IsEquivalence]

/-- The actual tensorator transports a line intertwiner. -/
def imageIntertwiner (Z : Center C) (L A : C) (γ : L ⊗ Z.1 ≅ A ⊗ L) :
    F.obj L ⊗ F.obj Z.1 ≅ F.obj A ⊗ F.obj L :=
  μIso F L Z.1 ≪≫ F.mapIso γ ≪≫ (μIso F A L).symm

/-- A physical comparison of actual line intertwiners derives the
conjugation identity for the actual center components. -/
lemma imageTrivialization_comparison (Z : Center C) (A L : C) (N B : D)
    (γ : L ⊗ Z.1 ≅ A ⊗ L) (E : TensorInverse L) (u : A ⟶ Z.1)
    (η : N ⊗ F.obj Z.1 ⟶ B ⊗ N) (a : F.obj A ⟶ B)
    (r : F.obj L ≅ N) (v : B ⟶ F.obj Z.1)
    (hγ : r.inv ▷ F.obj Z.1 ≫ (imageIntertwiner F Z L A γ).hom ≫
      a ▷ F.obj L ≫ B ◁ r.hom = η)
    (hu : γ.hom ≫ u ▷ L = (Z.2.β L).inv)
    (hv : η ≫ v ▷ N = (((DrinfeldEquivalence.map F).obj Z).2.β N).inv) :
    a ≫ v = F.map u := by
  apply component_intertwining_unique ((DrinfeldEquivalence.map F).obj Z)
    (F.obj A) (F.obj L) (imageIntertwiner F Z L A γ) (E.map F)
  · exact transportComponent_intertwines ((DrinfeldEquivalence.map F).obj Z)
      (F.obj A) B (F.obj L) N (imageIntertwiner F Z L A γ).hom η a r v hγ hv
  · simpa [imageIntertwiner, Category.assoc] using
      imageComponent_intertwines F Z L A γ.hom u hu
end Image

section Product
variable (F G H : C ⥤ C) [F.Monoidal] [G.Monoidal] [H.Monoidal]
  [F.IsEquivalence] [G.IsEquivalence] [H.IsEquivalence]
  (L M N : C) (γ : tensorLeft L ≅ F ⋙ tensorRight L)
  (δ : tensorLeft M ≅ G ⋙ tensorRight M)
  (η : tensorLeft N ≅ H ⋙ tensorRight N)
  (τF : DrinfeldEquivalence.map F ≅ 𝟭 (Center C))
  (τG : DrinfeldEquivalence.map G ≅ 𝟭 (Center C))
  (τH : DrinfeldEquivalence.map H ≅ 𝟭 (Center C))

/-- The actual line product comparison and the genuine half-braiding
hexagon imply multiplication of actual trivializing components. -/
lemma productTrivialization_comparison (E : TensorInverse (L ⊗ M))
    (Z : Center C) (a : F.obj (G.obj Z.1) ⟶ H.obj Z.1) (r : L ⊗ M ≅ N)
    (hγ : r.inv ▷ Z.1 ≫ (productIntertwiner F G L M γ δ Z.1).hom ≫
      a ▷ (L ⊗ M) ≫ H.obj Z.1 ◁ r.hom = η.hom.app Z.1)
    (hF : ∀ W : Center C, γ.hom.app W.1 ≫ (τF.hom.app W).f ▷ L = (W.2.β L).inv)
    (hG : ∀ W : Center C, δ.hom.app W.1 ≫ (τG.hom.app W).f ▷ M = (W.2.β M).inv)
    (hH : η.hom.app Z.1 ≫ (τH.hom.app Z).f ▷ N = (Z.2.β N).inv) :
    a ≫ (τH.hom.app Z).f =
      (τF.hom.app ((DrinfeldEquivalence.map G).obj Z)).f ≫ (τG.hom.app Z).f := by
  apply component_intertwining_unique Z (F.obj (G.obj Z.1)) (L ⊗ M)
    (productIntertwiner F G L M γ δ Z.1) E
  · exact transportComponent_intertwines Z _ _ (L ⊗ M) N
      (productIntertwiner F G L M γ δ Z.1).hom (η.hom.app Z.1)
      a r (τH.hom.app Z).f hγ hH
  · exact productIntertwiner_intertwines F G L M γ δ τF τG hF hG Z
end Product

end Paper18.Category.DrinfeldInner
