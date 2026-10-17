import Paper18.Category.DrinfeldInnerTrivialization

/-! # Actual multiplication of inner center trivializations -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u
namespace Paper18.Category.DrinfeldInner
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  (F G : C ⥤ C) [F.Monoidal] [G.Monoidal] [F.IsEquivalence] [G.IsEquivalence]
  (L M : C) (γ : tensorLeft L ≅ F ⋙ tensorRight L)
  (δ : tensorLeft M ≅ G ⋙ tensorRight M)

/-- The actual composite intertwiner carries the actual tensor product
of the two conjugating lines. -/
def productIntertwiner (X : C) : (L ⊗ M) ⊗ X ≅ F.obj (G.obj X) ⊗ (L ⊗ M) :=
  α_ L M X ≪≫ whiskerLeftIso L (δ.app X) ≪≫ (α_ L (G.obj X) M).symm ≪≫
    whiskerRightIso (γ.app (G.obj X)) M ≪≫ α_ (F.obj (G.obj X)) L M

variable (τF : DrinfeldEquivalence.map F ≅ 𝟭 (Center C))
  (τG : DrinfeldEquivalence.map G ≅ 𝟭 (Center C))

/-- The genuine half-braiding hexagon gives the product law of the actual
trivializing components for the composite conjugation intertwiner. -/
lemma productIntertwiner_intertwines
    (hF : ∀ Z : Center C, γ.hom.app Z.1 ≫ (τF.hom.app Z).f ▷ L = (Z.2.β L).inv)
    (hG : ∀ Z : Center C, δ.hom.app Z.1 ≫ (τG.hom.app Z).f ▷ M = (Z.2.β M).inv)
    (Z : Center C) :
    (productIntertwiner F G L M γ δ Z.1).hom ≫
      ((τF.hom.app ((DrinfeldEquivalence.map G).obj Z)).f ≫ (τG.hom.app Z).f) ▷ (L ⊗ M) =
        (Z.2.β (L ⊗ M)).inv := by
  let U := (DrinfeldEquivalence.map G).obj Z
  let p := (τF.hom.app U).f
  let q := (τG.hom.app Z).f
  have hc : (U.2.β L).inv ≫ q ▷ L = L ◁ q ≫ (Z.2.β L).inv := by
    apply (cancel_mono (Z.2.β L).hom).mp
    have h := (τG.hom.app Z).comm L
    change q ▷ L ≫ (Z.2.β L).hom = (U.2.β L).hom ≫ L ◁ q at h
    rw [Category.assoc, h, Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, comp_id]
  calc
    _ = (α_ L M Z.1).hom ≫ L ◁ δ.hom.app Z.1 ≫ (α_ L U.1 M).inv ≫
        (γ.hom.app U.1 ≫ p ▷ L) ▷ M ≫ (α_ U.1 L M).hom ≫ q ▷ (L ⊗ M) := by
      dsimp only [productIntertwiner, U, p, q]
      simp only [Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom, whiskerRightIso_hom]
      monoidal
    _ = (α_ L M Z.1).hom ≫ L ◁ δ.hom.app Z.1 ≫ (α_ L U.1 M).inv ≫
        (U.2.β L).inv ▷ M ≫ (α_ U.1 L M).hom ≫ q ▷ (L ⊗ M) := by rw [hF U]
    _ = (α_ L M Z.1).hom ≫ L ◁ δ.hom.app Z.1 ≫ (α_ L U.1 M).inv ≫
        ((U.2.β L).inv ≫ q ▷ L) ▷ M ≫ (α_ Z.1 L M).hom := by monoidal
    _ = (α_ L M Z.1).hom ≫ L ◁ δ.hom.app Z.1 ≫ (α_ L U.1 M).inv ≫
        (L ◁ q ≫ (Z.2.β L).inv) ▷ M ≫ (α_ Z.1 L M).hom := by rw [hc]
    _ = (α_ L M Z.1).hom ≫ L ◁ (δ.hom.app Z.1 ≫ q ▷ M) ≫
        (α_ L Z.1 M).inv ≫ (Z.2.β L).inv ▷ M ≫ (α_ Z.1 L M).hom := by monoidal
    _ = (α_ L M Z.1).hom ≫ L ◁ (Z.2.β M).inv ≫
        (α_ L Z.1 M).inv ≫ (Z.2.β L).inv ▷ M ≫ (α_ Z.1 L M).hom := by rw [hG Z]
    _ = _ := (Drinfeld.halfBraiding_inv_monoidal Z.2 L M).symm

end Paper18.Category.DrinfeldInner
