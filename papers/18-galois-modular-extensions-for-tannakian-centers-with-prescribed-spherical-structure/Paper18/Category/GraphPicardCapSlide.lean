import Paper18.Category.GraphPicardTensorTranspose
import Paper18.Category.DrinfeldBasic

/-! # Sliding an actual central strand past a genuine cap

Only the actual naturality and tensor law of one half-braiding are used.
The ambient monoidal category need not carry a braiding.
-/
noncomputable section
set_option maxHeartbeats 2000000
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u
namespace Paper18.Category.GraphPicard
variable {E : Type u} [Category.{v} E] [MonoidalCategory E]

/-- The actual middle-strand crossing supplied by one specified genuine
central object, without any ambient braiding. -/
def centralTensorShuffle (Z : Center E) (A B Q : E) :
    (A ⊗ Z.1) ⊗ (B ⊗ Q) ⟶ (A ⊗ B) ⊗ (Z.1 ⊗ Q) :=
  (α_ A Z.1 (B ⊗ Q)).hom ≫
    A ◁ ((α_ Z.1 B Q).inv ≫ (Z.2.β B).hom ▷ Q ≫ (α_ B Z.1 Q).hom) ≫
      (α_ A B (Z.1 ⊗ Q)).inv

/-- Moving a genuine central strand through a genuine cap preserves the
actual two-cap contraction. No centrality of either cap is assumed. -/
lemma centralTensorShuffle_nestedCap (Z : Center E) {A B Q : E}
    (e : A ⊗ Z.1 ⟶ 𝟙_ E) (f : B ⊗ Q ⟶ 𝟙_ E) :
    centralTensorShuffle Z A B Q ≫ (A ⊗ B) ◁ (Z.2.β Q).hom ≫ nestedCap f e =
      (e ⊗ₘ f) ≫ (λ_ (𝟙_ E)).hom := by
  have hn := Z.2.naturality f
  rw [Drinfeld.halfBraiding_unit] at hn
  calc
    _ = (α_ A Z.1 (B ⊗ Q)).hom ≫
        A ◁ ((Z.2.β (B ⊗ Q)).hom ≫ f ▷ Z.1 ≫ (λ_ Z.1).hom) ≫ e := by
      dsimp only [centralTensorShuffle, nestedCap]
      rw [Z.2.monoidal]
      monoidal
    _ = (α_ A Z.1 (B ⊗ Q)).hom ≫
        A ◁ (Z.1 ◁ f ≫ (ρ_ Z.1).hom) ≫ e := by
      rw [← reassoc_of% hn]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = ((A ⊗ Z.1) ◁ f ≫ e ▷ (𝟙_ E)) ≫ (λ_ (𝟙_ E)).hom := by monoidal
    _ = _ := by rw [← MonoidalCategory.tensorHom_def']

end Paper18.Category.GraphPicard
