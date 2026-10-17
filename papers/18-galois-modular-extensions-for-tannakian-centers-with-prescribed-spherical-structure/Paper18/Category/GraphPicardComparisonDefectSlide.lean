import Paper18.Category.GraphPicardCapSlide

/-! # Cancelling the genuine central cap shuffle -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u
namespace Paper18.Category.GraphPicard
variable {E : Type u} [Category.{v} E] [MonoidalCategory E]

instance centralTensorShuffle_isIso (Z : Center E) (A B Q : E) :
    IsIso (centralTensorShuffle Z A B Q) := by
  unfold centralTensorShuffle
  infer_instance

/-- The ordered two-cap product determines its unshuffled product, with
an inverse of the genuine central crossing. -/
lemma capProduct_of_ordered {P A B Q T : E} (Z : Center E)
    (a : A ⊗ B ≅ P) (r : Z.1 ⊗ Q ⟶ T)
    (e : A ⊗ Z.1 ⟶ 𝟙_ E) (f : B ⊗ Q ⟶ 𝟙_ E) (t : P ⊗ T ⟶ 𝟙_ E)
    (h : (e ⊗ₘ f) ≫ (λ_ (𝟙_ E)).hom =
      centralTensorShuffle Z A B Q ≫ (a.hom ⊗ₘ r) ≫ t) :
    P ◁ ((Z.2.β Q).inv ≫ r) ≫ t =
      a.inv ▷ (Q ⊗ Z.1) ≫ nestedCap f e := by
  have hc : (a.hom ⊗ₘ r) ≫ t =
      (A ⊗ B) ◁ (Z.2.β Q).hom ≫ nestedCap f e := by
    apply (cancel_epi (centralTensorShuffle Z A B Q)).mp
    exact h.symm.trans (centralTensorShuffle_nestedCap Z e f).symm
  have hh := congrArg (fun k => (a.inv ⊗ₘ (Z.2.β Q).inv) ≫ k) hc
  simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc,
    Iso.inv_hom_id, Category.comp_id] at hh
  simpa only [id_tensorHom, tensorHom_id] using hh

end Paper18.Category.GraphPicard
