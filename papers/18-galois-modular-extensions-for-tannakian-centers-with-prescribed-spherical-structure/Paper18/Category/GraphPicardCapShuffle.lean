import Paper18.Category.GraphPicardCapSlide
import Paper18.Category.GraphPicardMoritaCentralBraided

/-! # The genuine mixed graph crossing under the Morita central action -/
noncomputable section
set_option maxHeartbeats 2000000
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped MonoidalLeftAction
universe v u vM uM
namespace Paper18.Category.GraphPicard

section Shuffle
variable {E : Type u} [Category.{v} E] [MonoidalCategory E]
lemma center_tensorμ_f (A B C Q : Center E) :
    (tensorμ A B C Q).f = centralTensorShuffle B A.1 C.1 Q.1 := by
  simp only [tensorμ, centralTensorShuffle, Center.comp_f,
    Center.associator_hom_f, Center.associator_inv_f,
    Center.whiskerLeft_f, Center.whiskerRight_f, Center.braiding_hom_f,
    whiskerLeft_comp, Category.assoc]
  rfl
end Shuffle

variable (D : Type u) [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]

/-- For the actual mixed negative-positive crossing the two center
braidings coincide, by the actual mutual centralization equation. -/
lemma mixedTensorμ_reverse (A B C Q : D) :
    tensorμ ((Drinfeld.positive D).obj A) ((Drinfeld.negative D).obj B)
        ((Drinfeld.positive D).obj C) ((Drinfeld.negative D).obj Q) =
      @tensorμ (Center D) _ _ (reverseBraiding (Center D))
        ((Drinfeld.positive D).obj A) ((Drinfeld.negative D).obj B)
        ((Drinfeld.positive D).obj C) ((Drinfeld.negative D).obj Q) := by
  have hb : (β_ ((Drinfeld.negative D).obj B) ((Drinfeld.positive D).obj C)).hom =
      (β_ ((Drinfeld.positive D).obj C) ((Drinfeld.negative D).obj B)).inv := by
    exact (centralizes_iff_braiding_inv _ _).mp
      (Drinfeld.positive_centralizes_negative C B)
  dsimp only [tensorμ, reverseBraiding, Iso.symm_hom]
  rw [hb]


variable (M : Type uM) [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [MonoidalLeftAction Dᴹᵒᵖ M]
  [∀ X : Dᴹᵒᵖ, (MonoidalLeftAction.actionLeft M X).Additive]
  [∀ X : Dᴹᵒᵖ, (MonoidalLeftAction.actionLeft M X).Linear ℂ]
local notation "H" => rightCentralAction D M
local notation "K" => rightCentralLift D M

/-- The actual strong central action transports the actual mixed graph
crossing to its actual native module-lineator crossing. -/
lemma rightCentralAction_mixedShuffle (A B C Q : D) :
    (Functor.LaxMonoidal.μ H ((Drinfeld.positive D).obj A) ((Drinfeld.negative D).obj B) ⊗ₘ
        Functor.LaxMonoidal.μ H ((Drinfeld.positive D).obj C) ((Drinfeld.negative D).obj Q)) ≫
      Functor.LaxMonoidal.μ H
        ((Drinfeld.positive D).obj A ⊗ (Drinfeld.negative D).obj B)
        ((Drinfeld.positive D).obj C ⊗ (Drinfeld.negative D).obj Q) ≫
      (H).map (tensorμ ((Drinfeld.positive D).obj A) ((Drinfeld.negative D).obj B)
        ((Drinfeld.positive D).obj C) ((Drinfeld.negative D).obj Q)) =
    centralTensorShuffle ((K).obj ((Drinfeld.negative D).obj B))
        ((H).obj ((Drinfeld.positive D).obj A)) ((H).obj ((Drinfeld.positive D).obj C))
        ((H).obj ((Drinfeld.negative D).obj Q)) ≫
      (Functor.LaxMonoidal.μ H ((Drinfeld.positive D).obj A) ((Drinfeld.positive D).obj C) ⊗ₘ
        Functor.LaxMonoidal.μ H ((Drinfeld.negative D).obj B) ((Drinfeld.negative D).obj Q)) ≫
      Functor.LaxMonoidal.μ H
        ((Drinfeld.positive D).obj A ⊗ (Drinfeld.positive D).obj C)
        ((Drinfeld.negative D).obj B ⊗ (Drinfeld.negative D).obj Q) := by
  letI : BraidedCategory (Center D) := reverseBraiding (Center D)
  letI : (K).Braided := rightCentralLiftReverseBraided D M
  have h := tensorμ_comp_μ_tensorHom_μ_comp_μ K
    ((Drinfeld.positive D).obj A) ((Drinfeld.negative D).obj B)
    ((Drinfeld.positive D).obj C) ((Drinfeld.negative D).obj Q)
  have hf := congrArg Center.Hom.f h
  simp only [Center.comp_f, Center.tensorHom_f, center_tensorμ_f] at hf
  change _ = _ at hf
  rw [← mixedTensorμ_reverse D A B C Q] at hf
  exact hf.symm

end Paper18.Category.GraphPicard
