import Paper18.Category.FactorizationDeligneBraidedBasic

/-! # The actual braided linear and Deligne factorization functors

Both source braidings are explicit reverse-second structures. No braided
instance is asserted for the default same-direction source braiding.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory CategoryTheory.Functor.LaxMonoidal CategoryTheory.Limits
open scoped TensorProduct
universe v u
namespace Paper18.Category.Drinfeld
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C] [BraidedCategory C]

lemma reverseSecondBraiding_hom (X Y : LinearTensor C C) :
    (letI : BraidedCategory (LinearTensor C C) := reverseSecondBraiding C;
      (β_ X Y).hom) =
    (show X ⊗ Y ⟶ Y ⊗ X from
      (β_ X.left Y.left).hom ⊗ₜ[ℂ] (β_ Y.right X.right).inv) := rfl

/-- The actual raw linear factorization is braided for the explicit
reverse-second source braiding. -/
def linearFactorizationBraided :
    letI : BraidedCategory (LinearTensor C C) := reverseSecondBraiding C
    (linearFactorization C).Braided := by
  letI : BraidedCategory (LinearTensor C C) := reverseSecondBraiding C
  refine { braided := ?_ }
  intro X Y
  change μ (factorizationBifunctor C) (X.left,X.right) (Y.left,Y.right) ≫
    (linearFactorization C).map
      (show X ⊗ Y ⟶ Y ⊗ X from
        (β_ X.left Y.left).hom ⊗ₜ[ℂ] (β_ Y.right X.right).inv) = _
  rw [linearFactorization_map_pure]
  exact factorization_braiding C X.left X.right Y.left Y.right

variable [HasFiniteBiproducts C]

/-- The actual Deligne factorization is braided for the explicit additive
reverse-second source braiding. The actual tensorator is the biproduct lift. -/
def deligneFactorizationBraided :
    letI : BraidedCategory (DeligneProduct C C) := deligneReverseSecondBraiding C
    (deligneFactorization C).Braided := by
  letI : BraidedCategory (LinearTensor C C) := reverseSecondBraiding C
  letI : BraidedCategory (DeligneProduct C C) := deligneReverseSecondBraiding C
  letI : (linearFactorization C).Braided := linearFactorizationBraided C
  exact inferInstanceAs ((linearMatLift (linearFactorization C)).Braided)

end Paper18.Category.Drinfeld
