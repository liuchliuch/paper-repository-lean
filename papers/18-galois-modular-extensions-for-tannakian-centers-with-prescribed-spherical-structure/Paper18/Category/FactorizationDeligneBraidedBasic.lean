import Paper18.Category.FactorizationDeligneMonoidal
import Paper18.Category.LinearTensorBraided
import Paper18.Category.LinearMatMonoidalLiftBraided

/-! # Reverse-second braiding and the actual factorization braid equation -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory CategoryTheory.Functor.LaxMonoidal
open scoped TensorProduct
universe v u v' u'
namespace Paper18.Category.Drinfeld

section BraidedTensor
variable {E : Type u'} [Category.{v'} E] [MonoidalCategory E] [BraidedCategory E]

/-- Tensoring a pair of strands respects the paired braiding whenever the
first positive strand centralizes the last negative strand. -/
lemma tensorμ_braided_of_cross (P Q R S : E)
    (h : (β_ P S).hom ≫ (β_ S P).hom = 𝟙 (P ⊗ S)) :
    tensorμ P Q R S ≫ ((β_ P R).hom ⊗ₘ (β_ Q S).hom) =
      (β_ (P ⊗ Q) (R ⊗ S)).hom ≫ tensorμ R S P Q := by
  symm
  calc
    _ = 𝟙 _ ⊗≫ (P ◁ (β_ Q R).hom) ▷ S ⊗≫
        ((β_ P R).hom ▷ (Q ⊗ S) ≫ (R ⊗ P) ◁ (β_ Q S).hom) ⊗≫
        (R ◁ ((β_ P S).hom ≫ (β_ S P).hom)) ▷ Q ⊗≫ 𝟙 _ := by
      simp only [braiding_tensor_left_hom, braiding_tensor_right_hom, tensorμ]
      monoidal
    _ = 𝟙 _ ⊗≫ (P ◁ (β_ Q R).hom) ▷ S ⊗≫
        ((β_ P R).hom ▷ (Q ⊗ S) ≫ (R ⊗ P) ◁ (β_ Q S).hom) ⊗≫ 𝟙 _ := by
      rw [h]
      monoidal
    _ = _ := by
      simp only [tensorμ, tensorHom_def]
      monoidal
end BraidedTensor

variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C] [BraidedCategory C]

/-- The actual raw tensor category's second factor carries reverse braiding.
This is an explicit structure, deliberately not a global instance. -/
def reverseSecondBraiding : BraidedCategory (LinearTensor C C) :=
  @LinearTensor.instBraidedCategory C _ _ _ _ _ _ _ C _ _ _ _ _ _ (reverseBraiding C)

/-- The actual additive Deligne tensor category inherits that precise
reverse-second raw braiding, again as an explicit structure. -/
def deligneReverseSecondBraiding : BraidedCategory (DeligneProduct C C) :=
  @LinearMat.braidedCategory (LinearTensor C C) _ _ _ _ (reverseSecondBraiding C)

lemma factorization_braiding (X Y X' Y' : C) :
    μ (factorizationBifunctor C) (X,Y) (X',Y') ≫
      (factorizationBifunctor C).map
        (show (X ⊗ X',Y ⊗ Y') ⟶ (X' ⊗ X,Y' ⊗ Y) from
          ((β_ X X').hom, (β_ Y' Y).inv)) =
      (β_ ((factorizationBifunctor C).obj (X,Y))
        ((factorizationBifunctor C).obj (X',Y'))).hom ≫
        μ (factorizationBifunctor C) (X',Y') (X,Y) := by
  apply (Center.forget C).map_injective
  change (μ (factorizationBifunctor C) (X,Y) (X',Y')).f ≫
      ((β_ X X').hom ⊗ₘ (β_ Y' Y).inv) =
    (β_ ((factorizationBifunctor C).obj (X,Y))
      ((factorizationBifunctor C).obj (X',Y'))).hom.f ≫
      (μ (factorizationBifunctor C) (X',Y') (X,Y)).f
  rw [factorizationTensorator, factorizationTensorator]
  have hh := tensorμ_braided_of_cross
    ((positive C).obj X) ((negative C).obj Y)
    ((positive C).obj X') ((negative C).obj Y')
    (positive_centralizes_negative (C := C) X Y')
  exact congrArg Center.Hom.f hh

end Paper18.Category.Drinfeld
