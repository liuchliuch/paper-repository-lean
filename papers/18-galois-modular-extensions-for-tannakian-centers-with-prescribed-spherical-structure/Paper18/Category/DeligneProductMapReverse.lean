import Paper18.Category.DeligneProductMap
import Paper18.Category.BraidedFunctorReverse
import Paper18.Category.FactorizationDeligneBraidedBasic

/-! # Actual Deligne functors with the second braiding reversed

The factor braidings are passed explicitly. This also handles equal source
categories without allowing the second reverse instance to replace the
first factor's original braiding.
-/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct
universe v u v' u' v₁ u₁ v₂ u₂
namespace Paper18.Category
section Structures
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C] [bC : BraidedCategory C]
  (D : Type u') [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D] [bD : BraidedCategory D]

/-- The actual linear tensor product with its second factor's braiding
reversed. This is an explicit structure, not a global instance. -/
def LinearTensor.reverseSecondBraiding : BraidedCategory (LinearTensor C D) :=
  @LinearTensor.instBraidedCategory C _ _ _ _ _ _ bC
    D _ _ _ _ _ _ (@reverseBraiding D _ _ bD)

/-- The actual additive Deligne product with the second braiding reversed. -/
def DeligneProduct.reverseSecondBraiding : BraidedCategory (DeligneProduct C D) :=
  @LinearMat.braidedCategory (LinearTensor C D) _ _ _ _
    (LinearTensor.reverseSecondBraiding C D)

lemma LinearTensor.reverseSecondBraiding_hom (X Y : LinearTensor C D) :
    (letI : BraidedCategory (LinearTensor C D) := reverseSecondBraiding C D
     (β_ X Y).hom) =
      (show X ⊗ Y ⟶ Y ⊗ X from
        (β_ X.left Y.left).hom ⊗ₜ[ℂ] (β_ Y.right X.right).inv) := rfl
end Structures

section Functors
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C] [bC : BraidedCategory C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D] [bD : BraidedCategory D]
  {E : Type u₁} [Category.{v₁} E] [Preadditive E] [Linear ℂ E]
  [MonoidalCategory E] [MonoidalPreadditive E] [MonoidalLinear ℂ E] [bE : BraidedCategory E]
  {H : Type u₂} [Category.{v₂} H] [Preadditive H] [Linear ℂ H]
  [MonoidalCategory H] [MonoidalPreadditive H] [MonoidalLinear ℂ H] [bH : BraidedCategory H]
  (F : C ⥤ E) [F.Additive] [F.Linear ℂ] [hF : F.Braided]
  (G : D ⥤ H) [G.Additive] [G.Linear ℂ] [hG : G.Braided]

/-- The actual raw componentwise tensor functor is braided for the
explicit reverse-second source and target braidings. -/
def LinearTensor.mapReverseSecondBraided :
    letI : BraidedCategory (LinearTensor C D) := reverseSecondBraiding C D
    letI : BraidedCategory (LinearTensor E H) := reverseSecondBraiding E H
    (map F G).Braided := by
  exact @LinearTensor.map_braided C _ _ _ _ _ _ D _ _ _ _ _ _
    E _ _ _ _ _ _ H _ _ _ _ _ _ F _ _ G _ _
    bC (@reverseBraiding D _ _ bD) bE (@reverseBraiding H _ _ bH) hF
    (@braidedFunctorReverse D _ _ bD H _ _ bH G hG)

/-- The actual Deligne componentwise functor is braided for the explicit
reverse-second structures. The tensor and unit maps are its constructed
strong monoidal maps. -/
def DeligneProduct.mapReverseSecondBraided :
    letI : BraidedCategory (DeligneProduct C D) := reverseSecondBraiding C D
    letI : BraidedCategory (DeligneProduct E H) := reverseSecondBraiding E H
    (map F G).Braided := by
  exact @DeligneProduct.map_braided C _ _ _ D _ _ _ E _ _ _ H _ _ _ F _ _ G _ _
    _ _ _ _ _ _ _ _ _ _ _ _
    bC (@reverseBraiding D _ _ bD) bE (@reverseBraiding H _ _ bH) hF
    (@braidedFunctorReverse D _ _ bD H _ _ bH G hG)
end Functors

section EqualSource
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C] [BraidedCategory C]

/-- The generic actual raw structure agrees with the precise braiding
used by actual canonical factorization. -/
lemma LinearTensor.reverseSecondBraiding_eq_drinfeld :
    reverseSecondBraiding C C = Drinfeld.reverseSecondBraiding C := rfl

/-- The generic additive structure agrees with the actual diagonal
algebra's factorization source braiding. -/
lemma DeligneProduct.reverseSecondBraiding_eq_drinfeld :
    reverseSecondBraiding C C = Drinfeld.deligneReverseSecondBraiding C := rfl
end EqualSource
end Paper18.Category
