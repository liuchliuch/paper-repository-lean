import Paper18.Category.DrinfeldPivotalBraided
import Paper18.Category.DeligneProductPivotal
import Paper18.Category.FactorizationDeligneBraided

/-! # The prescribed pivotal structure for reverse-second factorization -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped TensorProduct
universe v u
namespace Paper18.Category.Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [LeftRigidCategory C] [BraidedCategory C]

/-- The actual product balancing with the first ambient and second reverse
braiding explicitly distinguished, even when both factors have the same type. -/
def reverseSecondTwist (J : PivotalStructure C) :
    𝟭 (LinearTensor C C) ≅ 𝟭 (LinearTensor C C) :=
  @LinearTensor.productTwist C _ _ _ _ _ inferInstance
    C _ _ _ _ _ (reverseBraiding C) J J

/-- The actual prescribed Deligne pivotal structure with exactly the
reverse-second braiding used by the actual factorization functor. -/
def reverseSecondPivotal (J : PivotalStructure C) :
    PivotalStructure (DeligneProduct C C) :=
  @DeligneProduct.pivotal C _ _ _ _ _ _ _ inferInstance
    C _ _ _ _ _ _ _ (reverseBraiding C) J J

lemma reverseSecondPivotal_twist (J : PivotalStructure C) :
    letI : BraidedCategory (DeligneProduct C C) := deligneReverseSecondBraiding C
    (reverseSecondPivotal J).twistNatIso = LinearMat.matrixTwist (reverseSecondTwist J) := by
  letI : BraidedCategory (DeligneProduct C C) := deligneReverseSecondBraiding C
  exact @DeligneProduct.pivotal_twist C _ _ _ _ _ _ _ inferInstance
    C _ _ _ _ _ _ _ (reverseBraiding C) J J

/-- On each actual pure pair, centralization of the positive and negative
images identifies the product balancing with the actual center balancing. -/
lemma linearFactorization_twist (J : PivotalStructure C) (X : LinearTensor C C) :
    (linearFactorization C).map ((reverseSecondTwist J).hom.app X) =
      ((centerPivotal J).twistIso ((linearFactorization C).obj X)).hom := by
  change (linearFactorization C).map
    (show X ⟶ X from (J.twistIso X.left).hom ⊗ₜ[ℂ]
      (letI : BraidedCategory C := reverseBraiding C; (J.twistIso X.right).hom)) = _
  rw [linearFactorization_map_tmul]
  change _ = ((centerPivotal J).twistIso
    ((positive C).obj X.left ⊗ (negative C).obj X.right)).hom
  rw [(centerPivotal J).twist_tensor,
    positive_centralizes_negative (C := C) X.left X.right, id_comp]
  rw [← (positive_preservesPivotal J).twist X.left, ← negative_twist J X.right]

end Paper18.Category.Drinfeld
