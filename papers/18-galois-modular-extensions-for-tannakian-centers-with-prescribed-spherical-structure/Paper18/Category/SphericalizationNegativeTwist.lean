import Paper18.Category.SphericalizationNegative
import Paper18.Category.PivotalBalancingInvertible

/-! # The actual twist of the canonical negative generator -/
noncomputable section
universe v u w
namespace Paper18.Category.Sphericalized
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

include S in
/-- The canonical transparent order-two boson has actual twist minus the
identity under the constructed spherical pivotal structure. -/
lemma negativeGenerator_twist :
    ((pivotalStructure (C := C)).twistIso negativeGenerator).hom =
      (-1 : ℂ) • 𝟙 negativeGenerator :=
  negativeGeneratorTensorInverse.twistIso_eq_neg_id (skeleton S) pivotalStructure
    negativeGenerator_selfBraiding (negativeGenerator_rightDim S)

end Paper18.Category.Sphericalized
