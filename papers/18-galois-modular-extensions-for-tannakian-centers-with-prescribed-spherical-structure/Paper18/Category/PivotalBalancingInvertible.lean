import Paper18.Category.PivotalBalancingBasic
import Paper18.Category.InvertibleObjectsDimensions

/-!
# The twist of an actual bosonic invertible object

Naturality of the braiding against the actual coevaluation, together with the
snake identity, computes the braided closure when self-braiding is trivial.
The resulting twist-dimension identity is proved, not supplied as a field.
-/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory CategoryTheory.Limits
universe v u w
namespace Paper18.Category
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C]

/-- The actual braided closure of the chosen cup and cap. -/
def braidedDimension (X : C) : 𝟙_ C ⟶ 𝟙_ C :=
  η_ X (dual C X) ≫ (β_ X (dual C X)).hom ≫ ε_ X (dual C X)

/-- Trivial self-braiding and cancellable tensoring force the braided
closure to be the identity, by braiding naturality and the snake identity. -/
lemma braidedDimension_eq_id_of_selfBraiding (X : C) [(tensorLeft X).Faithful]
    (h : (β_ X X).hom = 𝟙 (X ⊗ X)) : braidedDimension X = 𝟙 (𝟙_ C) := by
  apply (tensorLeft X).map_injective
  change X ◁ braidedDimension X = X ◁ 𝟙 (𝟙_ C)
  calc
    _ = X ◁ η_ X (dual C X) ≫ (β_ X (X ⊗ dual C X)).hom ≫
        (α_ X (dual C X) X).hom ≫ X ◁ ε_ X (dual C X) := by
      rw [braiding_tensor_right_hom, h]
      simp only [id_whiskerRight, id_comp]
      dsimp [braidedDimension]
      monoidal
    _ = (β_ X (𝟙_ C)).hom ≫ η_ X (dual C X) ▷ X ≫
        (α_ X (dual C X) X).hom ≫ X ◁ ε_ X (dual C X) := by
      rw [braiding_naturality_right_assoc]
    _ = (β_ X (𝟙_ C)).hom ≫ (λ_ X).hom ≫ (ρ_ X).inv := by
      rw [ExactPairing.evaluation_coevaluation]
    _ = _ := by simp

variable [Preadditive C] [Linear ℂ C] [HasKernels C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [Simple (𝟙_ C)]

namespace PivotalStructure
variable (J : PivotalStructure C)

/-- The twist scalar times the braided closure is the actual pivotal
dimension, directly from the definition by the Drinfeld comparison. -/
lemma rightDimension_twistScalar (X : C) [Simple X] :
    J.rightDimension X = J.twistScalar X • braidedDimension X := by
  rw [J.rightDimension_twist, ← J.twistScalar_spec]
  simp [braidedDimension]

/-- The twist-dimension identity for actual simple objects with trivial
self-braiding is derived from the categorical closure calculation. -/
lemma twistScalar_eq_rightDim_of_selfBraiding (X : C) [Simple X]
    [(tensorLeft X).Faithful] (h : (β_ X X).hom = 𝟙 (X ⊗ X)) :
    J.twistScalar X = J.rightDim X := by
  unfold rightDim
  rw [J.rightDimension_twistScalar, braidedDimension_eq_id_of_selfBraiding X h]
  simp

end PivotalStructure

namespace TensorInverse
variable [HasFiniteBiproducts C] {ι : Type w} [Fintype ι]
  (S : FiniteSemisimpleSkeleton C ι) {T : C} (A : TensorInverse T)

include S A in
/-- An actual invertible with trivial self-braiding has twist equal to its
actual pivotal dimension times the identity. -/
lemma twistIso_eq_dimension (J : PivotalStructure C)
    (h : (β_ T T).hom = 𝟙 (T ⊗ T)) :
    (J.twistIso T).hom = J.rightDim T • 𝟙 T := by
  letI := A.simple S
  letI := A.tensorLeftIsEquivalence
  rw [← J.twistScalar_spec, J.twistScalar_eq_rightDim_of_selfBraiding T h]

include S A in
/-- The negative-dimensional boson in Proposition 2.2 has actual twist
minus the identity; no twist-dimension hypothesis is an input. -/
lemma twistIso_eq_neg_id (J : PivotalStructure C)
    (h : (β_ T T).hom = 𝟙 (T ⊗ T)) (hd : J.rightDim T = -1) :
    (J.twistIso T).hom = (-1 : ℂ) • 𝟙 T := by
  rw [A.twistIso_eq_dimension S J h, hd]

end TensorInverse
end Paper18.Category
