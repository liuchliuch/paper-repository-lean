import Paper18.Category.QuasiFusionPivotalClosure
import Paper18.Category.SphericalComparisonPositive

/-! # Actual positive spherical pivotal structure on cocycle graded vector spaces

The bidual map is corrected in degree g by ψ(g,g⁻¹,g). Actual cup-cap
calculations show that its closure on each categorical simple is one.
Schur injectivity and canonical tensor-cap comparison prove coherence on
simple pairs, and actual biproduct decompositions extend it to every pair.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
namespace Paper18.Category.QuasiFusion.CocycleVec
attribute [local instance 2000] RightRigidCategory.rightDual
variable {G : Type} [Group G] [Fintype G] (ψ : ThreeCocycle G)

/-- The actual ψ-weighted bidual identification respects the canonical
rigid double-dual tensor comparison on every actual pair of objects. -/
lemma pivotalNatIso_tensor (X Y : CocycleVec ψ) :
    (pivotalNatIso ψ).hom.app (X ⊗ Y) =
      ((pivotalNatIso ψ).hom.app X ⊗ₘ (pivotalNatIso ψ).hom.app Y) ≫
        doubleDualTensorHom (CocycleVec ψ) X Y := by
  apply PivotalCriterion.tensor_of_representatives (skeleton ψ) (pivotalNatIso ψ) _ X Y
  intro a b
  letI : Simple ((skeleton ψ).simpleObject a ⊗ (skeleton ψ).simpleObject b) :=
    homogeneousTensor_simple a b
  apply PivotalCriterion.tensor_of_normalized_closure (pivotalNatIso ψ)
  intro Z hZ
  letI := hZ
  exact pivotal_closure_simple ψ Z

/-- The actual positive pivotal structure on the actual cocycle fusion
category, including canonical unit and tensor coherence. -/
def pivotalStructure : PivotalStructure (CocycleVec ψ) where
  j := pivotalNatIso ψ
  unit := PivotalCriterion.unit_of_tensor (pivotalNatIso ψ) (pivotalNatIso_tensor ψ)
  tensor := pivotalNatIso_tensor ψ

/-- Its actual categorical dimension is the sum of homogeneous ranks. -/
lemma pivotal_rightDimension (X : CocycleVec ψ) :
    (pivotalStructure ψ).rightDimension X =
      (∑ a, (Module.finrank ℂ (X a) : ℂ)) • 𝟙 (𝟙_ (CocycleVec ψ)) := by
  simpa only [PivotalStructure.rightDimension, PivotalStructure.rightTrace,
    PivotalStructure.leftEvaluation, id_whiskerRight, id_comp, pivotalStructure,
    PivotalCriterion.closure] using pivotal_closure ψ X

/-- Every actual categorical simple has categorical dimension one. -/
lemma pivotal_rightDim_simple (X : CocycleVec ψ) [Simple X] :
    (pivotalStructure ψ).rightDim X = 1 := by
  change unitScalarEquiv (C := CocycleVec ψ) _ = 1
  have h := pivotal_closure_simple ψ X
  have he : (pivotalStructure ψ).rightDimension X = 𝟙 (𝟙_ (CocycleVec ψ)) := by
    simpa only [PivotalStructure.rightDimension, PivotalStructure.rightTrace,
      PivotalStructure.leftEvaluation, id_whiskerRight, id_comp, pivotalStructure,
      PivotalCriterion.closure] using h
  rw [he, unitScalarEquiv_id]

/-- Positivity is proved for the actual pivotal trace on every actual simple. -/
theorem pivotal_positive : (pivotalStructure ψ).Positive := by
  intro X hX
  letI := hX
  rw [pivotal_rightDim_simple]
  exact ⟨by norm_num, rfl⟩

/-- The constructed pivotal structure is spherical on all endomorphisms. -/
theorem pivotal_spherical : (pivotalStructure ψ).Spherical :=
  (pivotalStructure ψ).spherical_of_positive (skeleton ψ) (pivotal_positive ψ)

end Paper18.Category.QuasiFusion.CocycleVec
