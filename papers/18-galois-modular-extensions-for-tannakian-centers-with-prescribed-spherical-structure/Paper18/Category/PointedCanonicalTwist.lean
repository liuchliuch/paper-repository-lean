import Paper18.Category.PointedAppendixB
import Paper18.Category.PointedPivotal
import Paper18.Category.PointedTensorCharacters

noncomputable section

open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits

namespace Paper18.Category.AppendixBPointed

attribute [local instance 2000] RightRigidCategory.rightDual
attribute [local instance] PointedVec.simple_simpleObject

lemma braidingScalar_neg_self (a : Paper18.PointedA) :
    braidingScalar a (-a) * Paper18.q a = 1 := by
  rw [← braidingScalar_self, ← braidingScalar_add_right]
  simp [braidingScalar]

lemma canonical_twistScalar (a : Paper18.PointedA) :
    (PointedVec.pivotalStructure Paper18.PointedA).twistScalar
      (PointedVec.simpleObject Paper18.PointedA a) = Paper18.q a := by
  let J := PointedVec.pivotalStructure Paper18.PointedA
  let X := PointedVec.simpleObject Paper18.PointedA a
  have hc : braidedDimension X = braidingScalar a (-a) • 𝟙 (𝟙_ Vec) := by
    exact PointedVec.simple_braidedDimension bicharacter a
  have hd := J.rightDimension_twistScalar X
  rw [PointedVec.pivotalStructure_rightDimension_simple, hc, smul_smul] at hd
  have he : (1 : ℂ) = J.twistScalar X * braidingScalar a (-a) := by
    apply smul_left_injective ℂ (CategoryTheory.id_nonzero (𝟙_ Vec))
    simpa only [one_smul] using hd
  apply mul_right_cancel₀ (braidingScalar_ne_zero a (-a))
  exact he.symm.trans (by rw [mul_comm, braidingScalar_neg_self])

/-- The actual twist induced by the canonical positive pivotal structure
is exactly the previously constructed quadratic twist `i^(ab)`. -/
theorem canonical_twist :
    (PointedVec.pivotalStructure Paper18.PointedA).twistNatIso = twist := by
  apply TensorAutomorphism.ext_simple _ _ (PointedVec.skeleton Paper18.PointedA)
  intro a
  change (PointedVec.pivotalStructure Paper18.PointedA).twistScalar
      (PointedVec.simpleObject Paper18.PointedA a) =
    simpleScalarEquiv _ (PointedVec.degreeMap Paper18.q (PointedVec.simpleObject _ a))
  rw [canonical_twistScalar, PointedVec.degreeMap_simple_eq_scalar,
    simpleScalarEquiv_smul_id]

/-- The actual pointed category with its positive canonical pivotal
structure is modular: it is spherical and its Müger center is trivial. -/
theorem canonical_modular :
    IsModular (PointedVec.pivotalStructure Paper18.PointedA) :=
  ⟨PointedVec.pivotalStructure_spherical Paper18.PointedA, nondegenerate⟩

end Paper18.Category.AppendixBPointed
