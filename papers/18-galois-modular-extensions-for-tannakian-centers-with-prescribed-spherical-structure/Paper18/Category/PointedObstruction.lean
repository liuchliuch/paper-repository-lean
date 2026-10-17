import Paper18.Category.PointedAppendixB
import Paper18.Category.PointedTensorCharacters
import Paper18.Category.PointedPivotal
import Paper18.Category.PivotalModification

noncomputable section

open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits

namespace Paper18.Category.AppendixBPointed

attribute [local instance] PointedVec.simple_simpleObject

/-- Every actual spherical pivotal structure on the ambient category has
dimension one on the degree `(0,2)` simple. The comparison character is
derived from the actual pivotal structures and their tensor coherence. -/
theorem spherical_dimension_zero_two (J : PivotalStructure Vec) (hJ : J.Spherical) :
    J.rightDim (PointedVec.simpleObject Paper18.PointedA (0, 2)) = 1 := by
  let K := PointedVec.pivotalStructure Paper18.PointedA
  let ψ := PointedVec.tensorCharacter (J.ratio K)
  have hsq (a : Paper18.PointedA) : ψ a ^ 2 = 1 := by
    have hs := J.comparisonScalar_sign K (PointedVec.skeleton Paper18.PointedA)
      hJ (PointedVec.pivotalStructure_spherical Paper18.PointedA)
      (PointedVec.simpleObject Paper18.PointedA a)
    change ψ a = 1 ∨ ψ a = -1 at hs
    rcases hs with hs | hs <;> simp [hs]
  have hp := Paper18.appendixB_chi_0_2 ψ hsq
  rw [J.rightDim_comparison K, PointedVec.pivotalStructure_rightDim_simple, mul_one]
  exact hp

/-- The all-degree character gives an explicit actual pivotal extension.
It is defined on every finite graded vector space and every morphism. -/
def nonsphericalPivotalExtension : PivotalStructure Vec :=
  (PointedVec.pivotalStructure Paper18.PointedA).modify
    (PointedVec.characterAutomorphism Paper18.chi)

lemma characterAutomorphism_scalar (χ : AddChar Paper18.PointedA ℂ) (a : Paper18.PointedA) :
    TensorAutomorphism.scalar (PointedVec.characterAutomorphism χ)
      (PointedVec.simpleObject Paper18.PointedA a) = χ a := by
  change simpleScalarEquiv _ (PointedVec.degreeMap χ (PointedVec.simpleObject _ a)) = _
  rw [PointedVec.degreeMap_simple_eq_scalar, simpleScalarEquiv_smul_id]

@[simp] theorem nonsphericalPivotalExtension_dimension (a : Paper18.PointedA) :
    nonsphericalPivotalExtension.rightDim (PointedVec.simpleObject Paper18.PointedA a) =
      Paper18.chi a := by
  rw [nonsphericalPivotalExtension, PivotalStructure.modify_rightDim,
    PointedVec.pivotalStructure_rightDim_simple, mul_one, characterAutomorphism_scalar]

@[simp] theorem nonsphericalPivotalExtension_leftDimension (a : Paper18.PointedA) :
    nonsphericalPivotalExtension.leftDim (PointedVec.simpleObject Paper18.PointedA a) =
      (Paper18.chi a)⁻¹ := by
  rw [nonsphericalPivotalExtension, PivotalStructure.modify_leftDim,
    PivotalStructure.leftDim_eq_rightDim _
      (PointedVec.pivotalStructure_spherical Paper18.PointedA),
    PointedVec.pivotalStructure_rightDim_simple, mul_one, characterAutomorphism_scalar]

/-- The actual right-to-left dimension ratio of the pivotal extension is
the monodromy with the distinguished object. -/
theorem nonsphericalPivotalExtension_slope (a : Paper18.PointedA) :
    nonsphericalPivotalExtension.rightDim (PointedVec.simpleObject Paper18.PointedA a) /
      nonsphericalPivotalExtension.leftDim (PointedVec.simpleObject Paper18.PointedA a) =
        Paper18.monodromy Paper18.f a := by
  rw [nonsphericalPivotalExtension_dimension, nonsphericalPivotalExtension_leftDimension,
    div_eq_mul_inv, inv_inv, ← pow_two]
  exact (Paper18.appendixB_slope a).1.trans (Paper18.appendixB_slope a).2

/-- This explicit pivotal extension is nonspherical, witnessed by an
actual categorical simple dimension. -/
theorem nonsphericalPivotalExtension_not_spherical :
    ¬ nonsphericalPivotalExtension.Spherical := by
  intro h
  have he := spherical_dimension_zero_two nonsphericalPivotalExtension h
  rw [nonsphericalPivotalExtension_dimension, Paper18.appendixB_chi_at_zero_two] at he
  norm_num at he

end Paper18.Category.AppendixBPointed
