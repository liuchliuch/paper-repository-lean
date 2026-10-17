import Paper18.Category.ENOPseudounitarySigns
import Paper18.Category.ENOPseudounitaryScalarLift
import Paper18.Category.PivotalModification
import Paper18.Category.SphericalComparisonPositive

/-!
# Constructing an actual positive spherical structure from pseudounitarity

For an already prescribed spherical pivotal structure, the sole hypothesis
below beyond the actual fusion-category structures is equality of its global
dimension and the total FP dimension. The correction is an actual natural
isomorphism with proved unit and tensor laws, constructed from the derived
sign character and actual finite biproduct decompositions.

The implication from weak integrality to this global-dimension equality
is the separate ENO Proposition 8.22/8.24 step; it is not asserted here.
-/

noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u w

namespace Paper18.Category.PivotalStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (J : PivotalStructure C) (S : FiniteSemisimpleSkeleton C ι)

/-- Correct the given actual pivotal identification by the sign character
derived from equality in the FP dimension bounds. -/
def positiveOfGlobalEq (hJ : J.Spherical)
    (hD : (J.pivotalData S).globalDimension.re = S.fusionBasis.totalFPdim) :
    PivotalStructure C :=
  J.modify (S.signNatIso
    ((J.pivotalData S).signCharacterOfGlobalEq (J.pivotalData_spherical S hJ) hD))

theorem positiveOfGlobalEq_spherical (hJ : J.Spherical)
    (hD : (J.pivotalData S).globalDimension.re = S.fusionBasis.totalFPdim) :
    (J.positiveOfGlobalEq S hJ hD).Spherical :=
  J.modify_spherical _ hJ (S.signNatIso_involutive _)

/-- The categorical trace of each corrected actual simple object is its
positive FP dimension. -/
@[simp] theorem positiveOfGlobalEq_rightDim_simple (hJ : J.Spherical)
    (hD : (J.pivotalData S).globalDimension.re = S.fusionBasis.totalFPdim) (i : ι) :
    (J.positiveOfGlobalEq S hJ hD).rightDim (S.simpleObject i) =
      (S.fusionBasis.fpdim i : ℂ) := by
  rw [positiveOfGlobalEq, modify_rightDim, S.signNatIso_scalar]
  exact (J.pivotalData S).sign_mul_jdim_of_global_eq (J.pivotalData_spherical S hJ) hD i

/-- Positivity concerns the actual trace on every actual simple object. -/
theorem positiveOfGlobalEq_positive (hJ : J.Spherical)
    (hD : (J.pivotalData S).globalDimension.re = S.fusionBasis.totalFPdim) :
    (J.positiveOfGlobalEq S hJ hD).Positive := by
  intro X hX
  letI := hX
  obtain ⟨i, ⟨e⟩⟩ := S.simple_isomorphic_representative X
  rw [(J.positiveOfGlobalEq S hJ hD).rightDim_iso e,
    J.positiveOfGlobalEq_rightDim_simple S hJ hD]
  exact ⟨S.fusionBasis.fpdim_pos i, rfl⟩

/-- Pseudounitary global-dimension equality produces the unique actual
positive coherent pivotal structure, with no positive-pivotal existence
premise. -/
theorem exists_unique_positive_of_global_eq (hJ : J.Spherical)
    (hD : (J.pivotalData S).globalDimension.re = S.fusionBasis.totalFPdim) :
    ∃! K : PivotalStructure C, K.Positive := by
  refine ⟨J.positiveOfGlobalEq S hJ hD, J.positiveOfGlobalEq_positive S hJ hD, ?_⟩
  intro K hK
  exact K.eq_of_positive (J.positiveOfGlobalEq S hJ hD) S hK
    (J.positiveOfGlobalEq_positive S hJ hD)

/-- The given spherical structure differs from the constructed positive
one by a sign character extracted from their actual pivotal quotient. -/
theorem exists_positive_sign_of_global_eq (hJ : J.Spherical)
    (hD : (J.pivotalData S).globalDimension.re = S.fusionBasis.totalFPdim) :
    ∃ K : PivotalStructure C, K.Positive ∧ K.Spherical ∧
      ∃ χ : Paper18.SignCharacter S.fusionBasis,
        ∀ i, J.rightDim (S.simpleObject i) = χ.val i * (S.fusionBasis.fpdim i : ℂ) := by
  let K := J.positiveOfGlobalEq S hJ hD
  have hp : K.Positive := J.positiveOfGlobalEq_positive S hJ hD
  have hs : K.Spherical := J.positiveOfGlobalEq_spherical S hJ hD
  refine ⟨K, hp, hs, J.signCharacter K S hJ hs, ?_⟩
  intro i
  exact J.rightDim_eq_sign_mul_fpdim K S hp i

/-- The sign comparison determines the entire actual monoidal natural
automorphism, including all nonsimple objects and all morphisms. -/
theorem ratio_eq_signNatIso (K : PivotalStructure C)
    (hJ : J.Spherical) (hK : K.Spherical) :
    J.ratio K = S.signNatIso (J.signCharacter K S hJ hK) := by
  apply TensorAutomorphism.ext_simple (J.ratio K) _ S
  intro i
  rw [S.signNatIso_scalar]
  rfl

include S in
/-- The actual comparison of two spherical structures has order at most
two on every object, as a consequence of the derived sign character. -/
theorem ratio_involutive (K : PivotalStructure C)
    (hJ : J.Spherical) (hK : K.Spherical) (X : C) :
    (J.ratio K).hom.app X ≫ (J.ratio K).hom.app X = 𝟙 X := by
  rw [J.ratio_eq_signNatIso S K hJ hK]
  exact S.signNatIso_involutive _ X

/-- The constructed positive structure compares with the prescribed one
by the actual natural automorphism obtained from its sign character. -/
theorem exists_positive_actual_sign_of_global_eq (hJ : J.Spherical)
    (hD : (J.pivotalData S).globalDimension.re = S.fusionBasis.totalFPdim) :
    ∃ K : PivotalStructure C, K.Positive ∧ K.Spherical ∧
      ∃ χ : Paper18.SignCharacter S.fusionBasis,
        J.ratio K = S.signNatIso χ ∧
        ∀ i, J.rightDim (S.simpleObject i) = χ.val i * (S.fusionBasis.fpdim i : ℂ) := by
  let K := J.positiveOfGlobalEq S hJ hD
  have hp : K.Positive := J.positiveOfGlobalEq_positive S hJ hD
  have hs : K.Spherical := J.positiveOfGlobalEq_spherical S hJ hD
  refine ⟨K, hp, hs, J.signCharacter K S hJ hs,
    J.ratio_eq_signNatIso S K hJ hs, ?_⟩
  intro i
  exact J.rightDim_eq_sign_mul_fpdim K S hp i

end Paper18.Category.PivotalStructure
