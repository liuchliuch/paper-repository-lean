import Paper18.Category.DrinfeldLoopTrace
import Paper18.Category.ENOPseudounitaryInductionProjector
import Paper18.Category.ENOPseudounitaryWeakIntegralSquares

/-!
# Actual weakly integral pseudounitarity and the positive spherical structure

The categorical ratio-integrality theorem is proved using the constructed
fusion-loop action on actual central induction, its proved pivotal trace,
and the actual FP projection. Splitting the underlying idempotent identifies
its trace with an algebraic-integer categorical dimension. The finite number
field norm argument then gives equality of global and FP dimensions for a
weakly integral fusion category. An actual coherent sign correction of the
prescribed spherical structure constructs the unique positive spherical
structure. No positive structure or dimension equality is supplied as input.

This proves the spherical-input form of ENO Propositions 8.22--8.24 through
the actual categorical constructions above, without an S-matrix premise.
-/

noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category.PivotalStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (J : PivotalStructure C) (S : FiniteSemisimpleSkeleton C ι)

/-- ENO 8.22: the actual categorical global dimension divided by the
derived total FP dimension is an algebraic integer. -/
theorem globalDimensionRatio_isIntegral :
    IsIntegral ℤ ((J.pivotalData S).globalDimension / (S.fusionBasis.totalFPdim : ℂ)) := by
  apply Drinfeld.dimensionRatio_isIntegral_of_loop_vanishing S J
  intro i hi
  simpa only [if_neg hi] using Drinfeld.inductionLoop_rightTrace S J i

/-- ENO 8.24: weak integrality forces equality of the actual categorical
global dimension and the derived total FP dimension. -/
theorem globalDimension_eq_totalFPdim_of_weakIntegral (hB : S.fusionBasis.WeaklyIntegral) :
    (J.pivotalData S).globalDimension.re = S.fusionBasis.totalFPdim :=
  (J.pivotalData S).globalDimension_eq_of_weakIntegral_and_ratioIntegral hB
    (J.globalDimensionRatio_isIntegral S)

/-- The actual positive pivotal structure is a coherent sign correction
of the prescribed spherical structure, constructed from the actual global
dimension theorem and actual finite simple decompositions. -/
def canonicalPositive (hJ : J.Spherical) (hB : S.fusionBasis.WeaklyIntegral) :
    PivotalStructure C :=
  J.positiveOfGlobalEq S hJ (J.globalDimension_eq_totalFPdim_of_weakIntegral S hB)

theorem canonicalPositive_positive (hJ : J.Spherical) (hB : S.fusionBasis.WeaklyIntegral) :
    (J.canonicalPositive S hJ hB).Positive :=
  J.positiveOfGlobalEq_positive S hJ (J.globalDimension_eq_totalFPdim_of_weakIntegral S hB)

theorem canonicalPositive_spherical (hJ : J.Spherical) (hB : S.fusionBasis.WeaklyIntegral) :
    (J.canonicalPositive S hJ hB).Spherical :=
  J.positiveOfGlobalEq_spherical S hJ (J.globalDimension_eq_totalFPdim_of_weakIntegral S hB)

@[simp] theorem canonicalPositive_rightDim_simple
    (hJ : J.Spherical) (hB : S.fusionBasis.WeaklyIntegral) (i : ι) :
    (J.canonicalPositive S hJ hB).rightDim (S.simpleObject i) =
      (S.fusionBasis.fpdim i : ℂ) :=
  J.positiveOfGlobalEq_rightDim_simple S hJ
    (J.globalDimension_eq_totalFPdim_of_weakIntegral S hB) i

/-- The trace identification extends to every actual object. -/
theorem canonicalPositive_rightDim
    (hJ : J.Spherical) (hB : S.fusionBasis.WeaklyIntegral) (X : C) :
    (J.canonicalPositive S hJ hB).rightDim X = (S.fpdim X : ℂ) :=
  (J.canonicalPositive S hJ hB).rightDim_eq_fpdim S (J.canonicalPositive_positive S hJ hB) X

/-- The constructed positive structure is unique as an actual coherent
natural isomorphism to the double-dual functor. -/
theorem exists_unique_positive_of_weakIntegral
    (hJ : J.Spherical) (hB : S.fusionBasis.WeaklyIntegral) :
    ∃! K : PivotalStructure C, K.Positive :=
  J.exists_unique_positive_of_global_eq S hJ
    (J.globalDimension_eq_totalFPdim_of_weakIntegral S hB)

/-- The actual canonical structure is independent of the prescribed
spherical input used to construct it. -/
theorem canonicalPositive_independent (K : PivotalStructure C)
    (hJ : J.Spherical) (hK : K.Spherical) (hB : S.fusionBasis.WeaklyIntegral) :
    J.canonicalPositive S hJ hB = K.canonicalPositive S hK hB :=
  (J.canonicalPositive S hJ hB).eq_of_positive (K.canonicalPositive S hK hB) S
    (J.canonicalPositive_positive S hJ hB) (K.canonicalPositive_positive S hK hB)

/-- The prescribed spherical structure differs from the constructed
positive structure by an actual monoidal sign automorphism, on every
object and with the derived simple-trace scaling formula. -/
theorem exists_positive_actual_sign_of_weakIntegral
    (hJ : J.Spherical) (hB : S.fusionBasis.WeaklyIntegral) :
    ∃ K : PivotalStructure C, K.Positive ∧ K.Spherical ∧
      ∃ χ : Paper18.SignCharacter S.fusionBasis,
        J.ratio K = S.signNatIso χ ∧
        ∀ i, J.rightDim (S.simpleObject i) = χ.val i * (S.fusionBasis.fpdim i : ℂ) :=
  J.exists_positive_actual_sign_of_global_eq S hJ
    (J.globalDimension_eq_totalFPdim_of_weakIntegral S hB)

end Paper18.Category.PivotalStructure
