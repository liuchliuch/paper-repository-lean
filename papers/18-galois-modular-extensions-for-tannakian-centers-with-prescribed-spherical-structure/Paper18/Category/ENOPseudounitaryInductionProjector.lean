import Paper18.Category.ENOPseudounitaryProjector
import Paper18.Category.ENOPseudounitaryInductionUnit
import Paper18.Category.ENOPseudounitaryReduction

/-!
# The actual FP projection on central induction

The fusion action here is the constructed loop action on the actual
central-induction object. Its fusion laws are proved from cups, caps and
the actual adjunction. The projection and its integral pivotal trace are
unconditional. Identifying that trace with the global-dimension ratio is
reduced to the explicitly stated nonunit-loop vanishing calculation, which
is proved in `DrinfeldLoopTrace` and consumed in `ENOPseudounitary`.
-/

noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category.Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι) (J : PivotalStructure C)

omit [Simple (𝟙_ C)] in
/-- Forgetting the actual central loop action preserves its proved fusion
multiplication as actual underlying morphisms. -/
theorem inductionLoop_underlying_fusion (i j : ι) :
    (inductionLoop S J (S.simpleObject i)).f ≫
        (inductionLoop S J (S.simpleObject j)).f =
      ∑ k, (S.fusionCoeff i j k : ℂ) • (inductionLoop S J (S.simpleObject k)).f := by
  calc
    _ = (Center.forget C).map (inductionLoop S J (S.simpleObject i) ≫
        inductionLoop S J (S.simpleObject j)) := rfl
    _ = (Center.forget C).map
        (∑ k, (S.fusionCoeff i j k : ℂ) • inductionLoop S J (S.simpleObject k)) :=
      congrArg ((Center.forget C).map) (inductionLoop_fusion S J i j)
    _ = _ := by rw [Functor.map_sum]; simp only [Functor.map_smul]; rfl

/-- The actual FP projection on the underlying induction object. -/
def inductionFPProjection : inductionUnderlying S (𝟙_ C) ⟶ inductionUnderlying S (𝟙_ C) :=
  PivotalStructure.fpProjection S (fun i => (inductionLoop S J (S.simpleObject i)).f)

/-- The projection law follows from the actual coend loop multiplication. -/
theorem inductionFPProjection_idempotent :
    inductionFPProjection S J ≫ inductionFPProjection S J = inductionFPProjection S J :=
  PivotalStructure.fpProjection_idempotent S _ (inductionLoop_underlying_fusion S J)

/-- The same FP projection is an actual morphism of the Drinfeld center,
since every loop is central and the actual center is complex-linear. -/
def inductionFPProjectionHom : inductionObj S J (𝟙_ C) ⟶ inductionObj S J (𝟙_ C) :=
  (S.fusionBasis.totalFPdim : ℂ)⁻¹ •
    ∑ i, (S.fusionBasis.fpdim i : ℂ) • inductionLoop S J (S.simpleObject i)

@[simp] theorem inductionFPProjectionHom_f :
    (inductionFPProjectionHom S J).f = inductionFPProjection S J := by
  change (Center.forget C).map
    ((S.fusionBasis.totalFPdim : ℂ)⁻¹ •
      ∑ i, (S.fusionBasis.fpdim i : ℂ) • inductionLoop S J (S.simpleObject i)) =
      (S.fusionBasis.totalFPdim : ℂ)⁻¹ •
        ∑ i, (S.fusionBasis.fpdim i : ℂ) • (inductionLoop S J (S.simpleObject i)).f
  rw [Functor.map_smul, Functor.map_sum]
  simp only [Functor.map_smul]
  rfl

/-- The central idempotence equation is inherited from its proved actual
underlying equation by faithfulness. -/
theorem inductionFPProjectionHom_idempotent :
    inductionFPProjectionHom S J ≫ inductionFPProjectionHom S J = inductionFPProjectionHom S J := by
  apply Center.ext
  simp only [Center.comp_f, inductionFPProjectionHom_f, inductionFPProjection_idempotent]

/-- Its actual pivotal trace is integral because it is the dimension of an
actual split image in the original finite semisimple category. -/
theorem inductionFPProjection_trace_isIntegral :
    IsIntegral ℤ (unitScalarEquiv (C := C) (J.rightTrace (inductionFPProjection S J))) :=
  J.rightTrace_idempotent_isIntegral S _ (inductionFPProjection_idempotent S J)

/-- The reduction to the nonunit simple-loop trace identity. The unit case
is already proved above; `DrinfeldLoopTrace` discharges this explicit input. -/
theorem dimensionRatio_isIntegral_of_loop_vanishing
    (htrace : ∀ i, i ≠ S.unitLabel →
      unitScalarEquiv (C := C) (J.rightTrace (inductionLoop S J (S.simpleObject i)).f) = 0) :
    IsIntegral ℤ ((J.pivotalData S).globalDimension / (S.fusionBasis.totalFPdim : ℂ)) := by
  apply J.ratio_isIntegral_of_fusion_trace S
    (fun i => (inductionLoop S J (S.simpleObject i)).f)
    (J.pivotalData S).globalDimension (inductionLoop_underlying_fusion S J)
  intro i
  by_cases hi : i = S.unitLabel
  · subst i
    simpa only [PivotalStructure.scalarRightTrace_apply, if_true] using
      inductionLoop_rightTrace_unitLabel S J
  · simpa only [PivotalStructure.scalarRightTrace_apply, if_neg hi] using htrace i hi

/-- With the concrete nonunit coend trace identity, the constructed actual
projection, number field argument and coherent sign correction give the
unique actual positive pivotal structure. -/
theorem exists_unique_positive_of_weakIntegral_of_loop_vanishing
    (hJ : J.Spherical) (hB : S.fusionBasis.WeaklyIntegral)
    (htrace : ∀ i, i ≠ S.unitLabel →
      unitScalarEquiv (C := C) (J.rightTrace (inductionLoop S J (S.simpleObject i)).f) = 0) :
    ∃! K : PivotalStructure C, K.Positive :=
  J.exists_unique_positive_of_weakIntegral_of_ratioIntegral S hJ hB
    (dimensionRatio_isIntegral_of_loop_vanishing S J htrace)

/-- The comparison sign in the same reduction is an equality of the
actual natural isomorphisms, and scales the actual categorical trace. -/
theorem exists_positive_actual_sign_of_weakIntegral_of_loop_vanishing
    (hJ : J.Spherical) (hB : S.fusionBasis.WeaklyIntegral)
    (htrace : ∀ i, i ≠ S.unitLabel →
      unitScalarEquiv (C := C) (J.rightTrace (inductionLoop S J (S.simpleObject i)).f) = 0) :
    ∃ K : PivotalStructure C, K.Positive ∧ K.Spherical ∧
      ∃ χ : Paper18.SignCharacter S.fusionBasis,
        J.ratio K = S.signNatIso χ ∧
        ∀ i, J.rightDim (S.simpleObject i) = χ.val i * (S.fusionBasis.fpdim i : ℂ) :=
  J.exists_positive_actual_sign_of_global_eq S hJ
    ((J.pivotalData S).globalDimension_eq_of_weakIntegral_and_ratioIntegral hB
      (dimensionRatio_isIntegral_of_loop_vanishing S J htrace))

end Paper18.Category.Drinfeld
