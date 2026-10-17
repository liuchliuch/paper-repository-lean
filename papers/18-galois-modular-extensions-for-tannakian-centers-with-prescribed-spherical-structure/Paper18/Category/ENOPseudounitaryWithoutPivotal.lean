import Paper18.Category.SphericalizationPositiveKernelForget
import Paper18.Results.CategoricalCaseTwoPivotal
import Paper18.Category.PositiveMonoidalFunctor

/-! # Positive pivotal existence without an initial pivotal structure

Equality of the actual squared dimension and FP dimension of the canonical
sphericalization constructs its positive pivotal structure. The actual
positive sign kernel forgets equivalently onto the original category, so
its inherited positive pivotal structure supplies the original category's
positive pivotal structure. No pivotal existence premise is used.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category.FiniteSemisimpleSkeleton
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- The actual equality criterion constructs an actual positive pivotal
structure on a braided fusion category having no chosen pivotal structure. -/
theorem exists_positive_of_sphericalizationGlobalEq
    (hD : ((Sphericalized.pivotalStructure (C := C)).pivotalData
      (Sphericalized.skeleton S)).globalDimension.re =
        (Sphericalized.skeleton S).fusionBasis.totalFPdim) :
    ∃ J : PivotalStructure C, J.Positive := by
  let SS := Sphericalized.skeleton S
  let JS := Sphericalized.pivotalStructure (C := C)
  have hJS : JS.Spherical := Sphericalized.pivotalStructure_spherical
  let K := JS.positiveOfGlobalEq SS hJS hD
  have hpK : K.Positive := JS.positiveOfGlobalEq_positive SS hJS hD
  have hsK : K.Spherical := JS.positiveOfGlobalEq_spherical SS hJS hD
  let χ := JS.ratio K
  have hχ : ∀ X, χ.hom.app X ≫ χ.hom.app X = 𝟙 X :=
    comparison_involutive SS JS K hJS hsK
  have hε : χ.hom.app (Sphericalized.negativeGenerator (C := C)) = (-1 : ℂ) • 𝟙 _ :=
    comparison_negative_invertible SS JS K Sphericalized.negativeGeneratorTensorInverse
      hpK (Sphericalized.negativeGenerator_rightDim S)
  letI := SignKernel.hasKernels χ SS
  letI := SignKernel.rightRigid χ SS
  letI := SignKernel.simpleUnit χ SS
  let F := Sphericalized.positiveForget χ
  letI : F.IsEquivalence := Sphericalized.positiveForget_isEquivalence S χ hχ hε
  let E := F.asEquivalence
  letI : E.functor.Monoidal := inferInstanceAs F.Monoidal
  letI : E.functor.Additive := inferInstanceAs F.Additive
  letI : E.functor.Linear ℂ := inferInstanceAs (F.Linear ℂ)
  letI : E.inverse.Monoidal := E.inverseMonoidal
  letI : E.inverse.Additive := Equivalence.inverse_additive E
  letI : E.inverse.Linear ℂ := Equivalence.inverseLinear ℂ E
  let JE := SignKernel.pivotal χ SS JS
  have hpE : JE.Positive := ratio_positive_kernel_positive SS JS K hpK
  exact ⟨pivotalPullbackMonoidal E.inverse JE,
    pivotalPullbackMonoidal_positive E.inverse JE (SignKernel.skeleton χ SS) hpE⟩

/-- Uniqueness follows from actual positive-pivotal comparison; the result
includes actual existence, rather than a dimension-only positive character. -/
theorem exists_unique_positive_of_sphericalizationGlobalEq
    (hD : ((Sphericalized.pivotalStructure (C := C)).pivotalData
      (Sphericalized.skeleton S)).globalDimension.re =
        (Sphericalized.skeleton S).fusionBasis.totalFPdim) :
    ∃! J : PivotalStructure C, J.Positive := by
  obtain ⟨J, hJ⟩ := S.exists_positive_of_sphericalizationGlobalEq hD
  exact ⟨J, hJ, fun K hK => K.eq_of_positive J S hK hJ⟩


/-- Weak integrality of the original category doubles to weak integrality
of its actual canonical sphericalization. -/
lemma sphericalization_weaklyIntegral (h : S.fusionBasis.WeaklyIntegral) :
    (Sphericalized.skeleton S).fusionBasis.WeaklyIntegral := by
  obtain ⟨n, hn⟩ := h
  refine ⟨2 * n, ?_⟩
  rw [Sphericalized.totalFPdim_eq_twice S, hn]
  push_cast
  rfl

/-- The actual weak-integral positive-existence theorem needs no initial
pivotal or spherical structure on the original braided fusion category. -/
theorem exists_unique_positive_of_weakIntegral_withoutPivotal
    (h : S.fusionBasis.WeaklyIntegral) :
    ∃! J : PivotalStructure C, J.Positive := by
  apply S.exists_unique_positive_of_sphericalizationGlobalEq
  exact Sphericalized.pivotalStructure.globalDimension_eq_totalFPdim_of_weakIntegral
    (Sphericalized.skeleton S) (S.sphericalization_weaklyIntegral h)

/-- Actual integral fusion categories have integer total FP dimension. -/
lemma weaklyIntegral_of_integral (h : S.Integral) : S.fusionBasis.WeaklyIntegral := by
  have hi := S.integral_iff_basis.mp h
  choose n hn using hi
  refine ⟨∑ i, n i ^ 2, ?_⟩
  simp only [Paper18.FusionBasis.totalFPdim, Int.cast_sum, Int.cast_pow]
  simp_rw [hn]

/-- In particular actual integrality supplies an actual positive pivotal
structure, with no pivotal existence certificate as a premise. -/
theorem exists_unique_positive_of_integral_withoutPivotal (h : S.Integral) :
    ∃! J : PivotalStructure C, J.Positive :=
  S.exists_unique_positive_of_weakIntegral_withoutPivotal (S.weaklyIntegral_of_integral h)

end Paper18.Category.FiniteSemisimpleSkeleton
