import Paper18.Results.CategoricalCaseOneModules
import Paper18.Category.TannakianPositive
import Paper18.Category.TannakianDeequivariantNondegenerate
import Paper18.Category.ModuleBalancingSeparable
import Paper18.Results.CategoricalSigns

/-! # Case 1 integrality for the actual Tannakian center

Every categorical ingredient used here is constructed from the actual
Tannakian identification: the regular separable algebra, its positive
descended pivotal structure and the nondegenerate de-equivariantization.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [RightRigidCategory C] [HasCoequalizers C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {G : Type} [Group G]

/-- The actual categorical Case 1 conclusion. No de-equivariant category,
positive module structure, nondegeneracy, odd invertible, grading law, or
even-module integrality is supplied as an input package. -/
theorem integral_case_one_tannakian
    (J : PivotalStructure C) (hJ : J.Positive) (T : TannakianCenter C G)
    (χ : 𝟭 C ≅ 𝟭 C) [NatTrans.IsMonoidal χ.hom]
    (hχcenter : ∀ X ∈ mugerCenter (C := C), χ.hom.app X = 𝟙 X)
    {e : C} (E : TensorInverse e) (he : e ⊗ e ≅ 𝟙_ C)
    (hχe : χ.hom.app e = (-1 : ℂ) • 𝟙 e)
    (hI : S.CentralizerIntegral {e}) : S.Integral := by
  letI := T.finite_group
  letI := Fintype.ofFinite G
  let R := T.regularAlgebraSeparable
  letI := R.moduleRightRigid
  letI := R.moduleSimpleUnit S T.regularAlgebra_connected
  let hθ := TannakianCenter.regularAlgebra_twist S J hJ T
  let K := ModuleBalancing.modulePivotal J hθ T.regularAlgebra_transparent
  exact integral_of_transparent_condensation_character R S T.regularAlgebra_transparent K
    (T.deequivariant_isNondegenerate S) χ
    (hχcenter T.regularAlgebra T.regularAlgebra_transparent) E he hχe hI

/-- Case 1 for the actual inherited weakly integral spherical category.
The positive structure and the value of its comparison on the negative
boson are both constructed, rather than received as input. -/
theorem integral_case_one_canonical
    (J : PivotalStructure C) (hJ : J.Spherical) (hB : S.fusionBasis.WeaklyIntegral)
    (T : TannakianCenter C G)
    (hcenter : ∀ X ∈ mugerCenter (C := C),
      (J.ratio (J.canonicalPositive S hJ hB)).hom.app X = 𝟙 X)
    {e : C} (E : TensorInverse e) (he : e ⊗ e ≅ 𝟙_ C) (hd : J.rightDim e = -1)
    (hI : S.CentralizerIntegral {e}) : S.Integral :=
  integral_case_one_tannakian S (J.canonicalPositive S hJ hB)
    (J.canonicalPositive_positive S hJ hB) T (J.ratio (J.canonicalPositive S hJ hB))
    hcenter E he (canonicalPositive_comparison_negative S J E hJ hB hd) hI

end Paper18.Category
