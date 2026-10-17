import Paper18.Category.SphericalizationFPdim
import Paper18.Category.SphericalComparisonPositive
import Paper18.Category.ENOPseudounitaryBounds
import Paper18.Category.ENOPseudounitaryNumberField

/-! # Intrinsic global dimension through actual sphericalization

Squared dimensions are independent of the actual pivotal structure, because
the actual pivotal quotient is a tensor character and its dual value is its
inverse. The definition below therefore requires no pivotal structure on the
original braided fusion category.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι]
namespace PivotalStructure
variable (J K : PivotalStructure C) (S : FiniteSemisimpleSkeleton C ι)

lemma ndim_pivotalData_eq (i : ι) :
    (J.pivotalData S).ndim i = (K.pivotalData S).ndim i := by
  change J.rightDim (S.simpleObject i) * J.rightDim (S.simpleObject (S.dualLabel i)) = _
  rw [J.rightDim_comparison K, J.rightDim_comparison K,
    J.comparisonScalar_dualLabel K S]
  have hn := J.comparisonScalar_ne_zero K (S.simpleObject i)
  change (_ * _) * (_⁻¹ * _) = _ * _
  field_simp
  rfl

lemma globalDimension_pivotalData_eq :
    (J.pivotalData S).globalDimension = (K.pivotalData S).globalDimension := by
  apply Finset.sum_congr rfl
  intro i _
  exact J.ndim_pivotalData_eq K S i

lemma globalDimension_eq_totalFPdim_of_positive (hJ : J.Positive) :
    (J.pivotalData S).globalDimension = (S.fusionBasis.totalFPdim : ℂ) := by
  simp only [Paper18.PivotalData.globalDimension, Paper18.PivotalData.ndim,
    pivotalData_jdim, J.rightDim_simple_eq_fpdim S hJ]
  change (∑ i, (S.fusionBasis.fpdim i : ℂ) * (S.fusionBasis.fpdim (S.fusionBasis.dual i) : ℂ)) = _
  simp_rw [S.fusionBasis.fpdim_dual]
  simp only [Paper18.FusionBasis.totalFPdim, Complex.ofReal_sum, Complex.ofReal_pow, pow_two, Complex.ofReal_mul]

end PivotalStructure
namespace Sphericalized
variable [BraidedCategory C] (S : FiniteSemisimpleSkeleton C ι)

/-- The global dimension of the original actual braided fusion category,
defined without choosing a pivotal structure on it. -/
def noPivotalGlobalDimension : ℂ :=
  ((pivotalStructure (C := C)).pivotalData (skeleton S)).globalDimension / 2

lemma noPivotalGlobalDimension_im : (noPivotalGlobalDimension S).im = 0 := by
  simp [noPivotalGlobalDimension, Paper18.PivotalData.globalDimension_im_eq_zero]

lemma noPivotalGlobalDimension_re_pos : 0 < (noPivotalGlobalDimension S).re := by
  have h := ((pivotalStructure (C := C)).pivotalData (skeleton S)).globalDimension_re_pos
  simpa [noPivotalGlobalDimension] using (div_pos h (by norm_num : (0 : ℝ) < 2))

lemma noPivotalGlobalDimension_ne_zero : noPivotalGlobalDimension S ≠ 0 := by
  intro h
  have hp := noPivotalGlobalDimension_re_pos S
  rw [h] at hp
  simp at hp

lemma noPivotalGlobalDimension_re_le_totalFPdim :
    (noPivotalGlobalDimension S).re ≤ S.fusionBasis.totalFPdim := by
  have h := ((pivotalStructure (C := C)).pivotalData (skeleton S)).globalDimension_re_le_totalFPdim
  rw [totalFPdim_eq_twice S] at h
  change (_ / (2 : ℂ)).re ≤ _
  rw [Complex.div_ofNat_re]
  linarith

end Sphericalized
end Paper18.Category
