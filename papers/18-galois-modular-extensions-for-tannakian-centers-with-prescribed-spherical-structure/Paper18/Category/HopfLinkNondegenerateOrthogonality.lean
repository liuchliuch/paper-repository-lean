import Paper18.Category.HopfLinkNondegenerateLoops
import Paper18.Category.HopfLinkMultiplicative
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Genuine Müger nondegeneracy gives weighted Hopf-link orthogonality -/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)] [BraidedCategory C]
  {ι : Type w} [Fintype ι]
namespace PivotalStructure
variable (J : PivotalStructure C) (S : FiniteSemisimpleSkeleton C ι)

/-- Tracing actual central averaging gives the unit column: the weighted
actual Hopf links detect exactly the actual unit summands of any object. -/
lemma hopfLink_weighted_unit_column (hC : IsNondegenerate (C := C)) (X : C) :
    ∑ i, J.rightDim (S.simpleObject (S.dualLabel i)) *
        J.hopfLink (S.simpleObject i) X =
      (J.pivotalData S).globalDimension * (S.multiplicity X S.unitLabel : ℂ) := by
  let tr : (X ⟶ X) →ₗ[ℂ] ℂ :=
    (unitScalarEquiv (C := C)).toLinearMap.comp (J.rightTraceLinearMap X)
  have ht := congrArg tr (J.hopfProjector_weighted_loops S X)
  simp only [map_smul, map_sum, smul_eq_mul] at ht
  change unitScalarEquiv (C := C) (J.rightTrace (J.hopfProjector S X)) =
    ((J.pivotalData S).globalDimension)⁻¹ *
      ∑ i, J.rightDim (dual C (S.simpleObject i)) *
        unitScalarEquiv (C := C) (J.rightTrace (J.averagingHopfLoop X (S.simpleObject i))) at ht
  simp_rw [J.rightTraceScalar_averagingHopfLoop, J.rightDim_iso (S.dualIso _).symm,
    J.hopfLink_symm X] at ht
  rw [J.rightTraceScalar_hopfProjector S hC] at ht
  have hd := (J.pivotalData S).globalDimension_ne_zero
  calc
    _ = (J.pivotalData S).globalDimension *
        (((J.pivotalData S).globalDimension)⁻¹ *
          ∑ i, J.rightDim (S.simpleObject (S.dualLabel i)) *
            J.hopfLink (S.simpleObject i) X) := by rw [← mul_assoc, mul_inv_cancel₀ hd, one_mul]
    _ = _ := congrArg ((J.pivotalData S).globalDimension * ·) ht.symm

/-- The weighted orthogonality identity is derived from actual central
averaging, actual rigidity and the categorical Hopf-loop tensor law. -/
lemma hopfLink_weighted_orthogonality (hC : IsNondegenerate (C := C)) (j k : ι) :
    ∑ i, (J.rightDim (S.simpleObject (S.dualLabel i)) / J.rightDim (S.simpleObject i)) *
      J.hopfLink (S.simpleObject i) (S.simpleObject j) *
      J.hopfLink (S.simpleObject i) (S.simpleObject (S.dualLabel k)) =
      (J.pivotalData S).globalDimension * if j = k then 1 else 0 := by
  have h := J.hopfLink_weighted_unit_column S hC
    (S.simpleObject j ⊗ S.simpleObject (S.dualLabel k))
  have hm : S.multiplicity (S.simpleObject j ⊗ S.simpleObject (S.dualLabel k)) S.unitLabel =
      if j = k then 1 else 0 := by
    change S.fusionCoeff j (S.dualLabel k) S.unitLabel = _
    rw [S.fusionCoeff_right, S.dualLabel_involutive,
      S.fusionCoeff_one_left S.unitLabel S.unitIso]
    simp only [eq_comm]
  rw [hm] at h
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero] at h
  simp_rw [J.hopfLink_tensor S] at h
  calc
    _ = ∑ i, J.rightDim (S.simpleObject (S.dualLabel i)) *
        (J.hopfLink (S.simpleObject i) (S.simpleObject j) *
          J.hopfLink (S.simpleObject i) (S.simpleObject (S.dualLabel k)) /
            J.rightDim (S.simpleObject i)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := h

/-- The actual Hopf-link matrix, formed from pivotal traces of actual double braidings. -/
def hopfLinkMatrix : Matrix ι ι ℂ :=
  fun i j => J.hopfLink (S.simpleObject i) (S.simpleObject j)

/-- The inverse predicted by the actual weighted orthogonality identity. -/
def hopfLinkInverseMatrix : Matrix ι ι ℂ := fun j i =>
  ((J.pivotalData S).globalDimension)⁻¹ *
    (J.rightDim (S.simpleObject (S.dualLabel i)) / J.rightDim (S.simpleObject i)) *
      J.hopfLink (S.simpleObject i) (S.simpleObject (S.dualLabel j))

/-- Actual weighted orthogonality supplies a left inverse of the actual
Hopf-link matrix, with no S-matrix invertibility premise. -/
lemma hopfLinkInverseMatrix_mul (hC : IsNondegenerate (C := C)) :
    J.hopfLinkInverseMatrix S * J.hopfLinkMatrix S = 1 := by
  ext j k
  change (∑ i, (((J.pivotalData S).globalDimension)⁻¹ *
    (J.rightDim (S.simpleObject (S.dualLabel i)) / J.rightDim (S.simpleObject i)) *
      J.hopfLink (S.simpleObject i) (S.simpleObject (S.dualLabel j))) *
        J.hopfLink (S.simpleObject i) (S.simpleObject k)) = if j = k then 1 else 0
  calc
    _ = ((J.pivotalData S).globalDimension)⁻¹ *
        ∑ i, (J.rightDim (S.simpleObject (S.dualLabel i)) / J.rightDim (S.simpleObject i)) *
          J.hopfLink (S.simpleObject i) (S.simpleObject k) *
          J.hopfLink (S.simpleObject i) (S.simpleObject (S.dualLabel j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [J.hopfLink_weighted_orthogonality S hC k j, ← mul_assoc,
        inv_mul_cancel₀ (J.pivotalData S).globalDimension_ne_zero, one_mul]
      simp only [eq_comm]

/-- The actual Hopf-link matrix is invertible under genuine Müger nondegeneracy. -/
lemma hopfLinkMatrix_isUnit (hC : IsNondegenerate (C := C)) :
    IsUnit (J.hopfLinkMatrix S) :=
  Matrix.isUnit_of_left_inverse (J.hopfLinkInverseMatrix_mul S hC)

/-- The actual Hopf-link transform is injective under genuine Müger nondegeneracy. -/
lemma hopfLinkMatrix_mulVec_injective (hC : IsNondegenerate (C := C)) :
    Function.Injective (J.hopfLinkMatrix S).mulVec :=
  Matrix.mulVec_injective_iff_isUnit.mpr (J.hopfLinkMatrix_isUnit S hC)

end PivotalStructure
end Paper18.Category
