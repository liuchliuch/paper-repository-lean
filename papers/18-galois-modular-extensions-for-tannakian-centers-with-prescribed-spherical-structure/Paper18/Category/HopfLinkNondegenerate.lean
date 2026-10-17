import Paper18.Category.HopfLinkNondegenerateOrthogonality

/-!
# Genuine nondegeneracy implies nonvanishing of the actual pivotal Gauss sum

The proof uses the inverse of the trace-defined Hopf-link matrix, obtained
from actual central averaging. No invertibility or nonzero certificate is
assumed, and no sphericality assumption is needed.
-/
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

/-- The actual formula is also a right inverse. -/
lemma hopfLinkMatrix_mul_inverse (hC : IsNondegenerate (C := C)) :
    J.hopfLinkMatrix S * J.hopfLinkInverseMatrix S = 1 :=
  Matrix.mul_eq_one_comm.mp (J.hopfLinkInverseMatrix_mul S hC)

/-- Genuine Müger nondegeneracy produces an actual inverse structure for the
trace-defined Hopf-link matrix. -/
def hopfLinkMatrixInvertible (hC : IsNondegenerate (C := C)) :
    Invertible (J.hopfLinkMatrix S) :=
  Matrix.invertibleOfLeftInverse _ _ (J.hopfLinkInverseMatrix_mul S hC)

/-- The actual pivotal Gauss sum cannot vanish in a Müger nondegenerate
complex-linear braided pivotal fusion category. -/
lemma pivotalGaussSum_ne_zero (hC : IsNondegenerate (C := C)) :
    J.pivotalGaussSum S ≠ 0 := by
  intro ht
  let a : ι → ℂ := fun i => J.twistScalar (S.simpleObject i) *
    J.rightDim (S.simpleObject (S.dualLabel i))
  have ha : (J.hopfLinkMatrix S).mulVec a = 0 := by
    funext j
    change (∑ i, J.hopfLink (S.simpleObject j) (S.simpleObject i) *
      (J.twistScalar (S.simpleObject i) *
        J.rightDim (S.simpleObject (S.dualLabel i)))) = 0
    calc
      _ = ∑ i, J.twistScalar (S.simpleObject i) *
          J.rightDim (S.simpleObject (S.dualLabel i)) *
            J.hopfLink (S.simpleObject i) (S.simpleObject j) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [J.hopfLink_symm]
        ring
      _ = 0 := by rw [J.hopfLink_gauss_identity S j, ht, zero_mul, zero_mul]
  have hz : a = 0 := J.hopfLinkMatrix_mulVec_injective S hC
    (by simpa only [Matrix.mulVec_zero] using ha)
  have hu := congrFun hz S.unitLabel
  exact mul_ne_zero (J.twistScalar_ne_zero (S.simpleObject S.unitLabel))
    (J.rightDim_ne_zero S (S.simpleObject (S.dualLabel S.unitLabel))) hu

end PivotalStructure
end Paper18.Category
