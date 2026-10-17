import Paper18.Category.HopfLinkNondegenerate
import Paper18.Category.HopfLinkMultiplicativeFusion

/-! # Actual Hopf-link inversion and the pivotal Verlinde formula -/
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

/-- The explicit inverse transform of an arbitrary vector follows from the
actual weighted orthogonality of the trace-defined Hopf links. -/
lemma hopfLink_inverse_transform (hC : IsNondegenerate (C := C)) (a : ι → ℂ) (k : ι) :
    ∑ i, (J.rightDim (S.simpleObject (S.dualLabel i)) / J.rightDim (S.simpleObject i)) *
      J.hopfLink (S.simpleObject i) (S.simpleObject (S.dualLabel k)) *
        (∑ j, J.hopfLink (S.simpleObject i) (S.simpleObject j) * a j) =
      (J.pivotalData S).globalDimension * a k := by
  calc
    _ = ∑ j, a j * ∑ i,
        (J.rightDim (S.simpleObject (S.dualLabel i)) / J.rightDim (S.simpleObject i)) *
          J.hopfLink (S.simpleObject i) (S.simpleObject j) *
          J.hopfLink (S.simpleObject i) (S.simpleObject (S.dualLabel k)) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      simp_rw [J.hopfLink_weighted_orthogonality S hC]
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring

/-- Verlinde's formula for actual Hom-defined fusion multiplicities, derived
from actual Hopf-loop multiplication and genuine Müger nondegeneracy.
The dual-dimension factor allows an arbitrary pivotal structure. -/
lemma hopfLink_verlinde (hC : IsNondegenerate (C := C)) (j k l : ι) :
    (S.fusionCoeff j k l : ℂ) = ((J.pivotalData S).globalDimension)⁻¹ *
      ∑ i, (J.rightDim (S.simpleObject (S.dualLabel i)) /
        (J.rightDim (S.simpleObject i) * J.rightDim (S.simpleObject i))) *
          J.hopfLink (S.simpleObject i) (S.simpleObject j) *
          J.hopfLink (S.simpleObject i) (S.simpleObject k) *
          J.hopfLink (S.simpleObject i) (S.simpleObject (S.dualLabel l)) := by
  have h := J.hopfLink_inverse_transform S hC (fun m => (S.fusionCoeff j k m : ℂ)) l
  have hh (i : ι) : (∑ m, J.hopfLink (S.simpleObject i) (S.simpleObject m) *
      (S.fusionCoeff j k m : ℂ)) =
      J.hopfLink (S.simpleObject i) (S.simpleObject j) *
        J.hopfLink (S.simpleObject i) (S.simpleObject k) / J.rightDim (S.simpleObject i) := by
    simpa only [mul_comm] using J.hopfLink_fusion_character S (S.simpleObject i) j k
  simp_rw [hh] at h
  have hr : (∑ i,
      (J.rightDim (S.simpleObject (S.dualLabel i)) / J.rightDim (S.simpleObject i)) *
      J.hopfLink (S.simpleObject i) (S.simpleObject (S.dualLabel l)) *
      (J.hopfLink (S.simpleObject i) (S.simpleObject j) *
        J.hopfLink (S.simpleObject i) (S.simpleObject k) / J.rightDim (S.simpleObject i))) =
      ∑ i, (J.rightDim (S.simpleObject (S.dualLabel i)) /
        (J.rightDim (S.simpleObject i) * J.rightDim (S.simpleObject i))) *
          J.hopfLink (S.simpleObject i) (S.simpleObject j) *
          J.hopfLink (S.simpleObject i) (S.simpleObject k) *
          J.hopfLink (S.simpleObject i) (S.simpleObject (S.dualLabel l)) := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hr] at h
  calc
    _ = ((J.pivotalData S).globalDimension)⁻¹ *
        ((J.pivotalData S).globalDimension * (S.fusionCoeff j k l : ℂ)) := by
      rw [← mul_assoc, inv_mul_cancel₀ (J.pivotalData S).globalDimension_ne_zero, one_mul]
    _ = _ := congrArg (((J.pivotalData S).globalDimension)⁻¹ * ·) h.symm

end PivotalStructure
end Paper18.Category
