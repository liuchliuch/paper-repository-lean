import Paper18.Category.HopfLinkBasic

/-!
# The Gauss-sum transform identity for actual Hopf links

This identity is proved from the derived categorical Hopf-link formula and
Frobenius reciprocity. No HopfLinkIdentity certificate or supplied S-matrix
is part of its statement.
-/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18

/-- Frobenius reciprocity and the dimension character evaluate the dual
dimension weighted column of a fusion matrix. -/
lemma fusion_dual_dimension_sum {ι : Type w} [Fintype ι] {B : FusionBasis ι}
    (D : PivotalData B) (j k : ι) :
    ∑ i, (B.N i j k : ℂ) * D.jdim (B.dual i) = D.jdim (B.dual k) * D.jdim j := by
  have hn (i : ι) : B.N i j k = B.N j (B.dual k) (B.dual i) := by
    calc
      _ = B.N k (B.dual j) i := B.N_right i j k
      _ = B.N (B.dual k) i (B.dual j) := B.N_dual k (B.dual j) i
      _ = B.N (B.dual j) (B.dual i) (B.dual k) := B.N_right (B.dual k) i (B.dual j)
      _ = _ := by rw [B.N_dual, B.dual_involutive]
  simp_rw [hn]
  let e : ι ≃ ι := ⟨B.dual, B.dual, B.dual_involutive, B.dual_involutive⟩
  calc
    _ = ∑ i, (B.N j (B.dual k) i : ℂ) * D.jdim i :=
      Equiv.sum_comp e (fun i => (B.N j (B.dual k) i : ℂ) * D.jdim i)
    _ = D.jdim j * D.jdim (B.dual k) := (D.jdim_tensor j (B.dual k)).symm
    _ = _ := mul_comm _ _

namespace Category
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)] [BraidedCategory C]
  {ι : Type w} [Fintype ι]

namespace PivotalStructure
variable (J : PivotalStructure C) (S : FiniteSemisimpleSkeleton C ι)

/-- The actual pivotal Gauss sum, defined from actual twist scalars and traces. -/
def pivotalGaussSum : ℂ := ∑ i, J.twistScalar (S.simpleObject i) *
  (J.rightDim (S.simpleObject i) * J.rightDim (S.simpleObject (S.dualLabel i)))

/-- The Hopf-link Gauss transform identity used in Lemma 2.1, now proved
for the actual categorical traces and induced twist. -/
lemma hopfLink_gauss_identity (j : ι) :
    (∑ i, J.twistScalar (S.simpleObject i) *
      J.rightDim (S.simpleObject (S.dualLabel i)) *
      J.hopfLink (S.simpleObject i) (S.simpleObject j)) =
    J.pivotalGaussSum S * J.rightDim (S.simpleObject j) *
      (J.twistScalar (S.simpleObject j))⁻¹ := by
  let t := fun i => J.twistScalar (S.simpleObject i)
  let d := fun i => J.rightDim (S.simpleObject i)
  have ht (i : ι) : t i ≠ 0 := J.twistScalar_ne_zero (S.simpleObject i)
  have hn (k : ι) : (∑ i, (S.fusionCoeff i j k : ℂ) * d (S.dualLabel i)) =
      d (S.dualLabel k) * d j := fusion_dual_dimension_sum (J.pivotalData S) j k
  change (∑ i, t i * d (S.dualLabel i) *
    J.hopfLink (S.simpleObject i) (S.simpleObject j)) = _
  calc
    _ = ∑ i, (t j)⁻¹ * ∑ k, (t k * d k) *
        ((S.fusionCoeff i j k : ℂ) * d (S.dualLabel i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [J.hopfLink_fusion_formula S i j]
      change t i * d (S.dualLabel i) *
          ((t i * t j)⁻¹ * ∑ k, (S.fusionCoeff i j k : ℂ) * (t k * d k)) = _
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      field_simp [ht i, ht j]
    _ = (t j)⁻¹ * ∑ k, (t k * d k) *
        (∑ i, (S.fusionCoeff i j k : ℂ) * d (S.dualLabel i)) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = (t j)⁻¹ * ∑ k, (t k * d k) * (d (S.dualLabel k) * d j) := by simp_rw [hn]
    _ = _ := by
      change _ = (∑ k, t k * (d k * d (S.dualLabel k))) * d j * (t j)⁻¹
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring

end PivotalStructure
end Category
end Paper18
