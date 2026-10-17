import Paper18.Category.DrinfeldNoPivotalDimensionBasic
import Paper18.Category.DrinfeldCoendModulesAdjunction

/-! # The actual center dimension square without a pivotal structure

The actual separable coend constructs the induction adjunction and the
center skeleton. Actual Hom multiplicities transpose the induction and
forgetting matrices, and their weighted sums give the dimension square.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
universe v u w t
namespace Paper18.Category.DrinfeldCoendModules
attribute [local instance 2000] RightRigidCategory.rightDual
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)
  {κ : Type t} [Fintype κ] (T : FiniteSemisimpleSkeleton (Center D) κ)

theorem induction_fpdim_noPivotal (X : D) :
    T.fpdim ((inductionNoPivotal S).obj X) =
      S.fusionBasis.totalFPdim * S.fpdim X := by
  rw [← T.fpdim_map S (Center.forget D)]
  change S.fpdim (algebra S ⊗ X) = _
  rw [S.fpdim_tensor, algebra_fpdim S]

theorem induction_multiplicity_noPivotal (i : ι) (q : κ) :
    T.multiplicity ((inductionNoPivotal S).obj (S.simpleObject i)) q =
      S.multiplicity (T.simpleObject q).1 i := by
  rw [T.multiplicity_eq_finrank_hom]
  exact (inductionHomLinearEquivNoPivotal S (S.simpleObject i) (T.simpleObject q)).finrank_eq

theorem induction_fpdim_sum_noPivotal (i : ι) :
    (∑ q : κ, (S.multiplicity (T.simpleObject q).1 i : ℝ) * T.fusionBasis.fpdim q) =
      S.fusionBasis.totalFPdim * S.fusionBasis.fpdim i := by
  have h := induction_fpdim_noPivotal S T (S.simpleObject i)
  rw [S.fpdim_simple] at h
  simpa only [FiniteSemisimpleSkeleton.fpdim, induction_multiplicity_noPivotal S T] using h

/-- The actual center's intrinsic FP dimension is the square of the
actual ambient dimension, without any pivotal or spherical premise. -/
theorem center_totalFPdim_noPivotal :
    T.fusionBasis.totalFPdim = S.fusionBasis.totalFPdim ^ 2 := by
  have hU (q : κ) :
      (∑ i : ι, (S.multiplicity (T.simpleObject q).1 i : ℝ) * S.fusionBasis.fpdim i) =
        T.fusionBasis.fpdim q := by
    have h := T.fpdim_map_simple S (Center.forget D) q
    rw [T.fpdim_simple] at h
    exact h
  calc
    T.fusionBasis.totalFPdim =
        ∑ q : κ, T.fusionBasis.fpdim q *
          (∑ i : ι, (S.multiplicity (T.simpleObject q).1 i : ℝ) * S.fusionBasis.fpdim i) := by
      simp_rw [hU]
      simp only [FusionBasis.totalFPdim, pow_two]
    _ = ∑ i : ι, (∑ q : κ,
        (S.multiplicity (T.simpleObject q).1 i : ℝ) * T.fusionBasis.fpdim q) *
          S.fusionBasis.fpdim i := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ = S.fusionBasis.totalFPdim ^ 2 := by
      simp_rw [induction_fpdim_sum_noPivotal S T]
      simp only [FusionBasis.totalFPdim, Finset.mul_sum, pow_two, mul_assoc]

/-- The constructed actual center skeleton satisfies the dimension-square
identity, with no skeleton-existence assumption. -/
theorem constructed_center_totalFPdim_noPivotal :
    (centerSkeletonNoPivotal S).fusionBasis.totalFPdim = S.fusionBasis.totalFPdim ^ 2 :=
  center_totalFPdim_noPivotal S (centerSkeletonNoPivotal S)

end Paper18.Category.DrinfeldCoendModules
