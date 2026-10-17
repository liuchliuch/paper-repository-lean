import Paper18.Category.DrinfeldInductionAdjunctionFunctor
import Paper18.Category.DrinfeldBiproducts
import Paper18.Category.FunctorImage

/-!
# Actual FP dimension of the Drinfeld center

An actual finite semisimple skeleton of the center is an explicit parameter.
The dimension-square formula is derived from the genuine induction
adjunction and the actual simple-diagonal coend decomposition. This file
does not assert existence of the center skeleton.
-/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u w t
namespace Paper18.Category.Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (J : PivotalStructure C)

/-- The actual right dual of a chosen simple has the same derived FP dimension. -/
lemma fpdim_simple_rightDual (i : ι) :
    S.fpdim (S.simpleObject i)ᘁ = S.fusionBasis.fpdim i := by
  rw [← S.fpdim_iso (S.dualIso i), S.fpdim_simple]
  exact S.fusionBasis.fpdim_dual i

/-- The actual underlying induction coend has FP dimension equal to the
ambient total dimension times the dimension of its middle input. -/
lemma inductionUnderlying_fpdim (X : C) :
    S.fpdim (inductionUnderlying S X) = S.fusionBasis.totalFPdim * S.fpdim X := by
  rw [S.fpdim_iso (inductionUnderlyingIso S X), S.fpdim_biproduct]
  simp_rw [S.fpdim_tensor, S.fpdim_simple, fpdim_simple_rightDual]
  unfold FusionBasis.totalFPdim
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

section CenterSkeleton
variable [HasKernels (Center C)] [RightRigidCategory (Center C)] [Simple (𝟙_ (Center C))]
  {κ : Type t} [Fintype κ] (T : FiniteSemisimpleSkeleton (Center C) κ)

/-- Actual monoidal forgetting preserves FP dimension, so the coend
calculation computes the intrinsic FP dimension of central induction. -/
lemma induction_fpdim (X : C) :
    T.fpdim (inductionObj S J X) = S.fusionBasis.totalFPdim * S.fpdim X := by
  rw [← T.fpdim_map S (Center.forget C)]
  exact inductionUnderlying_fpdim S X

/-- The genuine induction Hom equivalence transposes the actual simple
multiplicity matrices of induction and forgetting. -/
lemma induction_multiplicity (i : ι) (q : κ) :
    T.multiplicity (inductionObj S J (S.simpleObject i)) q =
      S.multiplicity (T.simpleObject q).1 i := by
  rw [T.multiplicity_eq_finrank_hom]
  exact (inductionHomLinearEquiv S J (S.simpleObject i) (T.simpleObject q)).finrank_eq

include J in
lemma induction_fpdim_sum (i : ι) :
    (∑ q : κ, (S.multiplicity (T.simpleObject q).1 i : ℝ) * T.fusionBasis.fpdim q) =
      S.fusionBasis.totalFPdim * S.fusionBasis.fpdim i := by
  have h := induction_fpdim S J T (S.simpleObject i)
  rw [S.fpdim_simple] at h
  simpa only [FiniteSemisimpleSkeleton.fpdim, induction_multiplicity S J T] using h

include J in
/-- Given an actual fusion-category structure and actual finite semisimple
skeleton of the center, its total FP dimension is the square of the ambient
total FP dimension. No dimension formula is supplied as an input. -/
theorem center_totalFPdim :
    T.fusionBasis.totalFPdim = S.fusionBasis.totalFPdim ^ 2 := by
  have hU (q : κ) :
      (∑ i : ι, (S.multiplicity (T.simpleObject q).1 i : ℝ) * S.fusionBasis.fpdim i) =
        T.fusionBasis.fpdim q := by
    have h := T.fpdim_map_simple S (Center.forget C) q
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
      simp_rw [induction_fpdim_sum S J T]
      simp only [FusionBasis.totalFPdim, Finset.mul_sum, pow_two, mul_assoc]

end CenterSkeleton
end Paper18.Category.Drinfeld
