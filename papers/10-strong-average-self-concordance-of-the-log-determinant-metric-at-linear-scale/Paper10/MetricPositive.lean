import Paper10.CongruenceCoordinates
import Paper10.LogDet
import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
namespace Paper10
variable {q : ℕ}

/-- The Frobenius quadratic form is nondegenerate on the full symmetric space. -/
theorem frobNormSq_eq_zero_iff (U : Matrix (Fin q) (Fin q) ℝ) (hU : U.IsSymm) :
    frobNormSq U = 0 ↔ U = 0 := by
  have he : frobNormSq U = ∑ i, ∑ j, U i j ^ 2 := by
    rw [frobNormSq_eq_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hU.apply i j]
    ring
  constructor
  · intro hz
    ext i j
    have hrow : U i j ^ 2 ≤ ∑ k, U i k ^ 2 := Finset.single_le_sum
      (fun k _ => sq_nonneg _) (Finset.mem_univ j)
    have hfull : (∑ k, U i k ^ 2) ≤ ∑ l, ∑ k, U l k ^ 2 := Finset.single_le_sum
      (fun l _ => Finset.sum_nonneg (fun k _ => sq_nonneg _)) (Finset.mem_univ i)
    rw [← he, hz] at hfull
    change U i j = 0
    nlinarith [sq_nonneg (U i j)]
  · rintro rfl
    simp [frobNormSq, frob]

/-- Positive definiteness of the actual log-determinant Hessian metric at every base point. -/
theorem localNormSq_pos (X H : Matrix (Fin q) (Fin q) ℝ) (hX : X.PosDef) (hH : H.IsSymm)
    {s : ℝ} (hs : 0 < s) (hH0 : H ≠ 0) : 0 < localNormSq s X H := by
  obtain ⟨R, K, hR, hK, hx, hh⟩ := congruence_coordinates_complete X H hX hH
  have hK0 : K ≠ 0 := by
    intro hz
    apply hH0
    simpa only [hz, Matrix.mul_zero, Matrix.zero_mul] using hh
  have hf : 0 < frobNormSq K := lt_of_le_of_ne (frobNormSq_nonneg hK)
    (Ne.symm (fun hz => hK0 ((frobNormSq_eq_zero_iff K hK).mp hz)))
  rw [hx, hh, localNormSq_frame R K hR]
  exact mul_pos hs hf

/-- The actual metric is C^k at every positive definite point, for every finite k. -/
theorem contDiffAt_metric (s : ℝ) (U V X : Matrix (Fin q) (Fin q) ℝ) (hX : X.PosDef) (k : ℕ) :
    ContDiffAt ℝ k (fun Y : Matrix (Fin q) (Fin q) ℝ => g s Y U V) X := by
  have hi : ContDiffAt ℝ k (fun Y : Matrix (Fin q) (Fin q) ℝ => Y⁻¹) X := by
    simpa only [hX.isUnit.unit_spec, Matrix.nonsing_inv_eq_ringInverse] using
      (contDiffAt_ringInverse ℝ (n := k) hX.isUnit.unit)
  have hm := ((hi.mul (contDiffAt_const (c := U))).mul hi).mul (contDiffAt_const (c := V))
  let tr : Matrix (Fin q) (Fin q) ℝ →L[ℝ] ℝ :=
    (Matrix.traceLinearMap (Fin q) ℝ ℝ).toContinuousLinearMap
  have ht := tr.contDiff.contDiffAt.comp X (show ContDiffAt ℝ k (fun Y => Y⁻¹ * U * Y⁻¹ * V) X from hm)
  exact (contDiffAt_const (c := s)).mul ht

end Paper10
