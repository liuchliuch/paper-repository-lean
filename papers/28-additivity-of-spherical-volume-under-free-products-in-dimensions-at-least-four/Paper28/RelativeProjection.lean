import Paper28.FoldingDifferential
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add

/-! The paper-owned finite local projection construction in Lemma 5.1.
The map is the actual weighted sum of coordinate projections. Its relative
fixing and sharp error/derivative estimates are proved from that formula. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open scoped InnerProductSpace
variable {J H : Type*} [Fintype J] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def weightedProjection (φ : J → H → ℝ) (P : J → H →L[ℝ] H) (u : H) : H :=
  ∑ j, φ j u • P j u

/-- Error form of the actual derivative; the zero sum of the weight
derivatives removes the identity contribution from the second sum. -/
def weightedProjectionDerivative (φ : J → H → ℝ)
    (dφ : J → H → H →L[ℝ] ℝ) (P : J → H →L[ℝ] H) (u : H) : H →L[ℝ] H :=
  (∑ j, φ j u • P j) + ∑ j, (dφ j u).smulRight (P j u - u)

theorem weightedProjection_sub (φ : J → H → ℝ) (P : J → H →L[ℝ] H) (u : H)
    (hSum : ∑ j, φ j u = 1) :
    weightedProjection φ P u - u = ∑ j, φ j u • (P j u - u) := by
  rw [weightedProjection]
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hSum, one_smul]

/-- The construction fixes the prescribed relative set pointwise whenever
every active coordinate projection does. -/
theorem weightedProjection_fixed (φ : J → H → ℝ) (P : J → H →L[ℝ] H) (u : H)
    (hSum : ∑ j, φ j u = 1) (hFix : ∀ j, φ j u ≠ 0 → P j u = u) :
    weightedProjection φ P u = u := by
  have he (j) : φ j u • P j u = φ j u • u := by
    by_cases hj : φ j u = 0
    · simp [hj]
    · rw [hFix j hj]
  simp_rw [weightedProjection, he]
  rw [← Finset.sum_smul, hSum, one_smul]

/-- The weighted construction inherits the local finite-coordinate error
without a factor depending on the number of charts. -/
theorem weightedProjection_error (φ : J → H → ℝ) (P : J → H →L[ℝ] H)
    (u : H) (ε : ℝ) (hSum : ∑ j, φ j u = 1) (hφ : ∀ j, 0 ≤ φ j u)
    (hError : ∀ j, ‖P j u - u‖ ≤ ε) : ‖weightedProjection φ P u - u‖ ≤ ε := by
  rw [weightedProjection_sub φ P u hSum]
  calc
    _ ≤ ∑ j, ‖φ j u • (P j u - u)‖ := norm_sum_le _ _
    _ = ∑ j, φ j u * ‖P j u - u‖ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hφ j)]
    _ ≤ ∑ j, φ j u * ε := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hError j) (hφ j))
    _ = ε := by rw [← Finset.sum_mul, hSum, one_mul]

/-- The unnormalized construction stays uniformly away from the origin. -/
theorem weightedProjection_norm_lower (φ : J → H → ℝ) (P : J → H →L[ℝ] H)
    (u : H) (ε : ℝ) (hu : ‖u‖ = 1) (hError : ‖weightedProjection φ P u - u‖ ≤ ε) :
    1 - ε ≤ ‖weightedProjection φ P u‖ := by
  have h := norm_sub_norm_le u (weightedProjection φ P u)
  rw [norm_sub_rev, hu] at h
  linarith

/-- Quantitative derivative estimate with constant one in its projection
part, as required for the near-isometry in Lemma 5.1. -/
theorem weightedProjectionDerivative_norm (φ : J → H → ℝ)
    (dφ : J → H → H →L[ℝ] ℝ) (P : J → H →L[ℝ] H)
    (u h : H) (ε C : ℝ) (hSum : ∑ j, φ j u = 1) (hφ : ∀ j, 0 ≤ φ j u)
    (hP : ∀ j v, ‖P j v‖ ≤ ‖v‖) (hError : ∀ j, ‖P j u - u‖ ≤ ε)
    (hε : 0 ≤ ε) (hC : ∑ j, ‖dφ j u‖ ≤ C) :
    ‖weightedProjectionDerivative φ dφ P u h‖ ≤ (1 + C * ε) * ‖h‖ := by
  have hFirst : ‖∑ j, φ j u • P j h‖ ≤ ‖h‖ := by
    calc
      _ ≤ ∑ j, ‖φ j u • P j h‖ := norm_sum_le _ _
      _ = ∑ j, φ j u * ‖P j h‖ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hφ j)]
      _ ≤ ∑ j, φ j u * ‖h‖ := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hP j h) (hφ j))
      _ = ‖h‖ := by rw [← Finset.sum_mul, hSum, one_mul]
  have hSecond : ‖∑ j, dφ j u h • (P j u - u)‖ ≤ C * ε * ‖h‖ := by
    calc
      _ ≤ ∑ j, ‖dφ j u h • (P j u - u)‖ := norm_sum_le _ _
      _ ≤ ∑ j, (‖dφ j u‖ * ‖h‖) * ε := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_smul]
        exact mul_le_mul ((dφ j u).le_opNorm h) (hError j)
          (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = (∑ j, ‖dφ j u‖) * ε * ‖h‖ := by rw [← Finset.sum_mul, ← Finset.sum_mul]; ring
      _ ≤ C * ε * ‖h‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC hε) (norm_nonneg h)
  change ‖(∑ j, φ j u • P j) h + (∑ j, (dφ j u).smulRight (P j u - u)) h‖ ≤ _
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply]
  calc
    _ ≤ ‖∑ j, φ j u • P j h‖ + ‖∑ j, dφ j u h • (P j u - u)‖ := norm_add_le _ _
    _ ≤ ‖h‖ + C * ε * ‖h‖ := add_le_add hFirst hSecond
    _ = _ := by ring

end Paper28
