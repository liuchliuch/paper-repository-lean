import Paper10.Metric
import Paper10.Feasibility

noncomputable section
open Matrix
namespace Paper10
variable {q : ℕ}

/-- Local norms are invariant under invertible congruence, in the actual log-det metric. -/
theorem localNormSq_congruence (R Y U : Matrix (Fin q) (Fin q) ℝ)
    (hR : IsUnit R) (s : ℝ) :
    localNormSq s (R * Y * Rᴴ) (R * U * Rᴴ) = localNormSq s Y U := by
  have hr := (Matrix.isUnit_iff_isUnit_det R).mp hR
  have hrs := (Matrix.isUnit_iff_isUnit_det Rᴴ).mp hR.star
  have h1 := Matrix.nonsing_inv_mul R hr
  have h2 := Matrix.mul_nonsing_inv R hr
  have h3 := Matrix.nonsing_inv_mul Rᴴ hrs
  have h4 := Matrix.mul_nonsing_inv Rᴴ hrs
  have hc : ∀ M : Matrix (Fin q) (Fin q) ℝ, R⁻¹ * (R * M) = M := by
    intro M
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hcs : ∀ M : Matrix (Fin q) (Fin q) ℝ, Rᴴ * ((Rᴴ)⁻¹ * M) = M := by
    intro M
    rw [← Matrix.mul_assoc, h4, Matrix.one_mul]
  have he : (R * Y * Rᴴ)⁻¹ * (R * U * Rᴴ) * (R * Y * Rᴴ)⁻¹ * (R * U * Rᴴ) =
      (Rᴴ)⁻¹ * (Y⁻¹ * U * Y⁻¹ * U) * Rᴴ := by
    simp only [Matrix.mul_inv_rev, Matrix.mul_assoc, hc, hcs]
  unfold localNormSq g G
  rw [he, Matrix.trace_mul_cycle, h4, Matrix.one_mul]

/-- Actual norm change at the identity is exactly the matrix remainder in Lemma 3.1. -/
theorem localNormSq_normalized_change (A : Matrix (Fin q) (Fin q) ℝ) (t s : ℝ) :
    localNormSq s (1 + t • A) (t • A) - localNormSq s 1 (t • A) = s * t ^ 2 * Ft t A := by
  let M : Matrix (Fin q) (Fin q) ℝ := 1 + t • A
  have hcomm : Commute A M := by
    show A * (1 + t • A) = (1 + t • A) * A
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_smul, Matrix.smul_mul]
  have hinv : A * M⁻¹ = M⁻¹ * A := by
    simpa only [Matrix.zpow_neg_one] using (Matrix.Commute.zpow_right hcomm (-1)).eq
  have he : M⁻¹ * A * M⁻¹ * A = A * A * M ^ (-2 : ℤ) := by
    rw [show (-2 : ℤ) = -(2 : ℕ) by norm_num, Matrix.zpow_neg_natCast, ← Matrix.inv_pow', pow_two]
    calc
      _ = (M⁻¹ * A) * (M⁻¹ * A) := by simp only [Matrix.mul_assoc]
      _ = (A * M⁻¹) * (A * M⁻¹) := congrArg₂ (· * ·) hinv.symm hinv.symm
      _ = _ := by rw [Matrix.mul_assoc, ← Matrix.mul_assoc M⁻¹ A M⁻¹, ← hinv]; simp only [Matrix.mul_assoc]
  unfold localNormSq g G
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    inv_one, Matrix.one_mul, Matrix.mul_one]
  change s * (t * (t * Matrix.trace (M⁻¹ * A * M⁻¹ * A))) - s * (t * (t * Matrix.trace (A * A))) = _
  rw [he]
  unfold Ft
  rw [Matrix.trace_sub]
  ring

/-- The norm-change identity (21) at an arbitrary invertible square-root factor of the base point. -/
theorem metric_change_congruence (R A : Matrix (Fin q) (Fin q) ℝ)
    (hR : IsUnit R) (s t : ℝ) :
    let X := R * Rᴴ
    let H := R * (t • A) * Rᴴ
    localNormSq s (X + H) H - localNormSq s X H = s * t ^ 2 * Ft t A := by
  have hx : R * Rᴴ = R * (1 : Matrix _ _ ℝ) * Rᴴ := by rw [Matrix.mul_one]
  have hz : R * Rᴴ + R * (t • A) * Rᴴ = R * (1 + t • A) * Rᴴ := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one]
  change localNormSq s (R * Rᴴ + R * (t • A) * Rᴴ) (R * (t • A) * Rᴴ) -
    localNormSq s (R * Rᴴ) (R * (t • A) * Rᴴ) = _
  rw [hz, localNormSq_congruence R _ _ hR, hx, localNormSq_congruence R _ _ hR]
  exact localNormSq_normalized_change A t s

end Paper10
