import Paper10.ExactCubic

noncomputable section
open Matrix MeasureTheory
namespace Paper10
variable {q m : ℕ}

/-- The quartic expectation as a polynomial in the covariance eigenvalues σ². -/
theorem fourth_moment_weighted (F : Fin m → Matrix (Fin q) (Fin q) ℝ) (σ : Fin m → ℝ) :
    (∫ ω, Matrix.trace (gaussianMatrix (fun a => σ a • F a) ω ^ 4) ∂stdGaussianMeasure m) =
      ∑ a, ∑ b, (σ a ^ 2 * σ b ^ 2) *
        (2 * Matrix.trace (F a * F a * F b * F b) + Matrix.trace (F a * F b * F a * F b)) := by
  let B := fun a => σ a • F a
  have hs : Matrix.trace ((∑ a, B a * B a) * (∑ a, B a * B a)) =
      ∑ a, ∑ b, Matrix.trace (B a * B a * B b * B b) := by
    simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_assoc]
    rw [Finset.sum_comm]
  rw [fourth_moment_expansion, hs]
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  dsimp [B]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_smul, smul_eq_mul]
  ring

/-- Covariance monotonicity of the quartic trace under Q≤I, proved directly from Wick coefficients. -/
theorem iso_quartic_max (F : Fin m → Matrix (Fin q) (Fin q) ℝ)
    (hF : OrthonormalFrob F) (σ : Fin m → ℝ) (hσ : ∀ a, 0 ≤ σ a ∧ σ a ≤ 1) :
    (∫ ω, Matrix.trace (gaussianMatrix (fun a => σ a • F a) ω ^ 4) ∂stdGaussianMeasure m) ≤
      (q : ℝ) * (2 * (q : ℝ) ^ 2 + 5 * (q : ℝ) + 5) / 4 := by
  rw [← iso_quartic F hF, fourth_moment_weighted]
  have hi := fourth_moment_weighted F (fun _ => 1)
  simp only [one_smul, one_pow, one_mul] at hi
  rw [hi]
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  have ha : σ a ^ 2 ≤ 1 := by nlinarith [(hσ a).1, (hσ a).2]
  have hb : σ b ^ 2 ≤ 1 := by nlinarith [(hσ b).1, (hσ b).2]
  have hw : σ a ^ 2 * σ b ^ 2 ≤ 1 := by
    exact (mul_le_mul_of_nonneg_right ha (sq_nonneg _)).trans (by simpa using hb)
  have hp := trace_A2H2_nonneg (hF.1 a) (hF.1 b)
  have hc := frob_cs_UVUV (hF.1 a) (hF.1 b)
  have hn := neg_abs_le (Matrix.trace (F a * F b * F a * F b))
  have hk : 0 ≤ 2 * Matrix.trace (F a * F a * F b * F b) + Matrix.trace (F a * F b * F a * F b) := by
    linarith
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hw hk

end Paper10
