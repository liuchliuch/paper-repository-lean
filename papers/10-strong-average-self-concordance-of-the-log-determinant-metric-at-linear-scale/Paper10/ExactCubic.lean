import Paper10.CubicMoment
import Paper10.Appendix

noncomputable section
open Matrix MeasureTheory
namespace Paper10
variable {q m : ℕ}

/-- Alternating trace contraction in the isotropic orthonormal basis. -/
theorem isotropic_alternating_sum (F : Fin m → Matrix (Fin q) (Fin q) ℝ)
    (hF : OrthonormalFrob F) :
    (∑ a, ∑ b, Matrix.trace (F a * F b * F a * F b)) = ((n q : ℝ) + q) / 2 := by
  have h := fourth_moment_expansion F
  rw [iso_quartic F hF, sum_squares_orthonormal F hF] at h
  have he : Matrix.trace ((c q • oneMat q) * (c q • oneMat q)) = (n q : ℝ) * c q := by
    simp only [oneMat, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
      Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
    rw [n_mul_c]
    ring
  rw [he] at h
  have hf : (q : ℝ) * (2 * (q : ℝ) ^ 2 + 5 * (q : ℝ) + 5) / 4 =
      2 * (n q : ℝ) * c q + ((n q : ℝ) + q) / 2 := by
    rw [n_mul_c]
    simp only [c, Nat.cast_add, Nat.cast_one]
    ring
  linarith

/-- Exact symmetric cubic tensor norm in the isotropic case. -/
theorem isotropic_cubic_tensor (F : Fin m → Matrix (Fin q) (Fin q) ℝ)
    (hF : OrthonormalFrob F) :
    (∑ a, ∑ b, ∑ c, Matrix.trace (F a * F b * F c) ^ 2) =
      ((n q : ℝ) * c q + ((n q : ℝ) + q) / 2) / 2 := by
  have hrow : ∀ b c, (∑ a, Matrix.trace (F a * F b * F c) ^ 2) =
      (Matrix.trace (F b * F b * F c * F c) + Matrix.trace (F b * F c * F b * F c)) / 2 := by
    intro b c
    have hp := frob_parseval F hF (symProduct (F b) (F c))
      (symProduct_isSymm (hF.1 b) (hF.1 c))
    have he : ∀ a, frob (F a) (symProduct (F b) (F c)) = Matrix.trace (F a * F b * F c) :=
      fun a => frob_symProduct (hF.1 a) (hF.1 b) (hF.1 c)
    simp_rw [he] at hp
    exact hp.trans (symProduct_norm_sq (hF.1 b) (hF.1 c))
  have hadj : (∑ b, ∑ c, Matrix.trace (F b * F b * F c * F c)) = (n q : ℝ) * c q := by
    calc
      _ = Matrix.trace ((∑ a, F a * F a) * (∑ a, F a * F a)) := by
        simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_assoc]
        rw [Finset.sum_comm]
      _ = _ := by
        rw [sum_squares_orthonormal F hF]
        simp only [oneMat, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
          Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
        rw [n_mul_c]
        ring
  calc
    _ = ∑ b, ∑ c, ∑ a, Matrix.trace (F a * F b * F c) ^ 2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
    _ = _ := by
      simp_rw [hrow]
      simp only [div_eq_mul_inv, Finset.sum_add_distrib, ← Finset.sum_mul]
      rw [hadj, isotropic_alternating_sum F hF]
      ring

/-- Exact contraction term of the isotropic cubic moment. -/
theorem isotropic_cubic_contraction (F : Fin m → Matrix (Fin q) (Fin q) ℝ)
    (hF : OrthonormalFrob F) :
    (∑ a, (Matrix.trace (F a * ∑ b, F b * F b)) ^ 2) = (n q : ℝ) * c q := by
  rw [sum_squares_orthonormal F hF]
  simp only [oneMat, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul,
    mul_pow, ← Finset.mul_sum]
  rw [parseval_trace_one F hF, n_mul_c]
  ring

/-- Exact isotropic cubic trace moment (16), as an actual sixth-degree Gaussian integral. -/
theorem iso_cubic_sq (F : Fin m → Matrix (Fin q) (Fin q) ℝ)
    (hF : OrthonormalFrob F) :
    (∫ ω, Matrix.trace (gaussianMatrix F ω ^ 3) ^ 2 ∂stdGaussianMeasure m) =
      3 * (q : ℝ) * (4 * (q : ℝ) ^ 2 + 9 * (q : ℝ) + 7) / 4 := by
  rw [cubic_moment_expansion F hF.1, isotropic_cubic_tensor F hF,
    isotropic_cubic_contraction F hF, n_mul_c]
  simp only [c, Nat.cast_add, Nat.cast_one]
  ring

end Paper10
