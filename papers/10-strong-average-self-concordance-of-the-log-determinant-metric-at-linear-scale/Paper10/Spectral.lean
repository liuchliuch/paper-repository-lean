import Paper10.Basic
import Mathlib.LinearAlgebra.Matrix.Spectrum

noncomputable section
open Matrix
namespace Paper10
variable {q : ℕ}

/-- Multiplication in orthogonal eigenvector coordinates preserves products. -/
theorem orthogonal_conj_mul (U : Matrix.unitaryGroup (Fin q) ℝ)
    (D E : Matrix (Fin q) (Fin q) ℝ) :
    ((U : Matrix _ _ ℝ) * D * (U : Matrix _ _ ℝ)ᴴ) *
      ((U : Matrix _ _ ℝ) * E * (U : Matrix _ _ ℝ)ᴴ) =
      (U : Matrix _ _ ℝ) * (D * E) * (U : Matrix _ _ ℝ)ᴴ := by
  have hU : (U : Matrix (Fin q) (Fin q) ℝ)ᴴ * (U : Matrix (Fin q) (Fin q) ℝ) = 1 := U.2.1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (U : Matrix (Fin q) (Fin q) ℝ)ᴴ
    (U : Matrix (Fin q) (Fin q) ℝ) (E * (U : Matrix (Fin q) (Fin q) ℝ)ᴴ), hU, Matrix.one_mul]

/-- Trace is invariant under orthogonal conjugation. -/
theorem trace_orthogonal_conj (U : Matrix.unitaryGroup (Fin q) ℝ)
    (D : Matrix (Fin q) (Fin q) ℝ) :
    Matrix.trace ((U : Matrix _ _ ℝ) * D * (U : Matrix _ _ ℝ)ᴴ) = Matrix.trace D := by
  rw [Matrix.trace_mul_cycle]
  have hU : (U : Matrix (Fin q) (Fin q) ℝ)ᴴ * (U : Matrix (Fin q) (Fin q) ℝ) = 1 := U.2.1
  rw [hU, Matrix.one_mul]

theorem real_isHermitian {A : Matrix (Fin q) (Fin q) ℝ} (hA : A.IsSymm) : A.IsHermitian := by
  simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hA

/-- Powers of a real symmetric matrix have the expected spectral traces. -/
theorem trace_pow_spectral (A : Matrix (Fin q) (Fin q) ℝ) (hA : A.IsSymm) (k : ℕ) :
    Matrix.trace (A ^ k) = ∑ i, ((real_isHermitian hA).eigenvalues i) ^ k := by
  let h : A.IsHermitian := real_isHermitian hA
  let U := h.eigenvectorUnitary
  let D : Matrix (Fin q) (Fin q) ℝ := Matrix.diagonal h.eigenvalues
  have hAD : A = (U : Matrix _ _ ℝ) * D * (U : Matrix _ _ ℝ)ᴴ := by
    simpa [U, D, RCLike.ofReal_real_eq_id] using h.spectral_theorem
  have hp : ∀ k : ℕ, A ^ k = (U : Matrix _ _ ℝ) *
      Matrix.diagonal (fun i => h.eigenvalues i ^ k) * (U : Matrix _ _ ℝ)ᴴ := by
    intro k
    induction k with
    | zero =>
      simp only [pow_zero, Matrix.diagonal_one, Matrix.mul_one]
      exact U.2.2.symm
    | succ k ih =>
      rw [pow_succ, ih]
      calc
        _ = ((U : Matrix _ _ ℝ) * Matrix.diagonal (fun i => h.eigenvalues i ^ k) *
            (U : Matrix _ _ ℝ)ᴴ) * ((U : Matrix _ _ ℝ) * D * (U : Matrix _ _ ℝ)ᴴ) :=
          congrArg (fun B => ((U : Matrix _ _ ℝ) *
            Matrix.diagonal (fun i => h.eigenvalues i ^ k) * (U : Matrix _ _ ℝ)ᴴ) * B) hAD
        _ = _ := by rw [orthogonal_conj_mul, Matrix.diagonal_mul_diagonal]; rfl
  rw [hp, trace_orthogonal_conj, Matrix.trace_diagonal]

/-- The third absolute power sum is bounded by the 3/2 power of the square sum. -/
theorem abs_sum_cube_le (k : Fin q → ℝ) :
    |∑ i, k i ^ 3| ≤ (∑ i, k i ^ 2) ^ (3 / 2 : ℝ) := by
  let R := ∑ i, k i ^ 2
  have hR : 0 ≤ R := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hi : ∀ i, |k i| ≤ Real.sqrt R := by
    intro i
    have hh : k i ^ 2 ≤ R := Finset.single_le_sum
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    nlinarith [Real.sq_sqrt hR, Real.sqrt_nonneg R, sq_abs (k i), abs_nonneg (k i)]
  calc
    |∑ i, k i ^ 3| ≤ ∑ i, |k i ^ 3| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, Real.sqrt R * k i ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_pow]
      have hh := mul_le_mul_of_nonneg_right (hi i) (sq_nonneg (k i))
      convert hh using 1 <;> rw [pow_succ, sq_abs] <;> ring
    _ = Real.sqrt R * R := by rw [← Finset.mul_sum]
    _ = R ^ (3 / 2 : ℝ) := by
      rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
        Real.rpow_add' hR (by norm_num), Real.rpow_one, Real.sqrt_eq_rpow]

/-- Spectral diagonalization over the reals, with the scalar embedding simplified. -/
theorem real_spectral_theorem (A : Matrix (Fin q) (Fin q) ℝ) (hA : A.IsSymm) :
    A = ((real_isHermitian hA).eigenvectorUnitary : Matrix _ _ ℝ) *
      Matrix.diagonal (real_isHermitian hA).eigenvalues *
      ((real_isHermitian hA).eigenvectorUnitary : Matrix _ _ ℝ)ᴴ := by
  simpa [RCLike.ofReal_real_eq_id] using (real_isHermitian hA).spectral_theorem

/-- Inversion of an orthogonally conjugated invertible real diagonal matrix. -/
theorem orthogonal_conj_diagonal_inv (U : Matrix.unitaryGroup (Fin q) ℝ)
    (d : Fin q → ℝ) (hd : ∀ i, d i ≠ 0) :
    ((U : Matrix _ _ ℝ) * Matrix.diagonal d * (U : Matrix _ _ ℝ)ᴴ)⁻¹ =
      (U : Matrix _ _ ℝ) * Matrix.diagonal (fun i => (d i)⁻¹) * (U : Matrix _ _ ℝ)ᴴ := by
  apply Matrix.inv_eq_left_inv
  rw [orthogonal_conj_mul, Matrix.diagonal_mul_diagonal]
  have he : Matrix.diagonal (fun i => (d i)⁻¹ * d i) = (1 : Matrix (Fin q) (Fin q) ℝ) := by
    simp [hd]
  rw [he, Matrix.mul_one]
  exact U.2.2

/-- Congruence takes a shifted and scaled diagonal matrix to the corresponding matrix. -/
theorem orthogonal_conj_one_add_smul (U : Matrix.unitaryGroup (Fin q) ℝ)
    (d : Fin q → ℝ) (t : ℝ) :
    (U : Matrix _ _ ℝ) * Matrix.diagonal (fun i => 1 + t * d i) * (U : Matrix _ _ ℝ)ᴴ =
      1 + t • ((U : Matrix _ _ ℝ) * Matrix.diagonal d * (U : Matrix _ _ ℝ)ᴴ) := by
  have hd : Matrix.diagonal (fun i => 1 + t * d i) =
      (1 : Matrix (Fin q) (Fin q) ℝ) + t • Matrix.diagonal d := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hij]
  have hU : (U : Matrix (Fin q) (Fin q) ℝ) * (U : Matrix (Fin q) (Fin q) ℝ)ᴴ = 1 := U.2.2
  rw [hd, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hU,
    Matrix.mul_smul, Matrix.smul_mul]

end Paper10
