import Paper26.QuantumModel
import Paper26.Normalization
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Actual tensor-copy input states, indexed by functions `Fin n → ι`. -/
noncomputable section
open scoped BigOperators Matrix ComplexOrder

namespace Paper26.TensorCopies

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def matrix (A : Matrix ι ι ℂ) (n : ℕ) : Matrix (Fin n → ι) (Fin n → ι) ℂ :=
  fun x y => ∏ i, A (x i) (y i)

theorem matrix_mul (A B : Matrix ι ι ℂ) (n : ℕ) :
    matrix (A * B) n = matrix A n * matrix B n := by
  ext x y
  simpa only [matrix, Matrix.mul_apply, Finset.prod_mul_distrib] using
    (Fintype.prod_sum (fun i : Fin n => fun j : ι => A (x i) j * B j (y i)))

theorem matrix_conjTranspose (A : Matrix ι ι ℂ) (n : ℕ) :
    matrix Aᴴ n = (matrix A n)ᴴ := by
  ext x y
  simp [matrix, Matrix.conjTranspose_apply]

theorem matrix_trace (A : Matrix ι ι ℂ) (n : ℕ) :
    Matrix.trace (matrix A n) = ∏ _i : Fin n, Matrix.trace A := by
  simpa only [matrix, Matrix.trace, Matrix.diag_apply] using
    (Fintype.prod_sum (fun _i : Fin n => fun j : ι => A j j)).symm

/-- A concrete finite-dimensional Gram factor, obtained from the actual
spectral theorem and nonnegative square roots. -/
theorem psd_exists_gram (A : Matrix ι ι ℂ) (hA : A.PosSemidef) :
    ∃ R : Matrix ι ι ℂ, Rᴴ * R = A := by
  let U : Matrix ι ι ℂ := hA.1.eigenvectorUnitary
  let a : ι → ℝ := hA.1.eigenvalues
  let D : Matrix ι ι ℂ := Normalization.diagonalMatrix (fun i => Real.sqrt (a i))
  have hD : Dᴴ = D := Normalization.diagonalMatrix_conjTranspose _
  have hDD : D * D = Normalization.diagonalMatrix a := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [D, Normalization.diagonalMatrix, Matrix.diagonal_mul_diagonal,
        Matrix.diagonal_apply_eq, ← Complex.ofReal_mul]
      congr 1
      simpa only [pow_two] using Real.sq_sqrt (hA.eigenvalues_nonneg i)
    · simp [D, Normalization.diagonalMatrix, Matrix.diagonal_mul_diagonal, hij]
  refine ⟨D * Uᴴ, ?_⟩
  have hspec : A = U * Normalization.diagonalMatrix a * Uᴴ := by
    simpa only [U, a, Normalization.diagonalMatrix, Function.comp_def,
      Matrix.star_eq_conjTranspose] using hA.1.spectral_theorem
  calc
    (D * Uᴴ)ᴴ * (D * Uᴴ) = U * (D * D) * Uᴴ := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        hD, Matrix.mul_assoc]
    _ = A := by rw [hDD, ← hspec]

theorem matrix_posSemidef (A : Matrix ι ι ℂ) (hA : A.PosSemidef) (n : ℕ) :
    (matrix A n).PosSemidef := by
  obtain ⟨R, hR⟩ := psd_exists_gram A hA
  rw [← hR, matrix_mul, matrix_conjTranspose]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- `n` independent copies of an arbitrary density matrix, including `n=0`. -/
def density (ρ : QuantumModel.Density ι) (n : ℕ) :
    QuantumModel.Density (Fin n → ι) where
  matrix := matrix ρ.matrix n
  positive := matrix_posSemidef _ ρ.positive n
  trace_one := by rw [matrix_trace, ρ.trace_one]; simp

@[simp] theorem density_matrix (ρ : QuantumModel.Density ι) (n : ℕ)
    (x y : Fin n → ι) :
    (density ρ n).matrix x y = ∏ i, ρ.matrix (x i) (y i) := rfl

theorem copy_dimension (n : ℕ) : Fintype.card (Fin n → ι) = Fintype.card ι ^ n := by
  simp

end Paper26.TensorCopies
