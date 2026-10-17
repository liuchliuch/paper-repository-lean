import Paper10.Remainder
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.Spectrum

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
namespace Paper10

/-- Lemma 3.1 with the paper's operator-norm hypothesis, and the actual matrix remainder. -/
theorem lemma_3_1_opNorm {q : ℕ} (A : Matrix (Fin q) (Fin q) ℝ) (hA : A.IsSymm)
    {t : ℝ} (ht : 0 < t) (hsmall : t * ‖A‖ ≤ 1 / 2) :
    |Ft t A| ≤ 2 * t * |Matrix.trace (A ^ 3)| + 8 * t ^ 2 * Matrix.trace (A ^ 4) := by
  apply lemma_3_1_matrix t A hA ht
  intro i
  letI : Nonempty (Fin q) := ⟨i⟩
  have hh := spectrum.norm_le_norm_of_mem ((real_isHermitian hA).eigenvalues_mem_spectrum_real i)
  rw [Real.norm_eq_abs] at hh
  rw [abs_mul, abs_of_pos ht]
  exact (mul_le_mul_of_nonneg_left hh ht.le).trans hsmall

end Paper10
