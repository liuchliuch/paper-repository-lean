import Paper29.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

noncomputable section
namespace Paper29

/-- Equation (2.7), with the fixed-tail-slope convention. -/
theorem huberWidth_piecewise {s : ℝ} (hs : 0 < s) (t : ℝ) :
    huberWidth s t = if |t| ≤ s then t ^ 2 / (2 * s) else |t| - s / 2 := by
  simp only [huberWidth, huber, abs_div, abs_of_pos hs]
  simp only [div_le_one hs]
  split_ifs <;> field_simp <;> ring

def widthObjective {n d : ℕ} (s : ℝ) (A : Matrix (Fin n) (Fin d) ℝ)
    (b : Fin n → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ i, huberWidth s ((A.mulVec x) i - b i)

/-- Width reduction in Section 2, preserving the same parameter x. -/
theorem widthObjective_scaling {n d : ℕ} (s : ℝ)
    (A : Matrix (Fin n) (Fin d) ℝ) (b : Fin n → ℝ) (x : Fin d → ℝ) :
    widthObjective s A b x = s * objective (s⁻¹ • A) (fun i => b i / s) x := by
  unfold widthObjective huberWidth objective
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  simp only [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
  ring

end Paper29
