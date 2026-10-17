import ELV.Basic
import ELV.CostIdentities
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Sqrt

/-!
# Line-purifier matrix algebra (Lemma 3.1)

Two-dimensional blocks of the line walk of §3.1: the plane reflection (3.3),
the product block `B_γ` (3.8), and the cost/catalyst arithmetic (3.5), (3.9)–(3.10).
-/

noncomputable section

open Matrix

namespace ELV

namespace LinePurifier

/-- Reflection of (3.3) in the ordered basis `(s,t)`. -/
def Rplane (p : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  of fun i j =>
    match i, j with
    | 0, 0 => 1 - 2 * p
    | 0, 1 => 2 * Real.sqrt (p * (1 - p))
    | 1, 0 => 2 * Real.sqrt (p * (1 - p))
    | 1, 1 => 2 * p - 1

/-- Product-reflection block `B_γ` of (3.8). -/
def Bgamma (γ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  of fun i j =>
    match i, j with
    | 0, 0 => (1 - γ ^ 2) / (1 + γ ^ 2)
    | 0, 1 => (2 * γ) / (1 + γ ^ 2)
    | 1, 0 => (2 * γ) / (1 + γ ^ 2)
    | 1, 1 => (γ ^ 2 - 1) / (1 + γ ^ 2)

theorem Rplane_diag0 (p : ℝ) : Rplane p 0 0 = 1 - 2 * p := rfl

theorem Rplane_diag1 (p : ℝ) : Rplane p 1 1 = 2 * p - 1 := rfl

theorem Rplane_trace (p : ℝ) : (Rplane p).trace = 0 := by
  have h00 : Rplane p 0 0 = 1 - 2 * p := rfl
  have h11 : Rplane p 1 1 = 2 * p - 1 := rfl
  have : (Rplane p).trace = Rplane p 0 0 + Rplane p 1 1 := by
    unfold Matrix.trace
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    rfl
  rw [this, h00, h11]
  ring

/-- Cost arithmetic of (3.9)–(3.10) for `p < 1/2`. -/
theorem cost_low (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1 / 2) :
    1 + 2 * (p / (1 - p) / (1 - p / (1 - p))) = 1 / (1 - 2 * p) := by
  rw [gamma_sq_div p hp0 hp1]
  exact line_total_cost_low p hp1

/-- Cost arithmetic of (3.9)–(3.10) for `p > 1/2`. -/
theorem cost_high (p : ℝ) (hp1 : 1 / 2 < p) (hp2 : p < 1) :
    1 + 2 * ((p / (1 - p))⁻¹ / (1 - (p / (1 - p))⁻¹)) = 1 / (2 * p - 1) := by
  rw [gamma_inv_sq_div p hp1 hp2]
  exact line_total_cost_high p hp1

/-- Catalyst squared norm (3.9) for `p < 1/2`. -/
theorem catalyst_norm_low (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1 / 2) :
    p / (1 - p) / (1 - p / (1 - p)) = p / (1 - 2 * p) :=
  gamma_sq_div p hp0 hp1

/-- Catalyst squared norm (3.9) for `p > 1/2`. -/
theorem catalyst_norm_high (p : ℝ) (hp1 : 1 / 2 < p) (hp2 : p < 1) :
    (p / (1 - p))⁻¹ / (1 - (p / (1 - p))⁻¹) = (1 - p) / (2 * p - 1) :=
  gamma_inv_sq_div p hp1 hp2

/-- `B_γ` eigenvalue arithmetic used in (3.8):
    `B_γ (1,γ) = (1,γ)` at the level of the matrix formula. -/
theorem Bgamma_fix_formula (γ : ℝ) (h : 1 + γ ^ 2 ≠ 0) :
    (1 - γ ^ 2) / (1 + γ ^ 2) * 1 + (2 * γ) / (1 + γ ^ 2) * γ = 1 ∧
    (2 * γ) / (1 + γ ^ 2) * 1 + (γ ^ 2 - 1) / (1 + γ ^ 2) * γ = γ := by
  constructor <;> field_simp [h] <;> ring

/-- `B_γ` negation of `(1, -γ⁻¹)`. -/
theorem Bgamma_neg_formula (γ : ℝ) (hγ : γ ≠ 0) (h : 1 + γ ^ 2 ≠ 0) :
    (1 - γ ^ 2) / (1 + γ ^ 2) * 1 + (2 * γ) / (1 + γ ^ 2) * (-γ⁻¹) = -1 ∧
    (2 * γ) / (1 + γ ^ 2) * 1 + (γ ^ 2 - 1) / (1 + γ ^ 2) * (-γ⁻¹) = γ⁻¹ := by
  constructor <;> field_simp [h, hγ] <;> ring

end LinePurifier

end ELV
