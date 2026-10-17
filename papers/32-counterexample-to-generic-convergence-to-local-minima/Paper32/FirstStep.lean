import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Numerical first-step capture from the actual basin and local oracle-coordinate bounds.
The connection of those bounds to the standard Clarke multifunction is a separate theorem. -/
namespace Paper32

lemma effective_noise_bound {v ν : ℝ} (hv : |v| < 1 / 100) (hν : |ν| ≤ 1 / 100) :
    |ν - v| < 1 / 50 := by
  calc
    |ν - v| ≤ |ν| + |v| := abs_sub _ _
    _ < 1 / 50 := by linarith

lemma first_coordinate_capture {x v w ν α M b C : ℝ}
    (hα : 0 < α) (hx : |x| < b * α)
    (hw : |w + v| ≤ M) (he : |ν - v| < 1 / 50)
    (hC : b + M + 1 / 50 < C) :
    |x - α * (w + ν)| < C * α := by
  have hadd : w + ν = (w + v) + (ν - v) := by ring
  have hsum : |w + ν| < M + 1 / 50 := by
    rw [hadd]
    exact lt_of_le_of_lt (abs_add_le _ _) (by linarith)
  calc
    |x - α * (w + ν)| ≤ |x| + |α * (w + ν)| := abs_sub _ _
    _ = |x| + α * |w + ν| := by rw [abs_mul, abs_of_pos hα]
    _ < b * α + α * (M + 1 / 50) := add_lt_add hx (mul_lt_mul_of_pos_left hsum hα)
    _ < C * α := by nlinarith

/-- The exact arithmetic of Lemma 4.1. `w+v` is the untilted Clarke value. -/
theorem first_step_capture {x y vx vy wx wy νx νy α : ℝ}
    (hα : 1 / 8 < α)
    (hx : |x| < 1 / 80) (hy : |y| < 1 / 20)
    (hvx : |vx| < 1 / 100) (hvy : |vy| < 1 / 100)
    (hwx : |wx + vx| ≤ 7) (hwy : |wy + vy| ≤ 2)
    (hνx : |νx| ≤ 1 / 100) (hνy : |νy| ≤ 1 / 100) :
    |x - α * (wx + νx)| < (36 / 5) * α ∧
    |y - α * (wy + νy)| < (5 / 2) * α := by
  have ha : 0 < α := by linarith
  constructor
  · exact first_coordinate_capture ha (by nlinarith : |x| < (1 / 10) * α)
      hwx (effective_noise_bound hvx hνx) (by norm_num)
  · exact first_coordinate_capture ha (by nlinarith : |y| < (2 / 5) * α)
      hwy (effective_noise_bound hvy hνy) (by norm_num)

/-- Exact differentiability-point initialization from Corollary 2.3. -/
theorem specified_initialization :
    |(1 / 160 : ℝ)| < 1 / 80 ∧ |(1 / 100 : ℝ)| < 1 / 20 ∧
    (1 / 160 : ℝ) ≠ 0 ∧ (1 / 100 : ℝ) ≠ 0 ∧
    |(1 / 100 : ℝ)| < 2 * |(1 / 160 : ℝ)| := by norm_num

end Paper32
