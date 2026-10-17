import Paper26.VolumeRates
import Paper26.SampleLowerBounds
import Mathlib.Data.Nat.Choose.Bounds

/-! The binomial-dimension and power arithmetic in Equation (35), including
`m=1`, the qubit case omitted by the Sobolev argument. -/
noncomputable section

namespace Paper26.PureLowerArithmetic

theorem symmetricDimension_upper (n m : ℕ) (hm : 0 < m) :
    ((n + m).choose n : ℝ) ≤ (Real.exp 1 * ((n : ℝ) + m) / (m : ℝ)) ^ m := by
  have hmr : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hlow : (0 : ℝ) < ((m : ℝ) / Real.exp 1) ^ m := by positivity
  calc
    ((n + m).choose n : ℝ) = ((n + m).choose m : ℝ) := by
      rw [Nat.choose_symm_add]
    _ ≤ ((n + m : ℕ) : ℝ) ^ m / (m.factorial : ℝ) := Nat.choose_le_pow_div m (n + m)
    _ ≤ ((n + m : ℕ) : ℝ) ^ m / (((m : ℝ) / Real.exp 1) ^ m) :=
      div_le_div_of_nonneg_left (by positivity) hlow (VolumeRates.pow_div_exp_le_factorial m hm)
    _ = (Real.exp 1 * ((n : ℝ) + m) / (m : ℝ)) ^ m := by
      rw [← div_pow]
      congr 1
      push_cast
      field_simp

theorem base_lower_of_power {x : ℝ} {m : ℕ} (hm : 0 < m) (hx : 0 ≤ x)
    (hp : 2 / 3 ≤ x ^ m) : 2 / 3 ≤ x := by
  by_contra h
  have hx1 : x ≤ 1 := by linarith
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have hpow : x ^ m ≤ x := by
    rw [hk, pow_succ]
    exact mul_le_of_le_one_left hx (pow_le_one₀ hx hx1)
  linarith

/-- A symmetric-dimension times loss-volume bound controls a linear base. -/
theorem linear_base_lower (n m : ℕ) (hm : 0 < m) {v : ℝ} (hv : 0 ≤ v)
    (hsuccess : 2 / 3 ≤ ((n + m).choose n : ℝ) * v ^ m) :
    2 / 3 ≤ (Real.exp 1 * ((n : ℝ) + m) / (m : ℝ)) * v := by
  apply base_lower_of_power hm (by positivity)
  calc
    2 / 3 ≤ ((n + m).choose n : ℝ) * v ^ m := hsuccess
    _ ≤ (Real.exp 1 * ((n : ℝ) + m) / (m : ℝ)) ^ m * v ^ m :=
      mul_le_mul_of_nonneg_right (symmetricDimension_upper n m hm) (by positivity)
    _ = _ := (mul_pow _ _ _).symm

theorem qubit_bures_linear (n : ℕ) {ε : ℝ} (hε : 0 < ε)
    (hsuccess : 2 / 3 ≤ ((n + 1).choose n : ℝ) * (6 * Real.exp 1 * ε)) :
    2 / 3 ≤ 6 * Real.exp 1 ^ 2 * ε * (1 + (n : ℝ)) := by
  have h := linear_base_lower n 1 (by omega) (by positivity : 0 ≤ 6 * Real.exp 1 * ε)
    (by simpa using hsuccess)
  convert h using 1 <;> push_cast <;> ring

theorem qubit_right_linear (n : ℕ) {ε : ℝ}
    (hsuccess : 2 / 3 ≤ ((n + 1).choose n : ℝ) * (18 * Real.exp 1 * ε ^ 2)) :
    2 / 3 ≤ 18 * Real.exp 1 ^ 2 * ε ^ 2 * (1 + (n : ℝ)) := by
  have h := linear_base_lower n 1 (by omega) (by positivity : 0 ≤ 18 * Real.exp 1 * ε ^ 2)
    (by simpa using hsuccess)
  convert h using 1 <;> push_cast <;> ring

end Paper26.PureLowerArithmetic
