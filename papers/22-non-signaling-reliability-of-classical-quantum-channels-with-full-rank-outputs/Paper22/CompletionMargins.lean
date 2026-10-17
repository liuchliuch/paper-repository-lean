import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Scalar margins in effect completion

These are the numerical estimates for the actual construction with `K = M + 6`.
The error radius is `3 / (M * (K - 3))`.
-/

namespace Paper22

private theorem completion_parameter_casts {M K : ℕ} (hM : 2 ≤ M) (hK : K = M + 6) :
    (2 : ℝ) ≤ M ∧ (K : ℝ) = (M : ℝ) + 6 := by
  constructor
  · exact_mod_cast hM
  · exact_mod_cast hK

/-- The error radius of the inverse-map construction is nonnegative. -/
theorem completion_margin_nonneg {M K : ℕ} (hM : 2 ≤ M) (hK : K = M + 6) :
    (0 : ℝ) ≤ 3 / ((M : ℝ) * ((K : ℝ) - 3)) := by
  obtain ⟨hm, hk⟩ := completion_parameter_casts hM hK
  have hm0 : (0 : ℝ) < M := by linarith
  have hk3 : (0 : ℝ) < (K : ℝ) - 3 := by linarith
  exact le_of_lt (div_pos (by norm_num) (mul_pos hm0 hk3))

/-- The inverse-map error fits below the gap between the two coding scales. -/
theorem completion_margin_lower {M K : ℕ} (hM : 2 ≤ M) (hK : K = M + 6) :
    (3 : ℝ) / ((M : ℝ) * ((K : ℝ) - 3)) ≤ 1 / (M : ℝ) - 1 / (K : ℝ) := by
  obtain ⟨hm, hk⟩ := completion_parameter_casts hM hK
  have hm0 : (0 : ℝ) < M := by linarith
  have hk0 : (0 : ℝ) < K := by linarith
  have hk3 : (0 : ℝ) < (K : ℝ) - 3 := by linarith
  have hgap : (1 : ℝ) / M - 1 / K = 6 / ((M : ℝ) * K) := by
    field_simp [ne_of_gt hm0, ne_of_gt hk0]
    nlinarith
  rw [hgap]
  apply (div_le_div_iff₀ (mul_pos hm0 hk3) (mul_pos hm0 hk0)).mpr
  rw [hk]
  nlinarith [sq_nonneg (M : ℝ)]

/-- A sharper uniform upper bound on the completed auxiliary effect. -/
theorem completion_margin_upper_sharp {M K : ℕ} (hM : 2 ≤ M) (hK : K = M + 6) :
    (1 : ℝ) / M + 3 / ((M : ℝ) * ((K : ℝ) - 3)) ≤ 4 / 5 := by
  obtain ⟨hm, hk⟩ := completion_parameter_casts hM hK
  have hm0 : (0 : ℝ) < M := by linarith
  have hk3 : (0 : ℝ) < (K : ℝ) - 3 := by linarith
  have hden : (10 : ℝ) ≤ (M : ℝ) * ((K : ℝ) - 3) := by
    calc
      (10 : ℝ) = 2 * 5 := by norm_num
      _ ≤ (M : ℝ) * ((K : ℝ) - 3) :=
        mul_le_mul hm (by linarith) (by norm_num) (le_of_lt hm0)
  have hfirst : (1 : ℝ) / M ≤ 1 / 2 := by
    apply (div_le_iff₀ hm0).mpr
    nlinarith
  have hsecond : (3 : ℝ) / ((M : ℝ) * ((K : ℝ) - 3)) ≤ 3 / 10 := by
    apply (div_le_iff₀ (mul_pos hm0 hk3)).mpr
    nlinarith
  linarith

/-- The scalar center plus the inverse-map error is bounded by the identity scale. -/
theorem completion_margin_upper {M K : ℕ} (hM : 2 ≤ M) (hK : K = M + 6) :
    (1 : ℝ) / M + 3 / ((M : ℝ) * ((K : ℝ) - 3)) ≤ 1 := by
  exact (completion_margin_upper_sharp hM hK).trans (by norm_num)

/-- The geometric-series error `c * (1/M) / (1-c)` is the chosen radius, for `c = 3/K`. -/
theorem completion_error_identity {M K : ℕ} (hM : 2 ≤ M) (hK : K = M + 6) :
    ((3 : ℝ) / K) * (1 / (M : ℝ)) / (1 - (3 : ℝ) / K) =
      3 / ((M : ℝ) * ((K : ℝ) - 3)) := by
  obtain ⟨hm, hk⟩ := completion_parameter_casts hM hK
  have hm0 : (M : ℝ) ≠ 0 := by linarith
  have hk0 : (K : ℝ) ≠ 0 := by linarith
  have hk3 : (K : ℝ) - 3 ≠ 0 := by linarith
  field_simp [hm0, hk0, hk3]
  <;> ring

end Paper22
