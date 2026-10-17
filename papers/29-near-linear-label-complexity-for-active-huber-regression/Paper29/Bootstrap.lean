import Paper29.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-! Deterministic scalar closure of the expectation argument in Lemma 3.5.
This is only the algebra after symmetrization and generic chaining; it is not
an assertion of either of those unproved probabilistic inputs. -/
namespace Paper29

lemma expectation_bootstrap_normalized {y α : ℝ}
    (hy : 0 ≤ y) (hα : 0 ≤ α) (ha1 : α ≤ 1)
    (h : y ^ 2 ≤ α ^ 2 * (1 + y)) : y ≤ 2 * α := by
  by_contra hn
  have hgt : 2 * α < y := lt_of_not_ge hn
  have hs : α ^ 2 ≤ α := by nlinarith
  have hs' : α ^ 2 * y ≤ α * y := mul_le_mul_of_nonneg_right hs hy
  have hp : 0 < (y - 2 * α) * (y + α) :=
    mul_pos (by linarith) (by linarith)
  nlinarith

lemma expectation_bootstrap {X α R : ℝ}
    (hX : 0 ≤ X) (hα : 0 ≤ α) (ha1 : α ≤ 1) (hR : 0 < R)
    (h : X ≤ α * Real.sqrt R * Real.sqrt (R + X)) : X ≤ 2 * α * R := by
  have hRX : 0 ≤ R + X := by positivity
  have hprod : 0 ≤ α * Real.sqrt R * Real.sqrt (R + X) := by positivity
  have hsq : X ^ 2 ≤ (α * Real.sqrt R * Real.sqrt (R + X)) ^ 2 :=
    (sq_le_sq₀ hX hprod).2 h
  have hsR : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR.le
  have hsRX : Real.sqrt (R + X) ^ 2 = R + X := Real.sq_sqrt hRX
  have hsq' : X ^ 2 ≤ α ^ 2 * R * (R + X) := by
    calc
      X ^ 2 ≤ (α * Real.sqrt R * Real.sqrt (R + X)) ^ 2 := hsq
      _ = α ^ 2 * R * (R + X) := by
        simp only [mul_pow, hsR, hsRX]
  have hnorm : (X / R) ^ 2 ≤ α ^ 2 * (1 + X / R) := by
    have hd := div_le_div_of_nonneg_right hsq' (sq_nonneg R)
    convert hd using 1 <;> field_simp <;> ring
  have hbound := expectation_bootstrap_normalized (div_nonneg hX hR.le) hα ha1 hnorm
  exact (div_le_iff₀ hR).1 (by nlinarith only [hbound])

end Paper29
