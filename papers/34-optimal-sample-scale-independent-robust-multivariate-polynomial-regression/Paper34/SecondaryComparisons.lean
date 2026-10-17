import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Section 7: arithmetic of comparisons with published results

The published statistical lower bounds and the published Lebesgue norm
inequality are documented in `ExternalComparisons.json`. They are not declared
as axioms or replaced with a new algorithm model here. This file proves only
the algebra used to combine their numerical bounds.

In ESA 2024, Theorem 1.11 has the factor `d * n / m` (both letters are on the
baseline in the primary PDF). The cube has unnormalized Lebesgue volume `2^n`.
Together with Theorem 1.12 this gives the exponent `2*n + 1` in (7.1).
The resulting grid condition is sufficient for that comparison argument;
it does not establish a necessary grid size for all possible algorithms.
-/

namespace Paper34.SecondaryComparisons

/-- The two inequalities used in (7.1), including the unnormalized cube volume.
`E` is the Lebesgue error and `S` and `L` are the two numerical norm values.
The premises are inequalities between real numbers, not statistical contracts. -/
theorem lebesgue_proxy_composition {E S L A B d m : ℝ} (n : ℕ)
    (hA : 0 ≤ A) (hd : 0 ≤ d) (hm : 0 < m)
    (hproxy : E ≤ (2 : ℝ) ^ n * (A * (d * (n : ℝ) / m) * S))
    (hnorm : S ≤ B * d ^ (2 * n) * L) :
    E ≤ ((2 : ℝ) ^ n * A * B * (n : ℝ)) * (d ^ (2 * n + 1) / m) * L := by
  calc
    E ≤ (2 : ℝ) ^ n * (A * (d * (n : ℝ) / m) * S) := hproxy
    _ ≤ (2 : ℝ) ^ n *
        (A * (d * (n : ℝ) / m) * (B * d ^ (2 * n) * L)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hnorm (by positivity)) (by positivity)
    _ = ((2 : ℝ) ^ n * A * B * (n : ℝ)) *
        (d ^ (2 * n + 1) / m) * L := by
      rw [pow_add, pow_one]
      ring

/-- A grid lower estimate is a sufficient condition for a numerical relative
proxy bound. This direction makes no necessity claim. -/
theorem relative_proxy_of_grid {E L K d m eps : ℝ} (k : ℕ)
    (hm : 0 < m) (hL : 0 ≤ L)
    (hproxy : E ≤ K * (d ^ k / m) * L)
    (hgrid : K * d ^ k ≤ eps * m) : E ≤ eps * L := by
  have hcoeff : K * (d ^ k / m) ≤ eps := by
    rw [← mul_div_assoc, div_le_iff₀ hm]
    exact hgrid
  exact hproxy.trans (mul_le_mul_of_nonneg_right hcoeff hL)

/-- For fixed dimension and a fixed positive lower-bound constant, the
distribution-free lower bound differs from `d^n * log d` by a positive
constant only. No lower bound on an algorithm is assumed or asserted here. -/
theorem distribution_free_lower_factor (c d : ℝ) (n : ℕ) :
    (c * d) ^ n * Real.log d = c ^ n * (d ^ n * Real.log d) := by
  rw [mul_pow]
  ring

/-- The corresponding exact factorization for the uniform-design comparison. -/
theorem uniform_lower_factor (c d : ℝ) (n : ℕ) :
    (c * d) ^ (2 * n) = c ^ (2 * n) * d ^ (2 * n) := by
  rw [mul_pow]

theorem fixed_parameter_factor_pos {c : ℝ} (hc : 0 < c) (k : ℕ) :
    0 < c ^ k := pow_pos hc k

end Paper34.SecondaryComparisons
