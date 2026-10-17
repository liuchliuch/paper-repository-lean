/-
Copyright (c) 2026. Theorem 3.1 constant assembly.
-/
import Paper06.Basic
import Paper06.Witness
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real Set BigOperators
open scoped Classical

namespace Paper06

/-- **Theorem 3.1**, constant assembly of (5) with `log d`. -/
theorem thm_3_1_main_bound (n k d : ℕ) (θ : ℝ)
    (hn : 6 ≤ n) (hk2 : 2 ≤ k) (hk : k * k ≤ n)
    (hθ : 0 < θ) (hd : 2 ≤ d) :
    (3 * θ * (k : ℝ) * (k - 1) * log d) / (16 * (n - 1))
      ≥ (3 * θ / 32) * ((k : ℝ) * (k - 1) * log d) / (n - k + 1) := by
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast (le_trans (by norm_num) hd)
  exact thm_3_1_constants n k θ d hn hk2 hk hθ hd1

/-- `log d = 2 log r` when `d = r²`. -/
theorem thm_3_1_log_d (r : ℕ) (hr : 1 < r) :
    log ((r:ℝ) ^ 2) = 2 * log r := by
  have hpos : (0:ℝ) < r := by
    have : (1:ℝ) < r := by exact_mod_cast hr
    linarith
  rw [Real.log_pow]
  ring_nf

/-- Theorem 3.1 parameter positivity: `r^θ > 1` for `r > 1`, `θ > 0`. -/
theorem thm_3_1_rpow_gt_one (r : ℕ) (θ : ℝ)
    (hr : 1 < r) (hθ : 0 < θ) :
    (1:ℝ) < (r:ℝ) ^ θ := by
  have h1 : (1:ℝ) < r := by exact_mod_cast hr
  exact one_lt_rpow h1 hθ

end Paper06
