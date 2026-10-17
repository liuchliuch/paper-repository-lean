/-
Copyright (c) 2026. Corollaries 3.5 and 3.6.
-/
import Paper06.Basic
import Paper06.Witness

open Real Set BigOperators
open scoped Classical

namespace Paper06

/-- **Corollary 3.5**, algebraic skeleton. -/
theorem cor_3_5_skeleton' (θ C : ℝ) (hθ : 0 < θ) (hC : 0 < C) :
    ¬ ((3 * θ / 32 : ℝ) ≤ C * 0) :=
  cor_3_5_skeleton θ C hθ hC

/-- **Corollary 3.6**, constant chain with `c = 3ε/128`. -/
theorem cor_3_6_constants (n k : ℕ) (ε d : ℝ)
    (hn : 6 ≤ n) (hk2 : 2 ≤ k) (hk : k * k ≤ n)
    (hε : 0 < ε) (hε1 : ε < 1 / 2) (hd : 1 ≤ d) :
    (3 * ε * (k : ℝ) * (k - 1) * log d) / (64 * (n - 1))
      ≥ (3 * ε / 128) * ((k : ℝ) * (k - 1) * log d) / (n - k + 1) := by
  have hk1 : (0:ℝ) ≤ k - 1 := by
    have : (2:ℝ) ≤ k := by exact_mod_cast hk2
    linarith
  have hn1 : (0:ℝ) < n - 1 := by
    have : (5:ℝ) ≤ n := by exact_mod_cast (le_trans (by norm_num) hn)
    linarith
  have hnk : (k:ℝ) * k ≤ n := by exact_mod_cast hk
  have hden : (0:ℝ) < n - k + 1 := by
    have : (k:ℝ) ≤ n := by nlinarith
    nlinarith
  have h2 : (n - 1 : ℝ) ≤ 2 * (n - k + 1) := by
    have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk2
    have : (k:ℝ) ≤ n := by nlinarith
    nlinarith
  have hlog : 0 ≤ log d := Real.log_nonneg hd
  have hA : (0:ℝ) ≤ (k : ℝ) * (k - 1) * log d := by positivity
  have hc : (0:ℝ) ≤ 3 * ε / 128 := by positivity
  have hcmp : (1 : ℝ) / (n - k + 1) ≤ 2 / (n - 1) := by
    have h4 : (0:ℝ) < n - 1 := hn1
    have h5 : (0:ℝ) < n - k + 1 := hden
    have hcross : (1:ℝ) * (n - 1) ≤ 2 * (n - k + 1) := by nlinarith
    exact (div_le_div_iff₀ h5 h4).mpr hcross
  have hLHS : (3 * ε * (k : ℝ) * (k - 1) * log d) / (64 * (n - 1))
      = (3 * ε / 128) * ((k : ℝ) * (k - 1) * log d) * (2 / (n - 1)) := by
    field_simp
    ring_nf
  have hRHS : (3 * ε / 128) * ((k : ℝ) * (k - 1) * log d) / (n - k + 1)
      = (3 * ε / 128) * ((k : ℝ) * (k - 1) * log d) * (1 / (n - k + 1)) := by
    rw [div_eq_mul_one_div]
  have hfinal : (3 * ε / 128) * ((k : ℝ) * (k - 1) * log d) * (2 / (n - 1))
      ≥ (3 * ε / 128) * ((k : ℝ) * (k - 1) * log d) * (1 / (n - k + 1)) :=
    mul_le_mul_of_nonneg_left hcmp (mul_nonneg hc hA)
  calc (3 * ε * (k : ℝ) * (k - 1) * log d) / (64 * (n - 1))
      = (3 * ε / 128) * ((k : ℝ) * (k - 1) * log d) * (2 / (n - 1)) := hLHS
    _ ≥ (3 * ε / 128) * ((k : ℝ) * (k - 1) * log d) * (1 / (n - k + 1)) := hfinal
    _ = (3 * ε / 128) * ((k : ℝ) * (k - 1) * log d) / (n - k + 1) := hRHS.symm

/-- Corollary 3.6 lower-bound positivity with `c = 3ε/128`. -/
theorem cor_3_6_nonneg (n k : ℕ) (ε d : ℝ)
    (hn : 6 ≤ n) (hk2 : 2 ≤ k) (hk : k ≤ n) (hε : 0 < ε) (hd : 1 ≤ d) :
    0 ≤ (3 * ε / 128) * ((k : ℝ) * (k - 1) * log d) / (n - k + 1) := by
  have hk1 : (0:ℝ) ≤ k - 1 := by
    have : (2:ℝ) ≤ k := by exact_mod_cast hk2
    linarith
  have hlog : 0 ≤ log d := Real.log_nonneg hd
  have hk0 : (0:ℝ) ≤ k := by exact_mod_cast (Nat.zero_le k)
  have hn1 : (0:ℝ) < n - k + 1 := by
    have hk' : (k:ℝ) ≤ n := by exact_mod_cast hk
    have : (k:ℝ) ≥ 2 := by exact_mod_cast hk2
    have : (5:ℝ) ≤ n := by exact_mod_cast (le_trans (by norm_num) hn)
    nlinarith
  positivity

end Paper06
