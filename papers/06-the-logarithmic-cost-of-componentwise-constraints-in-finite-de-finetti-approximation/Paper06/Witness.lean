/-
Copyright (c) 2026. Matching-event relative-entropy witness (Proposition 3.4).
-/
import Paper06.Basic
import Paper06.Conditioning

open Real Set BigOperators
open scoped Classical

namespace Paper06

/-- Number of candidate internal edges `m = C(k,2) = k(k-1)/2`. -/
def mPairs (k : ℕ) : ℕ := k * (k - 1) / 2

/-- `Real.exp 1 > 1`. -/
theorem exp_one_gt_one : (1:ℝ) < Real.exp 1 := by
  have h : Real.exp (0:ℝ) < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)
  rw [Real.exp_zero] at h
  exact h

/-- Auxiliary: `-log(1 - x) ≤ x / (1 - x)` for `0 ≤ x < 1`. -/
theorem neg_log_one_sub_le' (x : ℝ) (hx : 0 ≤ x) (hx1 : x < 1) :
    -log (1 - x) ≤ x / (1 - x) := by
  have h1 : 0 < 1 - x := by linarith
  have hne : (1 - x : ℝ) ≠ 0 := ne_of_gt h1
  have h2 : 0 < 1 / (1 - x) := by positivity
  have h3 : log (1 / (1 - x)) ≤ 1 / (1 - x) - 1 :=
    log_le_sub_one_of_pos h2
  have h4 : log (1 / (1 - x)) = - log (1 - x) := by
    rw [log_div (by norm_num) (ne_of_gt h1), log_one, zero_sub]
  rw [h4] at h3
  have key : (1:ℝ) / (1 - x) = 1 + x / (1 - x) := by
    have h : (1:ℝ) / (1 - x) = ((1 - x) + x) / (1 - x) := by
      rw [sub_add_cancel]
    rw [h, add_div, div_self hne]
  rw [key] at h3
  linarith

/-- Inclusion–exclusion feasibility: `3 (k(k-1)/2) / (4(n-1)) ≤ 1`. -/
theorem matching_prob_le_one (n k : ℕ)
    (hn : 6 ≤ n) (hk2 : 2 ≤ k) (hk : k * k ≤ n) :
    (3 : ℝ) * ((k : ℝ) * (k - 1) / 2) / (4 * (n - 1)) ≤ 1 := by
  have hnk : (k : ℝ) * k ≤ n := by exact_mod_cast hk
  have hn1 : (0 : ℝ) < n - 1 := by
    have : (5:ℝ) ≤ n := by exact_mod_cast (le_trans (by norm_num) hn)
    linarith
  have hk1 : (0:ℝ) ≤ k - 1 := by
    have : (2:ℝ) ≤ k := by exact_mod_cast hk2
    linarith
  have hkk : (k:ℝ) * (k - 1) ≤ n := by
    have h1 : (k:ℝ) * (k - 1) ≤ k * k := by nlinarith
    exact le_trans h1 hnk
  have hn6 : (6:ℝ) ≤ n := by exact_mod_cast hn
  have h6 : (3:ℝ) / 2 * n ≤ 4 * (n - 1) := by
    have : (0:ℝ) ≤ n - 1 := le_of_lt hn1
    nlinarith
  have h5 : (3:ℝ) / 2 * (k * (k - 1)) ≤ 3 / 2 * n :=
    mul_le_mul_of_nonneg_left hkk (by norm_num)
  have h7 : (3:ℝ) / 2 * (k * (k - 1)) ≤ 4 * (n - 1) := le_trans h5 h6
  have hden : (0:ℝ) < 4 * (n - 1) := by positivity
  rw [div_le_iff₀ hden]
  have h8 : (3:ℝ) * ((k : ℝ) * (k - 1) / 2) = 3 / 2 * (k * (k - 1)) := by ring
  rw [h8, one_mul]
  exact h7

/-- Theorem 3.1 constant chain, positivity. -/
theorem thm_3_1_lb_nonneg (n k : ℕ) (θ d : ℝ)
    (hn : 6 ≤ n) (hk2 : 2 ≤ k) (hθ : 0 < θ) (hd : 1 ≤ d) :
    0 ≤ (3 * θ * k * (k - 1) * log d) / (16 * (n - 1)) := by
  have hk1 : (0:ℝ) ≤ k - 1 := by
    have : (2:ℝ) ≤ k := by exact_mod_cast hk2
    linarith
  have hn1 : (0:ℝ) < n - 1 := by
    have : (5:ℝ) ≤ n := by exact_mod_cast (le_trans (by norm_num) hn)
    linarith
  have hlog : 0 ≤ log d := Real.log_nonneg hd
  have hk0 : (0:ℝ) ≤ k := by exact_mod_cast (Nat.zero_le k)
  positivity

/-- Theorem 3.1 constant comparison. -/
theorem thm_3_1_constants (n k : ℕ) (θ d : ℝ)
    (hn : 6 ≤ n) (hk2 : 2 ≤ k) (hk : k * k ≤ n)
    (hθ : 0 < θ) (hd : 1 ≤ d) :
    (3 * θ * (k : ℝ) * (k - 1) * log d) / (16 * (n - 1))
      ≥ (3 * θ / 32) * ((k : ℝ) * (k - 1) * log d) / (n - k + 1) := by
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
  have hc : (0:ℝ) ≤ 3 * θ / 32 := by positivity
  have hcmp : (1 : ℝ) / (n - k + 1) ≤ 2 / (n - 1) := by
    have h4 : (0:ℝ) < n - 1 := hn1
    have h5 : (0:ℝ) < n - k + 1 := hden
    rw [div_le_div_iff₀ h5 h4]
    nlinarith
  have hLHS : (3 * θ * (k : ℝ) * (k - 1) * log d) / (16 * (n - 1))
      = (3 * θ / 32) * ((k : ℝ) * (k - 1) * log d) * (2 / (n - 1)) := by
    field_simp
    ring_nf
  have hRHS : (3 * θ / 32) * ((k : ℝ) * (k - 1) * log d) / (n - k + 1)
      = (3 * θ / 32) * ((k : ℝ) * (k - 1) * log d) * (1 / (n - k + 1)) := by
    rw [div_eq_mul_one_div]
  have hfinal : (3 * θ / 32) * ((k : ℝ) * (k - 1) * log d) * (2 / (n - 1))
      ≥ (3 * θ / 32) * ((k : ℝ) * (k - 1) * log d) * (1 / (n - k + 1)) :=
    mul_le_mul_of_nonneg_left hcmp (mul_nonneg hc hA)
  calc (3 * θ * (k : ℝ) * (k - 1) * log d) / (16 * (n - 1))
      = (3 * θ / 32) * ((k : ℝ) * (k - 1) * log d) * (2 / (n - 1)) := hLHS
    _ ≥ (3 * θ / 32) * ((k : ℝ) * (k - 1) * log d) * (1 / (n - k + 1)) := hfinal
    _ = (3 * θ / 32) * ((k : ℝ) * (k - 1) * log d) / (n - k + 1) := hRHS.symm

/-- Corollary 3.5 algebraic skeleton. -/
theorem cor_3_5_skeleton (θ C : ℝ) (hθ : 0 < θ) (hC : 0 < C) :
    ¬ ((3 * θ / 32 : ℝ) ≤ C * 0) := by
  intro h0
  have hle : (3 * θ / 32 : ℝ) ≤ 0 := by nlinarith
  have hpos : (0:ℝ) < 3 * θ / 32 := by positivity
  nlinarith

/-- **Proposition 3.4**, constant form nonnegative under `β < 3/(4(n-1))`. -/
theorem prop_3_4_constant_nonneg (n k : ℕ) (β : ℝ)
    (hn : 6 ≤ n) (hk2 : 2 ≤ k) (hβ : 0 < β)
    (hβ1 : β < 3 / (4 * Real.exp 1 * (n - 1))) :
    0 ≤ (3 * (k : ℝ) * (k - 1) / (8 * (n - 1))) *
      log (3 / (4 * Real.exp 1 * (n - 1) * β)) := by
  have hn1 : (0:ℝ) < n - 1 := by
    have : (5:ℝ) ≤ n := by exact_mod_cast (le_trans (by norm_num) hn)
    linarith
  have hk1 : (0:ℝ) ≤ k - 1 := by
    have : (2:ℝ) ≤ k := by exact_mod_cast hk2
    linarith
  have hpos : (0:ℝ) < 4 * (n - 1) := by positivity
  have hcross : β * (4 * Real.exp 1 * (n - 1)) < 3 := by
    have hβ' : β < 3 / (4 * Real.exp 1 * ((n:ℝ) - 1)) := hβ1
    rw [lt_div_iff₀ (by positivity)] at hβ'
    nlinarith
  have he1 : (1:ℝ) < Real.exp 1 := exp_one_gt_one
  have hden : (0:ℝ) < 4 * Real.exp 1 * (n - 1) * β := by positivity
  have h4 : (4 * Real.exp 1 * (n - 1) * β : ℝ) ≤ 3 := by
    have hrew : (4 * Real.exp 1 * (n - 1) * β : ℝ)
        = β * (4 * Real.exp 1 * (n - 1)) := by ring
    rw [hrew]
    exact le_of_lt hcross
  have hge : 1 ≤ 3 / (4 * Real.exp 1 * (n - 1) * β) := by
    rw [one_le_div₀ hden]
    exact h4
  have hlog : 0 ≤ log (3 / (4 * Real.exp 1 * (n - 1) * β)) :=
    Real.log_nonneg hge
  have hk0 : (0:ℝ) ≤ k := by exact_mod_cast (Nat.zero_le k)
  have hcoeff : (0:ℝ) ≤ 3 * (k:ℝ) * (k - 1) / (8 * (n - 1)) := by positivity
  exact mul_nonneg hcoeff hlog

end Paper06
