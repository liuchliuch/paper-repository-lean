/-
Copyright (c) 2026. Mutual information and the conditioning upper bound
(Proposition 2.2) for finite de Finetti approximation.
-/
import Paper06.Basic
import Paper06.Constraints
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Field

open Real Set BigOperators
open scoped Classical

namespace Paper06

/-! ### Marginals -/

/-- Left marginal of a joint law on `α × β`. -/
noncomputable def margL {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb (α × β)) : FinProb α where
  w x := ∑ y, P.w (x, y)
  nonneg := by intro x; exact Finset.sum_nonneg (fun y _ => P.nonneg _)
  sum_eq_one := by
    have key : ∑ x, ∑ y, P.w (x, y) = ∑ z : α × β, P.w z :=
      (Fintype.sum_prod_type' (fun x y => P.w (x, y))).symm
    rw [key, P.sum_eq_one]

/-- Right marginal of a joint law on `α × β`. -/
noncomputable def margR {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb (α × β)) : FinProb β where
  w y := ∑ x, P.w (x, y)
  nonneg := by intro y; exact Finset.sum_nonneg (fun x _ => P.nonneg _)
  sum_eq_one := by
    have h4 : ∑ y : β, ∑ x : α, P.w (x, y) = ∑ z : α × β, P.w z :=
      (Fintype.sum_prod_type_right' (fun (x : α) (y : β) => P.w (x, y))).symm
    rw [h4, P.sum_eq_one]

/-- Mutual information `I(U; V) = H(U) + H(V) - H(U,V)`. -/
noncomputable def mutInfo {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb (α × β)) : ℝ :=
  FinProb.entropy (margL P) + FinProb.entropy (margR P) - FinProb.entropy P

/-! ### Sampling-without-replacement bound `L(n,k)` -/

/-- `L(n,k) = log(n^k / (n)_k)` with `Nat.descFactorial`. -/
noncomputable def Lbound (n k : ℕ) : ℝ :=
  log (((n : ℝ) ^ k) / (Nat.descFactorial n k : ℝ))

/-- Auxiliary: `-log(1 - x) ≤ x / (1 - x)` for `0 ≤ x < 1`. -/
theorem neg_log_one_sub_le (x : ℝ) (hx : 0 ≤ x) (hx1 : x < 1) :
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

/-- Auxiliary: `∑_{i < k} i / (n - k + 1) = k(k-1) / (2(n-k+1))` for `1 ≤ k < n`. -/
theorem sum_range_div_eq (k n : ℕ) (hk : 1 ≤ k) (hn : k < n) :
    ∑ i ∈ Finset.range k, (i : ℝ) / (n - k + 1)
      = (k * (k - 1) : ℝ) / (2 * (n - k + 1)) := by
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by omega)
  have hden : 0 < (n - k + 1 : ℝ) := by
    have : (k:ℝ) < n := by exact_mod_cast hn
    linarith
  have hden0 : (n - k + 1 : ℝ) ≠ 0 := ne_of_gt hden
  have hcast1 : ((k - 1 : ℕ) : ℝ) = (k:ℝ) - 1 := Nat.cast_pred hk0
  have hmul2 : (∑ i ∈ Finset.range k, (i : ℝ)) * 2 = (k:ℝ) * (k - 1) := by
    have h := congrArg (Nat.cast : ℕ → ℝ) (Finset.sum_range_id_mul_two k)
    simp only [Nat.cast_mul, Nat.cast_two] at h
    rw [hcast1, Nat.cast_sum] at h
    exact h
  have hsum : ∑ i ∈ Finset.range k, (i : ℝ) = (k:ℝ) * (k - 1) / 2 :=
    eq_div_of_mul_eq (by norm_num) hmul2
  rw [← Finset.sum_div, hsum]
  field_simp [hden0]

/-- **Sampling-without-replacement bound** (paper eq. 1):
`L(n,k) = log(n^k / (n)_k) ≤ k(k-1) / (2(n-k+1))` for `1 ≤ k < n`. -/
theorem Lbound_le (n k : ℕ) (hk : 1 ≤ k) (hn : k < n) :
    Lbound n k ≤ (k * (k - 1) : ℝ) / (2 * (n - k + 1)) := by
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by omega)
  have hn0 : 0 < n := lt_trans hk0 hn
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn0
  have hne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hknat : k ≤ n := Nat.le_of_lt hn
  have hdesc : 0 < n.descFactorial k := Nat.descFactorial_pos.mpr hknat
  have hdescne : (n.descFactorial k : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hdesc)
  -- Expand `Lbound` as a sum of `-log(1 - i/n)`.
  unfold Lbound
  rw [Real.log_div (pow_ne_zero k hne) hdescne, Real.log_pow]
  rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  have hprodne : ∀ i ∈ Finset.range k, ((n - i : ℕ) : ℝ) ≠ 0 := by
    intro i hi
    have hi' : i < k := Finset.mem_range.mp hi
    have hiln : i < n := lt_trans hi' hn
    have hpos : 0 < (n - i : ℕ) := Nat.sub_pos_of_lt hiln
    exact_mod_cast (ne_of_gt hpos)
  rw [Real.log_prod _ _ hprodne]
  have hsumlog : (k * log (n:ℝ) : ℝ) = ∑ _i ∈ Finset.range k, log (n:ℝ) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hsumlog, ← Finset.sum_sub_distrib]
  have hterm : ∀ i ∈ Finset.range k,
      log (n:ℝ) - log ((n - i : ℕ) : ℝ) = -log (1 - (i:ℝ)/n) := by
    intro i hi
    have hi' : i < k := Finset.mem_range.mp hi
    have hiln : i < n := lt_trans hi' hn
    have hsub : ((n - i : ℕ) : ℝ) = (n:ℝ) - i :=
      Nat.cast_sub (Nat.le_of_lt hiln)
    have hine : ((n - i : ℕ) : ℝ) ≠ 0 := hprodne i hi
    have hx0 : 0 ≤ (i:ℝ)/n := by positivity
    have hx1 : (i:ℝ)/n < 1 := (div_lt_one hnpos).mpr (by exact_mod_cast hiln)
    have hone : (1 - (i:ℝ)/n) ≠ 0 := by linarith
    have hratio : (n:ℝ) / ((n - i : ℕ) : ℝ) = (1:ℝ) / (1 - (i:ℝ)/n) := by
      rw [hsub]
      have hne1 : (n:ℝ) - i ≠ 0 := by
        have : (i:ℝ) < n := by exact_mod_cast hiln
        linarith
      field_simp [hne, hne1, hone]
    calc log (n:ℝ) - log ((n - i : ℕ) : ℝ)
        = log ((n:ℝ) / ((n - i : ℕ) : ℝ)) := (Real.log_div hne hine).symm
      _ = log ((1:ℝ) / (1 - (i:ℝ)/n)) := by rw [hratio]
      _ = -log (1 - (i:ℝ)/n) := by
          rw [Real.log_div (by norm_num) hone, Real.log_one, zero_sub]
  rw [Finset.sum_congr rfl hterm]
  -- Bound each term by `i / (n - k + 1)`.
  have hbound : ∀ i ∈ Finset.range k,
      -log (1 - (i:ℝ)/n) ≤ (i:ℝ) / (n - k + 1) := by
    intro i hi
    have hi' : i < k := Finset.mem_range.mp hi
    have hiln : i < n := lt_trans hi' hn
    have hx0 : 0 ≤ (i:ℝ)/n := by positivity
    have hx1 : (i:ℝ)/n < 1 := (div_lt_one hnpos).mpr (by exact_mod_cast hiln)
    have hble := neg_log_one_sub_le ((i:ℝ)/n) hx0 hx1
    have hsub : ((n - i : ℕ) : ℝ) = (n:ℝ) - i :=
      Nat.cast_sub (Nat.le_of_lt hiln)
    have hratio : (i:ℝ)/n / (1 - (i:ℝ)/n) = (i:ℝ) / ((n - i : ℕ) : ℝ) := by
      rw [hsub]
      have hne1 : (n:ℝ) - i ≠ 0 := by
        have : (i:ℝ) < n := by exact_mod_cast hiln
        linarith
      have hone : 1 - (i:ℝ)/n ≠ 0 := by linarith
      field_simp [hne, hne1, hone]
    have hden1 : 0 < (n - k + 1 : ℝ) := by
      have : (k:ℝ) < n := by exact_mod_cast hn
      linarith
    have hden2 : 0 < ((n - i : ℕ) : ℝ) := by
      have : 0 < (n - i : ℕ) := Nat.sub_pos_of_lt hiln
      exact_mod_cast this
    have hi1 : (i:ℝ) ≤ k - 1 := by
      have h1 : i ≤ k - 1 := Nat.le_pred_of_lt hi'
      rw [← Nat.cast_pred hk0]
      exact_mod_cast h1
    have hcmp : (n - k + 1 : ℝ) ≤ ((n - i : ℕ) : ℝ) := by
      rw [hsub]
      have : (k:ℝ) ≥ 1 := by exact_mod_cast hk
      linarith
    calc -log (1 - (i:ℝ)/n)
        ≤ (i:ℝ)/n / (1 - (i:ℝ)/n) := hble
      _ = (i:ℝ) / ((n - i : ℕ) : ℝ) := hratio
      _ ≤ (i:ℝ) / (n - k + 1) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg i) hden1 hcmp
  have hsumle := Finset.sum_le_sum hbound
  have hsumeq := sum_range_div_eq k n hk hn
  exact hsumle.trans (le_of_eq hsumeq)

/-- **Proposition 2.2**, nonnegativity of the right-hand side. -/
theorem prop_2_2_bound (n k d : ℕ) (hd : 0 < d)
    (hk : 1 ≤ k) (hn : k < n) :
    0 ≤ (k * (k - 1) : ℝ) / (2 * (n - k + 1)) * log d := by
  have hk1 : (0:ℝ) ≤ k - 1 := by
    have : (1:ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hn1 : (0:ℝ) < n - k + 1 := by
    have : (k:ℝ) < n := by exact_mod_cast hn
    linarith
  have hlog : 0 ≤ log (d:ℝ) := Real.log_nonneg (by
    have : (1:ℝ) ≤ d := by exact_mod_cast (Nat.succ_le_of_lt hd)
    exact this)
  have hk0 : (0:ℝ) ≤ k := by exact_mod_cast (Nat.zero_le k)
  positivity

/-- The entropy average of Proposition 2.2 is nonnegative. -/
theorem prop_2_2_entropy_average (k n d : ℕ) (hd : 1 ≤ d) :
    (k * (k - 1) : ℝ) / 2 * log d ≥ 0 := by
  have hlog : 0 ≤ log (d:ℝ) := Real.log_nonneg (by exact_mod_cast hd)
  have hk0 : (0:ℝ) ≤ k := by exact_mod_cast (Nat.zero_le k)
  by_cases h : k = 0
  · subst h
    simp
  · have hk1 : (0:ℝ) ≤ k - 1 := by
      have : 1 ≤ k := Nat.succ_le_of_lt (Nat.pos_of_ne_zero h)
      have : (1:ℝ) ≤ k := by exact_mod_cast this
      have : (0:ℝ) ≤ (k:ℝ) - 1 := by linarith
      exact this
    positivity

end Paper06
