import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Scalar schedules and the geometric accounting in Sections 3, 4 and 7 of P31.
The stage `n + 1` is indexed by `n : ℕ` in the finite sums. -/

namespace P31.Schedule

open scoped BigOperators

noncomputable def deltaDenom (p κ : ℝ) : ℝ := κ * p + κ - p
noncomputable def beta (p κ : ℝ) : ℝ := p / deltaDenom p κ
noncomputable def tau (p κ : ℝ) : ℝ := (2 : ℝ) ^ (p - (κ + 1) / 2)
noncomputable def ratio (κ : ℝ) : ℝ := (2 : ℝ) ^ (-(κ - 1) / 2)
noncomputable def theta (p : ℝ) : ℝ := (2 : ℝ) ^ (-(p - 1))
noncomputable def radius (R : ℝ) (s : ℕ) : ℝ := R / (2 : ℝ) ^ s
noncomputable def sigma (σ₁ τ : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => σ₁ * τ ^ n
noncomputable def alpha (σ₁ τ : ℝ) (s : ℕ) : ℝ := sigma σ₁ τ s - sigma σ₁ τ (s - 1)

@[simp] theorem sigma_zero (σ₁ τ : ℝ) : sigma σ₁ τ 0 = 0 := rfl
@[simp] theorem sigma_succ (σ₁ τ : ℝ) (n : ℕ) : sigma σ₁ τ (n+1) = σ₁ * τ ^ n := rfl
@[simp] theorem alpha_one (σ₁ τ : ℝ) : alpha σ₁ τ 1 = σ₁ := by simp [alpha]
theorem alpha_succ_succ (σ₁ τ : ℝ) (n : ℕ) :
    alpha σ₁ τ (n+2) = σ₁ * (τ-1) * τ ^ n := by
  simp [alpha, pow_succ]
  ring

theorem deltaDenom_pos {p κ : ℝ} (hp : 2 ≤ p) (hκ : 1 < κ) :
    0 < deltaDenom p κ := by
  have h := mul_pos (sub_pos.mpr hκ) (show 0 < p by linarith)
  dsimp [deltaDenom]
  nlinarith

theorem beta_pos {p κ : ℝ} (hp : 2 ≤ p) (hκ : 1 < κ) : 0 < beta p κ :=
  div_pos (by linarith) (deltaDenom_pos hp hκ)

theorem tau_gt_one {p κ : ℝ} (hp : 2 ≤ p) (hκ : κ ≤ 2) : 1 < tau p κ := by
  apply Real.one_lt_rpow (by norm_num : (1:ℝ) < 2)
  linarith

theorem ratio_pos (κ : ℝ) : 0 < ratio κ := Real.rpow_pos_of_pos (by norm_num) _
theorem ratio_lt_one {κ : ℝ} (hκ : 1 < κ) : ratio κ < 1 := by
  apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1:ℝ) < 2)
  linarith

theorem theta_pos (p : ℝ) : 0 < theta p := Real.rpow_pos_of_pos (by norm_num) _
theorem theta_lt_one {p : ℝ} (hp : 2 ≤ p) : theta p < 1 := by
  apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1:ℝ) < 2)
  linarith

theorem tau_mul_theta (p κ : ℝ) : tau p κ * theta p = ratio κ := by
  dsimp [tau, theta, ratio]
  rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  congr 1
  ring

theorem cost_ratio (p κ : ℝ) : (2:ℝ) ^ (p-κ) / tau p κ = ratio κ := by
  dsimp [tau, ratio]
  rw [← Real.rpow_sub (by norm_num : (0:ℝ) < 2)]
  congr 1
  ring

theorem alpha_pos {σ₁ τ : ℝ} (hσ : 0 < σ₁) (hτ : 1 < τ) {s : ℕ}
    (hs : 0 < s) : 0 < alpha σ₁ τ s := by
  rcases s with _ | n
  · omega
  rcases n with _ | n
  · simpa using hσ
  · rw [show n+1+1=n+2 by omega, alpha_succ_succ]
    exact mul_pos (mul_pos hσ (sub_pos.mpr hτ)) (pow_pos (by linarith) _)

theorem sum_alpha (σ₁ τ : ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, alpha σ₁ τ (k+1)) = sigma σ₁ τ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp [alpha]

/-- Every partial geometric series lies below its convergent sum. -/
theorem geom_sum_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    (∑ k ∈ Finset.range n, r ^ k) ≤ 1 / (1-r) := by
  apply (le_div_iff₀ (sub_pos.mpr hr1)).2
  rw [geom_sum_mul_neg]
  exact sub_le_self _ (pow_nonneg hr0 _)

/-- The exact finite form of (4.5), including the exceptional first increment. -/
theorem weighted_alpha_sum (σ₁ τ θ : ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (n+1), alpha σ₁ τ (k+1) * θ ^ k) =
      σ₁ + σ₁ * (τ-1) * θ * ∑ k ∈ Finset.range n, (τ*θ) ^ k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ,
      show n+1+1=n+2 by omega, alpha_succ_succ, pow_succ, mul_pow]
    ring

/-- Finite-history version of (4.5), sufficient for every terminal stage. -/
theorem weighted_alpha_sum_le {σ₁ τ θ : ℝ}
    (hσ : 0 ≤ σ₁) (hτ : 1 ≤ τ) (hθ : 0 ≤ θ) (hr : τ*θ < 1) (n : ℕ) :
    (∑ k ∈ Finset.range n, alpha σ₁ τ (k+1) * θ ^ k) ≤
      σ₁ * (1-θ) / (1-τ*θ) := by
  have hden : 0 < 1-τ*θ := sub_pos.mpr hr
  have hc : 0 ≤ σ₁ * (τ-1) * θ := mul_nonneg (mul_nonneg hσ (sub_nonneg.mpr hτ)) hθ
  cases n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    apply div_nonneg
    · apply mul_nonneg hσ
      have : θ ≤ τ*θ := by nlinarith
      linarith
    · exact le_of_lt hden
  | succ n =>
    rw [weighted_alpha_sum]
    calc
      σ₁ + σ₁ * (τ-1) * θ * ∑ k ∈ Finset.range n, (τ*θ)^k
        ≤ σ₁ + σ₁ * (τ-1) * θ * (1 / (1-τ*θ)) :=
          add_le_add_left (mul_le_mul_of_nonneg_left
            (geom_sum_le (mul_nonneg (by linarith) hθ) hr n) hc) _
      _ = σ₁ * (1-θ) / (1-τ*θ) := by field_simp; ring

/-- Paper (4.5) in its balanced-schedule parameters. -/
theorem balanced_weighted_alpha_sum_le {p κ σ₁ : ℝ}
    (hp : 2 ≤ p) (hκlo : 1 < κ) (hκhi : κ ≤ 2) (hσ : 0 ≤ σ₁) (n : ℕ) :
    (∑ k ∈ Finset.range n, alpha σ₁ (tau p κ) (k+1) * theta p ^ k) ≤
      σ₁ * (1-theta p) / (1-ratio κ) := by
  simpa only [tau_mul_theta] using weighted_alpha_sum_le hσ
    (le_of_lt (tau_gt_one hp hκhi)) (le_of_lt (theta_pos p))
    (by rw [tau_mul_theta]; exact ratio_lt_one hκlo) n

/-- A positive geometric stage scale has summable power costs, cf. (4.12). -/
theorem geometric_power_sum_le {B r b : ℝ} (hB : 0 ≤ B)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hb : 0 < b) (n : ℕ) :
    (∑ k ∈ Finset.range n, (B * r ^ k) ^ b) ≤ B ^ b / (1-r ^ b) := by
  have hpow : r^b < 1 := Real.rpow_lt_one hr0 hr1 hb
  calc
    (∑ k ∈ Finset.range n, (B * r^k)^b)
      = B^b * ∑ k ∈ Finset.range n, (r^b)^k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [Real.mul_rpow hB (pow_nonneg hr0 _), ← Real.rpow_natCast,
          ← Real.rpow_mul hr0, mul_comm (k:ℝ) b, Real.rpow_mul hr0, Real.rpow_natCast]
    _ ≤ B^b * (1 / (1-r^b)) := mul_le_mul_of_nonneg_left
      (geom_sum_le (Real.rpow_nonneg hr0 b) hpow n) (Real.rpow_nonneg hB b)
    _ = B^b / (1-r^b) := by ring

/-- Summing (4.9) after establishing the exact recurrence (4.10). -/
theorem budget_sum_le {C B r b : ℝ} {T : ℕ → ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hr0 : 0 ≤ r) (hr1 : r < 1) (hb : 0 < b)
    (hT : ∀ k, T k ≤ C * (1+(B*r^k)^b)) (n : ℕ) :
    (∑ k ∈ Finset.range n, T k) ≤ C * ((n:ℝ) + B^b / (1-r^b)) := by
  calc
    (∑ k ∈ Finset.range n, T k)
      ≤ ∑ k ∈ Finset.range n, C * (1+(B*r^k)^b) := Finset.sum_le_sum (fun k _ => hT k)
    _ = C * ((n:ℝ) + ∑ k ∈ Finset.range n, (B*r^k)^b) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      simp
    _ ≤ C * ((n:ℝ) + B^b / (1-r^b)) := mul_le_mul_of_nonneg_left
      (add_le_add_left (geometric_power_sum_le hB hr0 hr1 hb n) _) hC

/-- Scalar normalization of (3.4), with `A = aₚ U^(p-1) R^(p-1)`. -/
noncomputable def initialWeight (A θ r ε : ℝ) : ℝ := (1-r)*ε / (2*A*(1-θ))

theorem initialWeight_pos {A θ r ε : ℝ} (hA : 0 < A) (hθ : θ < 1)
    (hr : r < 1) (hε : 0 < ε) : 0 < initialWeight A θ r ε := by
  exact div_pos (mul_pos (sub_pos.mpr hr) hε)
    (mul_pos (mul_pos (by norm_num) hA) (sub_pos.mpr hθ))

theorem initialWeight_calibration {A θ r ε : ℝ} (hA : 0 < A)
    (hθ : θ < 1) (hr : r < 1) :
    A * (initialWeight A θ r ε * (1-θ) / (1-r)) = ε/2 := by
  have hA0 : A ≠ 0 := ne_of_gt hA
  have hθ0 : 1-θ ≠ 0 := ne_of_gt (sub_pos.mpr hθ)
  have hr0 : 1-r ≠ 0 := ne_of_gt (sub_pos.mpr hr)
  dsimp [initialWeight]
  field_simp

/-- The regularizer-gradient bias is at most half the requested accuracy. -/
theorem calibrated_history_bound {p κ A ε : ℝ} (hp : 2 ≤ p)
    (hκlo : 1 < κ) (hκhi : κ ≤ 2) (hA : 0 < A) (hε : 0 < ε) (n : ℕ) :
    A * (∑ k ∈ Finset.range n,
      alpha (initialWeight A (theta p) (ratio κ) ε) (tau p κ) (k+1) * theta p ^ k)
      ≤ ε/2 := by
  have hw := initialWeight_pos hA (theta_lt_one hp) (ratio_lt_one hκlo) hε
  calc
    _ ≤ A * (initialWeight A (theta p) (ratio κ) ε * (1-theta p) / (1-ratio κ)) :=
      mul_le_mul_of_nonneg_left (balanced_weighted_alpha_sum_le hp hκlo hκhi (le_of_lt hw) n)
        (le_of_lt hA)
    _ = ε/2 := initialWeight_calibration hA (theta_lt_one hp) (ratio_lt_one hκlo)

@[simp] theorem radius_zero (R : ℝ) : radius R 0 = R := by simp [radius]
theorem radius_pos {R : ℝ} (hR : 0 < R) (n : ℕ) : 0 < radius R n :=
  div_pos hR (pow_pos (by norm_num) _)
theorem radius_succ (R : ℝ) (n : ℕ) : radius R (n+1) = radius R n / 2 := by
  simp only [radius, pow_succ]
  ring

theorem sigma_succ_succ (σ₁ τ : ℝ) (n : ℕ) :
    sigma σ₁ τ (n+2) = τ * sigma σ₁ τ (n+1) := by
  simp [sigma, pow_succ]
  ring

/-- The paper's `Bₛ`, with `n = s-1`. -/
noncomputable def stageScale (L σ₁ τ R p κ : ℝ) (n : ℕ) : ℝ :=
  L / (sigma σ₁ τ (n+1) * radius R (n+1) ^ (p-κ))

theorem stageScale_succ {L σ₁ τ R p κ : ℝ} (hR : 0 < R) (n : ℕ) :
    stageScale L σ₁ τ R p κ (n+1) =
      ((2:ℝ) ^ (p-κ) / τ) * stageScale L σ₁ τ R p κ n := by
  change L / (sigma σ₁ τ (n+2) * radius R (n+2) ^ (p-κ)) =
    ((2:ℝ) ^ (p-κ) / τ) * (L / (sigma σ₁ τ (n+1) * radius R (n+1) ^ (p-κ)))
  rw [sigma_succ_succ, show n+2=(n+1)+1 by omega, radius_succ,
    Real.div_rpow (le_of_lt (radius_pos hR _)) (by norm_num : (0:ℝ) ≤ 2)]
  by_cases hτ : τ = 0
  · simp [hτ]
  by_cases hσ : σ₁ * τ^n = 0
  · simp [hσ]
  have hrad : radius R (n+1) ^ (p-κ) ≠ 0 := ne_of_gt
    (Real.rpow_pos_of_pos (radius_pos hR _) _)
  have htwo : (2:ℝ) ^ (p-κ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  field_simp

/-- Exact geometric form of the scale sequence in (4.10). -/
theorem balanced_stageScale {L σ₁ R p κ : ℝ} (hR : 0 < R) (n : ℕ) :
    stageScale L σ₁ (tau p κ) R p κ n =
      stageScale L σ₁ (tau p κ) R p κ 0 * ratio κ ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [stageScale_succ hR, cost_ratio, ih, pow_succ]; ring

/-- Direct substitution of (3.4) into `B₁`, i.e. (4.11).
Here `A = aₚ U^(p-1)`; the factor `R^(p-1)` is kept explicitly. -/
theorem calibrated_first_stageScale {A R θ r ε L τ p κ : ℝ}
    (hA : 0 < A) (hR : 0 < R) (hθ : θ < 1) (hr : r < 1) (hε : 0 < ε) :
    stageScale L (initialWeight (A*R^(p-1)) θ r ε) τ R p κ 0 =
      (2*A*(1-θ)*(2:ℝ)^(p-κ)/(1-r)) * (L*R^(κ-1)/ε) := by
  have hA0 : A ≠ 0 := ne_of_gt hA
  have hε0 : ε ≠ 0 := ne_of_gt hε
  have hθ0 : 1-θ ≠ 0 := ne_of_gt (sub_pos.mpr hθ)
  have hr0 : 1-r ≠ 0 := ne_of_gt (sub_pos.mpr hr)
  have hRp0 : R^(p-κ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hR _)
  have hRk0 : R^(κ-1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hR _)
  have htwo0 : (2:ℝ)^(p-κ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  have hRp : R^(p-1) = R^(p-κ)*R^(κ-1) := by
    rw [← Real.rpow_add hR]
    congr 1
    ring
  simp only [stageScale, sigma_succ, pow_zero, mul_one, radius, Nat.zero_add, pow_one, initialWeight]
  rw [Real.div_rpow (le_of_lt hR) (by norm_num : (0:ℝ) ≤ 2), hRp]
  field_simp

/-- The exact finite stopping stage from (3.3). -/
noncomputable def stageCount (L R κ ε : ℝ) : ℕ :=
  ⌈Real.logb 2 (2*L*R^(κ-1)/ε) / (κ-1)⌉₊

/-- The ceiling schedule makes the Hölder-transfer term at most `ε/2`, as in (4.7). -/
theorem terminal_radius_bound {L R κ ε : ℝ} (hL : 0 < L) (hR : 0 < R)
    (hκ : 1 < κ) (hε : 0 < ε) :
    L * radius R (stageCount L R κ ε) ^ (κ-1) ≤ ε/2 := by
  let S := stageCount L R κ ε
  let Q : ℝ := 2*L*R^(κ-1)/ε
  have hκ0 : 0 < κ-1 := sub_pos.mpr hκ
  have hRp : 0 < R^(κ-1) := Real.rpow_pos_of_pos hR _
  have hQ : 0 < Q := div_pos (mul_pos (mul_pos (by norm_num) hL) hRp) hε
  have hceil : Real.logb 2 Q / (κ-1) ≤ (S:ℝ) := Nat.le_ceil _
  have hexp : Real.logb 2 Q ≤ (S:ℝ)*(κ-1) := (div_le_iff₀ hκ0).mp hceil
  have hpow : Q ≤ (2:ℝ)^((S:ℝ)*(κ-1)) := by
    calc
      Q = (2:ℝ) ^ Real.logb 2 Q :=
        (Real.rpow_logb (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≠ 1) hQ).symm
      _ ≤ (2:ℝ)^((S:ℝ)*(κ-1)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hden : 0 < (2:ℝ)^((S:ℝ)*(κ-1)) := Real.rpow_pos_of_pos (by norm_num) _
  have hrad : radius R S ^ (κ-1) = R^(κ-1) / (2:ℝ)^((S:ℝ)*(κ-1)) := by
    rw [radius, Real.div_rpow (le_of_lt hR) (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) _)]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  change L * radius R S ^ (κ-1) ≤ ε/2
  rw [hrad, ← mul_div_assoc]
  have hQ' : 2*L*R^(κ-1) ≤ (2:ℝ)^((S:ℝ)*(κ-1))*ε :=
    (div_le_iff₀ hε).mp hpow
  apply (div_le_iff₀ hden).2
  nlinarith

/-- The additive logarithmic stage count is absorbed by every positive power.
The displayed constant depends only on `κ` and `b`, never on `Λ`. -/
theorem ceiling_log_le_power {κ b Λ : ℝ} (hκ : 1 < κ) (hb : 0 < b) (hΛ : 1 ≤ Λ) :
    (⌈Real.logb 2 (2*Λ) / (κ-1)⌉₊ : ℝ) ≤
      ((1 + 1 / (b * Real.log 2)) / (κ-1) + 1) * Λ^b := by
  have hΛ0 : 0 < Λ := lt_of_lt_of_le (by norm_num) hΛ
  have hP : 1 ≤ Λ^b := Real.one_le_rpow hΛ (le_of_lt hb)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl : Real.log Λ ≤ Λ^b / b := by
    apply (le_div_iff₀ hb).2
    have hx := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hΛ0 b)
    rw [Real.log_rpow hΛ0] at hx
    nlinarith
  have hlog : Real.logb 2 (2*Λ) ≤ (1 + 1 / (b*Real.log 2)) * Λ^b := by
    calc
      Real.logb 2 (2*Λ) = 1 + Real.log Λ / Real.log 2 := by
        rw [Real.logb, Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (ne_of_gt hΛ0)]
        field_simp [ne_of_gt hl2]
      _ ≤ 1 + (Λ^b / b) / Real.log 2 :=
        add_le_add_left (div_le_div_of_nonneg_right hl (le_of_lt hl2)) _
      _ ≤ Λ^b + (Λ^b / b) / Real.log 2 := add_le_add_right hP _
      _ = (1 + 1 / (b*Real.log 2)) * Λ^b := by ring
  have hnon : 0 ≤ Real.logb 2 (2*Λ) / (κ-1) := by
    apply div_nonneg _ (le_of_lt (sub_pos.mpr hκ))
    exact Real.logb_nonneg (by norm_num : (1:ℝ) < 2) (by linarith)
  calc
    (⌈Real.logb 2 (2*Λ) / (κ-1)⌉₊ : ℝ)
      ≤ Real.logb 2 (2*Λ) / (κ-1) + 1 := (Nat.ceil_lt_add_one hnon).le
    _ ≤ ((1 + 1 / (b*Real.log 2))*Λ^b) / (κ-1) + 1 :=
      add_le_add_right (div_le_div_of_nonneg_right hlog (le_of_lt (sub_pos.mpr hκ))) _
    _ ≤ ((1 + 1 / (b*Real.log 2))*Λ^b) / (κ-1) + Λ^b := add_le_add_left hP _
    _ = ((1 + 1 / (b*Real.log 2)) / (κ-1) + 1)*Λ^b := by ring

/-- Complete scalar query accounting: summing stages and absorbing their count
introduces no multiplicative logarithmic factor. -/
theorem logarithmic_budget_le_power {κ b Λ C K r : ℝ} {T : ℕ → ℝ}
    (hκ : 1 < κ) (hb : 0 < b) (hΛ : 1 ≤ Λ) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hT : ∀ k, T k ≤ C*(1+(K*Λ*r^k)^b)) :
    (∑ k ∈ Finset.range ⌈Real.logb 2 (2*Λ)/(κ-1)⌉₊, T k) ≤
      C * (((1 + 1/(b*Real.log 2))/(κ-1) + 1 + K^b/(1-r^b))*Λ^b) := by
  have hΛ0 : 0 ≤ Λ := by linarith
  calc
    _ ≤ C * ((⌈Real.logb 2 (2*Λ)/(κ-1)⌉₊ : ℝ) + (K*Λ)^b/(1-r^b)) :=
      budget_sum_le hC (mul_nonneg hK hΛ0) hr0 hr1 hb hT _
    _ ≤ C * ((((1 + 1/(b*Real.log 2))/(κ-1) + 1)*Λ^b) + (K*Λ)^b/(1-r^b)) :=
      mul_le_mul_of_nonneg_left (add_le_add_right (ceiling_log_le_power hκ hb hΛ) _) hC
    _ = C * (((1 + 1/(b*Real.log 2))/(κ-1) + 1 + K^b/(1-r^b))*Λ^b) := by
      rw [Real.mul_rpow hK hΛ0]
      ring

/-- Rounding the fixed stage query budget costs only a parameter-dependent factor. -/
theorem ceil_budget_le {C factor B b : ℝ} (hC : 0 ≤ C) (hf : 0 ≤ factor) (hB : 0 ≤ B) :
    (⌈C*(1+factor*B^b)⌉₊ : ℝ) ≤ (C*(1+factor)+1)*(1+B^b) := by
  have hx : 0 ≤ B^b := Real.rpow_nonneg hB _
  have hnon : 0 ≤ C*(1+factor*B^b) := mul_nonneg hC (by nlinarith [mul_nonneg hf hx])
  have hc := (Nat.ceil_lt_add_one hnon).le
  nlinarith [mul_nonneg hC hf, mul_nonneg hC hx]

noncomputable def leadingScale (A p κ : ℝ) : ℝ :=
  2*A*(1-theta p)*(2:ℝ)^(p-κ)/(1-ratio κ)

noncomputable def queryConstant (C A p κ : ℝ) : ℝ :=
  (C*(1+(2:ℝ)^(κ*beta p κ))+1) *
    ((1+1/(beta p κ*Real.log 2))/(κ-1)+1+
      leadingScale A p κ ^ beta p κ / (1-ratio κ ^ beta p κ))

/-- The integer budget in (3.7), with the paper's calibrated history weight. -/
noncomputable def queryBudget (C A L R p κ ε : ℝ) (n : ℕ) : ℕ :=
  ⌈C*(1+(2:ℝ)^(κ*beta p κ)*
    stageScale L (initialWeight (A*R^(p-1)) (theta p) (ratio κ) ε)
      (tau p κ) R p κ n ^ beta p κ)⌉₊

theorem leadingScale_pos {A p κ : ℝ} (hA : 0 < A) (hp : 2 ≤ p) (hκ : 1 < κ) :
    0 < leadingScale A p κ := by
  exact div_pos (mul_pos (mul_pos (mul_pos (by norm_num) hA)
    (sub_pos.mpr (theta_lt_one hp))) (Real.rpow_pos_of_pos (by norm_num) _))
    (sub_pos.mpr (ratio_lt_one hκ))

theorem queryConstant_pos {C A p κ : ℝ} (hC : 0 ≤ C) (hA : 0 < A)
    (hp : 2 ≤ p) (hκ : 1 < κ) : 0 < queryConstant C A p κ := by
  have hb : 0 < beta p κ := beta_pos hp hκ
  have hr0 : 0 ≤ ratio κ := le_of_lt (ratio_pos κ)
  have hr1 : ratio κ < 1 := ratio_lt_one hκ
  have hden : 0 < 1-ratio κ ^ beta p κ :=
    sub_pos.mpr (Real.rpow_lt_one hr0 hr1 hb)
  have hl : 0 < beta p κ * Real.log 2 := mul_pos hb (Real.log_pos (by norm_num))
  have hf : 0 ≤ (2:ℝ)^(κ*beta p κ) := Real.rpow_nonneg (by norm_num) _
  have hout : 0 < C*(1+(2:ℝ)^(κ*beta p κ))+1 := by
    nlinarith [mul_nonneg hC hf]
  have hfirst : 0 < (1+1/(beta p κ*Real.log 2))/(κ-1)+1 :=
    add_pos (div_pos (add_pos zero_lt_one (div_pos zero_lt_one hl))
      (sub_pos.mpr hκ)) zero_lt_one
  have htail : 0 ≤ leadingScale A p κ ^ beta p κ / (1-ratio κ ^ beta p κ) :=
    div_nonneg (Real.rpow_nonneg (le_of_lt (leadingScale_pos hA hp hκ)) _)
      (le_of_lt hden)
  exact mul_pos hout (add_pos_of_pos_of_nonneg hfirst htail)

/-- The full scalar bound for the fixed integer budgets, after substituting
both the initial regularization weight and the stopping stage. -/
theorem total_query_budget_le {C A L R p κ ε : ℝ}
    (hC : 0 ≤ C) (hA : 0 < A) (_hL : 0 < L) (hR : 0 < R)
    (hp : 2 ≤ p) (hκlo : 1 < κ) (_hκhi : κ ≤ 2)
    (hε : 0 < ε) (hsmall : ε ≤ L*R^(κ-1)) :
    (∑ n ∈ Finset.range (stageCount L R κ ε), (queryBudget C A L R p κ ε n : ℝ)) ≤
      queryConstant C A p κ * (L*R^(κ-1)/ε)^beta p κ := by
  let Λ := L*R^(κ-1)/ε
  let K := leadingScale A p κ
  let C' := C*(1+(2:ℝ)^(κ*beta p κ))+1
  have hΛ : 1 ≤ Λ := (le_div_iff₀ hε).2 (by simpa using hsmall)
  have hΛ0 : 0 ≤ Λ := by linarith
  have hK : 0 ≤ K := le_of_lt (leadingScale_pos hA hp hκlo)
  have hr0 : 0 ≤ ratio κ := le_of_lt (ratio_pos κ)
  have hb : 0 < beta p κ := beta_pos hp hκlo
  have hf : 0 ≤ (2:ℝ)^(κ*beta p κ) := Real.rpow_nonneg (by norm_num) _
  have hC' : 0 ≤ C' := by dsimp [C']; nlinarith [mul_nonneg hC hf]
  have hscale (n : ℕ) :
      stageScale L (initialWeight (A*R^(p-1)) (theta p) (ratio κ) ε) (tau p κ) R p κ n =
        K*Λ*ratio κ ^ n := by
    rw [balanced_stageScale hR, calibrated_first_stageScale hA hR (theta_lt_one hp)
      (ratio_lt_one hκlo) hε]
    rfl
  have hT (n : ℕ) :
      (queryBudget C A L R p κ ε n : ℝ) ≤ C'*(1+(K*Λ*ratio κ ^ n)^beta p κ) := by
    have hs0 : 0 ≤ stageScale L (initialWeight (A*R^(p-1)) (theta p) (ratio κ) ε)
        (tau p κ) R p κ n := by
      rw [hscale]
      exact mul_nonneg (mul_nonneg hK hΛ0) (pow_nonneg hr0 _)
    simpa only [queryBudget, hscale] using ceil_budget_le hC hf hs0 (b := beta p κ)
  have hS : stageCount L R κ ε = ⌈Real.logb 2 (2*Λ)/(κ-1)⌉₊ := by
    unfold stageCount
    rw [show 2*L*R^(κ-1)/ε = 2*Λ by dsimp [Λ]; ring]
  rw [hS]
  calc
    _ ≤ C' * (((1+1/(beta p κ*Real.log 2))/(κ-1)+1+
        K^beta p κ/(1-ratio κ^beta p κ))*Λ^beta p κ) :=
      logarithmic_budget_le_power hκlo hb hΛ hC' hK hr0 (ratio_lt_one hκlo) hT
    _ = queryConstant C A p κ * (L*R^(κ-1)/ε)^beta p κ := by
      dsimp [queryConstant, C', K, Λ]
      ring

noncomputable def gamma (p κ : ℝ) : ℝ :=
  κ*(p-1) / ((κ-1)*deltaDenom p κ)

/-- The exact difference in (7.7); the assumptions ensure its denominators are nonzero. -/
theorem gamma_sub_beta {p κ : ℝ} (hp : 2 ≤ p) (hκ : 1 < κ) :
    gamma p κ - beta p κ = (p-κ) / ((κ-1)*deltaDenom p κ) := by
  have hd : deltaDenom p κ ≠ 0 := ne_of_gt (deltaDenom_pos hp hκ)
  have hk : κ-1 ≠ 0 := ne_of_gt (sub_pos.mpr hκ)
  dsimp [gamma, beta]
  field_simp
  ring

theorem beta_le_gamma {p κ : ℝ} (hp : 2 ≤ p) (hκlo : 1 < κ) (hκhi : κ ≤ 2) :
    beta p κ ≤ gamma p κ := by
  have h := gamma_sub_beta hp hκlo
  have hnon : 0 ≤ (p-κ) / ((κ-1)*deltaDenom p κ) :=
    div_nonneg (by linarith) (le_of_lt (mul_pos (sub_pos.mpr hκlo) (deltaDenom_pos hp hκlo)))
  linarith

end P31.Schedule
