/-
Copyright (c) 2026. Endpoint-complete scalar rare-event witness and
parameter implications for the random-matching lower bound.
-/
import Paper06.Witness
import Paper06.Divergence
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Nat.Choose.Cast

open Real Set BigOperators
open scoped Classical

namespace Paper06

/-- The elementary supporting-line inequality for `x ↦ x log x`. -/
theorem mul_log_div_ge_sub {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a - b ≤ a * Real.log (a / b) := by
  have h := Real.log_le_sub_one_of_pos (div_pos hb ha)
  have hlog : Real.log (b / a) = -Real.log (a / b) := by
    rw [Real.log_div (ne_of_gt hb) (ne_of_gt ha),
      Real.log_div (ne_of_gt ha) (ne_of_gt hb)]
    ring
  rw [hlog] at h
  have hmul := mul_le_mul_of_nonneg_left h (le_of_lt ha)
  have hcancel : a * (b / a - 1) = b - a := by
    field_simp
  rw [hcancel] at hmul
  nlinarith

/-- The charge `p log (p/(e q))` is increasing for `p ≥ q > 0`.
This proof uses the supporting-line inequality and covers the endpoint `p = 1`. -/
theorem bernoulli_charge_mono {p₀ p q : ℝ}
    (hq : 0 < q) (hqp₀ : q ≤ p₀) (hp₀p : p₀ ≤ p) :
    p₀ * log (p₀ / (Real.exp 1 * q)) ≤
      p * log (p / (Real.exp 1 * q)) := by
  have hp₀ : 0 < p₀ := lt_of_lt_of_le hq hqp₀
  have hp : 0 < p := lt_of_lt_of_le hp₀ hp₀p
  have hlog : 0 ≤ log (p₀ / q) := Real.log_nonneg ((le_div_iff₀ hq).2 (by linarith))
  have hline := mul_log_div_ge_sub hp hp₀
  have hprod := mul_nonneg (sub_nonneg.mpr hp₀p) hlog
  have hsplit : log (p / q) = log (p / p₀) + log (p₀ / q) := by
    rw [Real.log_div (ne_of_gt hp) (ne_of_gt hq),
      Real.log_div (ne_of_gt hp) (ne_of_gt hp₀),
      Real.log_div (ne_of_gt hp₀) (ne_of_gt hq)]
    ring
  have hcharge (x : ℝ) (hx : 0 < x) :
      log (x / (Real.exp 1 * q)) = log (x / q) - 1 := by
    rw [Real.log_div (ne_of_gt hx) (by positivity),
      Real.log_mul (by positivity) (ne_of_gt hq), Real.log_exp,
      Real.log_div (ne_of_gt hx) (ne_of_gt hq)]
    ring
  rw [hcharge p hp, hcharge p₀ hp₀, hsplit]
  nlinarith

/-- The Bernoulli charge estimate, including `p = 1`. -/
theorem dBer_ge_p_log_closed {p q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hqp : q ≤ p) (hp1 : p ≤ 1) :
    p * log (p / (Real.exp 1 * q)) ≤ dBer p q := by
  have hp : 0 < p := lt_of_lt_of_le hq hqp
  rcases eq_or_lt_of_le hp1 with rfl | hp1
  · have hlog : log (1 / (Real.exp 1 * q)) = log (1 / q) - 1 := by
      rw [Real.log_div (by norm_num) (by positivity),
        Real.log_mul (by positivity) (ne_of_gt hq), Real.log_exp,
        Real.log_div (by norm_num) (ne_of_gt hq)]
      ring
    simp only [dBer, one_ne_zero, ↓reduceIte, one_mul, hlog, add_zero]
    linarith
  · exact dBer_ge_p_log p q hq hq1 hqp hp1 hp

/-- Scalar event witness with upper and lower event-probability bounds.
Only the genuine separation `q₀ < p₀` is required; the logarithmic charge
may be negative, as in Proposition 3.4 itself. -/
theorem dBer_ge_event_charge {p q p₀ q₀ : ℝ}
    (hq : 0 < q) (hqq₀ : q ≤ q₀) (hq₀p₀ : q₀ < p₀)
    (hp₀p : p₀ ≤ p) (hp1 : p ≤ 1) :
    p₀ * log (p₀ / (Real.exp 1 * q₀)) ≤ dBer p q := by
  have hq₀ : 0 < q₀ := lt_of_lt_of_le hq hqq₀
  have hp₀ : 0 < p₀ := lt_trans hq₀ hq₀p₀
  have hp : 0 < p := lt_of_lt_of_le hp₀ hp₀p
  have hq1 : q < 1 := lt_of_le_of_lt hqq₀ (lt_of_lt_of_le hq₀p₀ (hp₀p.trans hp1))
  have hqp : q ≤ p := hqq₀.trans (le_of_lt hq₀p₀) |>.trans hp₀p
  have hlog : log (p / (Real.exp 1 * q₀)) ≤ log (p / (Real.exp 1 * q)) := by
    apply Real.log_le_log (by positivity)
    apply div_le_div_of_nonneg_left (le_of_lt hp) (by positivity)
    exact mul_le_mul_of_nonneg_left hqq₀ (by positivity)
  calc
    p₀ * log (p₀ / (Real.exp 1 * q₀)) ≤ p * log (p / (Real.exp 1 * q₀)) :=
      bernoulli_charge_mono hq₀ (le_of_lt hq₀p₀) hp₀p
    _ ≤ p * log (p / (Real.exp 1 * q)) :=
      mul_le_mul_of_nonneg_left hlog (le_of_lt hp)
    _ ≤ dBer p q := dBer_ge_p_log_closed hq hq1 hqp hp1

/-- Binary relative entropy with the source paper's absolute-continuity
convention, including the two singular endpoints. -/
noncomputable def dBerFull (p q : ℝ) : EReal :=
  if (q = 0 ∧ p ≠ 0) ∨ (q = 1 ∧ p ≠ 1) then ⊤ else (dBer p q : EReal)

/-- The event witness remains valid at `q = 0` and `p = 1`. -/
theorem dBerFull_ge_event_charge {p q p₀ q₀ : ℝ}
    (hq : 0 ≤ q) (hqq₀ : q ≤ q₀) (hq₀p₀ : q₀ < p₀)
    (hp₀p : p₀ ≤ p) (hp1 : p ≤ 1) :
    ((p₀ * log (p₀ / (Real.exp 1 * q₀)) : ℝ) : EReal) ≤ dBerFull p q := by
  have hp : 0 < p := lt_of_le_of_lt hq (hqq₀.trans_lt (hq₀p₀.trans_le hp₀p))
  by_cases hq0 : q = 0
  · simp [dBerFull, hq0, ne_of_gt hp]
  · have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
    have hq1 : q < 1 := lt_of_le_of_lt hqq₀ (hq₀p₀.trans_le (hp₀p.trans hp1))
    simp only [dBerFull, hq0, ne_of_lt hq1, false_and, or_self, ↓reduceIte]
    exact EReal.coe_le_coe (dBer_ge_event_charge hqpos hqq₀ hq₀p₀ hp₀p hp1)

/-- Cancellation of the candidate-pair count in the witness likelihood ratio. -/
theorem matching_charge_identity (n k : ℕ) (β : ℝ)
    (hn : 1 < n) (hk : 2 ≤ k) :
    (3 * ((k : ℝ) * (k - 1) / 2) / (4 * (n - 1))) *
        log ((3 * ((k : ℝ) * (k - 1) / 2) / (4 * (n - 1))) /
          (Real.exp 1 * (((k : ℝ) * (k - 1) / 2) * β))) =
      (3 * (k : ℝ) * (k - 1) / (8 * (n - 1))) *
        log (3 / (4 * Real.exp 1 * (n - 1) * β)) := by
  have hnpos : (0 : ℝ) < n - 1 := by
    have h : (1 : ℝ) < n := by exact_mod_cast hn
    linarith
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hk)
  have hk1 : (0 : ℝ) < k - 1 := by
    have h : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hc : 3 * ((k : ℝ) * (k - 1) / 2) / (4 * (n - 1)) =
      3 * (k : ℝ) * (k - 1) / (8 * (n - 1)) := by field_simp; ring
  rw [hc]
  congr 1
  by_cases hβ : β = 0
  · simp [hβ]
  · congr 1
    field_simp
    <;> ring

/-- Proposition 3.4's scalar assembly from its two event estimates.
The assumptions use `β < 3/(4(n-1))` exactly, without the stronger and
unnecessary restriction `β < 3/(4e(n-1))`. -/
theorem prop_3_4_scalar (n k : ℕ) (β p q : ℝ)
    (hn : 6 ≤ n) (hk2 : 2 ≤ k) (hk : k * k ≤ n)
    (hβ : 0 ≤ β) (hβ1 : β < 3 / (4 * ((n : ℝ) - 1)))
    (hq : 0 ≤ q) (hp1 : p ≤ 1)
    (hp : 3 * ((k : ℝ) * (k - 1) / 2) / (4 * (n - 1)) ≤ p)
    (hqbound : q ≤ ((k : ℝ) * (k - 1) / 2) * β) :
    (((3 * (k : ℝ) * (k - 1) / (8 * (n - 1))) *
      log (3 / (4 * Real.exp 1 * (n - 1) * β)) : ℝ) : EReal) ≤ dBerFull p q := by
  have hnpos : (0 : ℝ) < n - 1 := by
    have h : (6 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hk2)
  have hk1 : (0 : ℝ) < k - 1 := by
    have h : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    linarith
  have hm : (0 : ℝ) < (k : ℝ) * (k - 1) / 2 := by positivity
  have hsep : ((k : ℝ) * (k - 1) / 2) * β <
      3 * ((k : ℝ) * (k - 1) / 2) / (4 * (n - 1)) := by
    have h := mul_lt_mul_of_pos_left hβ1 hm
    convert h using 1 <;> ring
  rw [← matching_charge_identity n k β (by omega) hk2]
  exact dBerFull_ge_event_charge hq hqbound hsep hp hp1

/-- The complete real-power implication used in the proof of Theorem 3.1.
The separation in the parameter hypothesis supplies both applicability of
the matching witness and the desired logarithmic charge. -/
theorem thm_3_1_parameter_chain (n r : ℕ) (θ : ℝ)
    (hn : 6 ≤ n) (hr : 1 < r) (hθ : 0 < θ) (_hθ1 : θ < 1 / 2)
    (hparam : 2 * Real.exp 1 * ((n : ℝ) - 1) ≤ (r : ℝ) ^ ((1 : ℝ) / 2 - θ)) :
    (r : ℝ) ^ θ ≤ Real.sqrt r / (2 * Real.exp 1 * ((n : ℝ) - 1)) ∧
      1 < Real.sqrt r / (2 * Real.exp 1 * ((n : ℝ) - 1)) ∧
      θ * Real.log r ≤ Real.log (Real.sqrt r / (2 * Real.exp 1 * ((n : ℝ) - 1))) ∧
      3 / (2 * Real.sqrt r) < 3 / (4 * ((n : ℝ) - 1)) := by
  have hr1 : (1 : ℝ) < r := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < r := by linarith
  have hnpos : (0 : ℝ) < n - 1 := by
    have h : (6 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hden : (0 : ℝ) < 2 * Real.exp 1 * ((n : ℝ) - 1) := by positivity
  have hsqrt : Real.sqrt r = (r : ℝ) ^ ((1 : ℝ) / 2 - θ) * (r : ℝ) ^ θ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hrpos]
    congr 1
    ring
  have hmul := mul_le_mul_of_nonneg_right hparam (Real.rpow_nonneg (le_of_lt hrpos) θ)
  rw [← hsqrt] at hmul
  have hratio : (r : ℝ) ^ θ ≤ Real.sqrt r / (2 * Real.exp 1 * ((n : ℝ) - 1)) :=
    (le_div_iff₀ hden).2 (by nlinarith [hmul])
  have hrpow : (1 : ℝ) < (r : ℝ) ^ θ := Real.one_lt_rpow hr1 hθ
  have hratio1 := lt_of_lt_of_le hrpow hratio
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos hrpos θ) hratio
  rw [Real.log_rpow hrpos] at hlog
  have hroot : 2 * Real.exp 1 * ((n : ℝ) - 1) < Real.sqrt r :=
    (one_lt_div hden).1 hratio1
  have hroot2 : 2 * ((n : ℝ) - 1) < Real.sqrt r := by
    have he := exp_one_gt_one
    have hmul' := mul_pos (sub_pos.mpr he) hnpos
    nlinarith
  have hbeta : 3 / (2 * Real.sqrt r) < 3 / (4 * ((n : ℝ) - 1)) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  exact ⟨hratio, hratio1, hlog, hbeta⟩

/-- Substituting the elementary game bound into the likelihood ratio. -/
theorem thm_3_1_log_ratio_identity (n r : ℕ) (hn : 1 < n) (hr : 0 < r) :
    Real.log (3 / (4 * Real.exp 1 * ((n : ℝ) - 1) *
      (3 / (2 * Real.sqrt r)))) =
      Real.log (Real.sqrt r / (2 * Real.exp 1 * ((n : ℝ) - 1))) := by
  have hnpos : (0 : ℝ) < n - 1 := by
    have h : (1 : ℝ) < n := by exact_mod_cast hn
    linarith
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hsqrt : 0 < Real.sqrt r := Real.sqrt_pos.mpr hrpos
  congr 1
  field_simp
  ring

/-- Theorem 3.1's first lower bound after the event estimates have been
proved for the constructed law. No support assumptions are needed. -/
theorem thm_3_1_scalar (n k r : ℕ) (θ p q : ℝ)
    (hn : 6 ≤ n) (hk2 : 2 ≤ k) (hk : k * k ≤ n)
    (hr : 1 < r) (hθ : 0 < θ) (hθ1 : θ < 1 / 2)
    (hparam : 2 * Real.exp 1 * ((n : ℝ) - 1) ≤ (r : ℝ) ^ ((1 : ℝ) / 2 - θ))
    (hq : 0 ≤ q) (hp1 : p ≤ 1)
    (hp : 3 * ((k : ℝ) * (k - 1) / 2) / (4 * (n - 1)) ≤ p)
    (hqbound : q ≤ ((k : ℝ) * (k - 1) / 2) * (3 / (2 * Real.sqrt r))) :
    (((3 * θ * (k : ℝ) * (k - 1) * log ((r : ℝ) ^ 2)) /
      (16 * (n - 1)) : ℝ) : EReal) ≤ dBerFull p q := by
  obtain ⟨_, _, hlog, hbeta⟩ := thm_3_1_parameter_chain n r θ hn hr hθ hθ1 hparam
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (lt_trans (by norm_num) hr)
  have hsqrt : 0 < Real.sqrt r := Real.sqrt_pos.mpr hrpos
  have hnpos : (0 : ℝ) < n - 1 := by
    have h : (6 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hk1 : (0 : ℝ) ≤ k - 1 := by
    have h : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    linarith
  have hc : (0 : ℝ) ≤ 3 * (k : ℝ) * (k - 1) / (8 * (n - 1)) := by positivity
  have hbound := prop_3_4_scalar n k (3 / (2 * Real.sqrt r)) p q hn hk2 hk
    (by positivity) hbeta hq hp1 hp hqbound
  rw [thm_3_1_log_ratio_identity n r (by omega) (by omega)] at hbound
  have hmain : (3 * θ * (k : ℝ) * (k - 1) * log ((r : ℝ) ^ 2)) /
      (16 * (n - 1)) =
      (3 * (k : ℝ) * (k - 1) / (8 * (n - 1))) * (θ * log r) := by
    rw [Real.log_pow]
    field_simp
    ring
  rw [hmain]
  exact (EReal.coe_le_coe (mul_le_mul_of_nonneg_left hlog hc)).trans hbound

/-- The number of disjoint unordered pairs of candidate edges, as a real
polynomial. This identity also covers `k < 4`. -/
theorem cast_choose_four (k : ℕ) :
    (k.choose 4 : ℝ) = (k : ℝ) * (k - 1) * (k - 2) * (k - 3) / 24 := by
  rw [Nat.cast_choose_eq_descPochhammer_div ℝ]
  norm_num [descPochhammer_succ_eval, Nat.factorial]

/-- The two-term matching inclusion-exclusion estimate implies the exact
`3/4` lower bound used in Proposition 3.4. -/
theorem matching_inclusion_exclusion_bound (n k : ℕ)
    (hn : 6 ≤ n) (hk2 : 2 ≤ k) (hk : k * k ≤ n) :
    3 * ((k : ℝ) * (k - 1) / 2) / (4 * (n - 1)) ≤
      ((k : ℝ) * (k - 1) / 2) / (n - 1) -
        3 * (k.choose 4 : ℝ) / ((n - 1) * (n - 3)) := by
  have hn3 : (0 : ℝ) < n - 3 := by
    have h : (6 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hn1 : (0 : ℝ) < n - 1 := by linarith
  have hk2' : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hkn : (k : ℝ) * k ≤ n := by exact_mod_cast hk
  have hdiff : ((k : ℝ) - 2) * (k - 3) ≤ (n : ℝ) - 3 := by nlinarith
  have hk1 : (0 : ℝ) ≤ k - 1 := by linarith
  have hm : (0 : ℝ) ≤ (k : ℝ) * (k - 1) := by positivity
  have hfactor :
      ((k : ℝ) * (k - 1) / 2) / (n - 1) -
        3 * (k.choose 4 : ℝ) / ((n - 1) * (n - 3)) =
      (((k : ℝ) * (k - 1) / 2) / (n - 1)) *
        (1 - (((k : ℝ) - 2) * (k - 3)) / (4 * (n - 3))) := by
    rw [cast_choose_four]
    field_simp
    ring
  rw [hfactor]
  have hquarter : (((k : ℝ) - 2) * (k - 3)) / (4 * ((n : ℝ) - 3)) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hcoef : (0 : ℝ) ≤ ((k : ℝ) * (k - 1) / 2) / (n - 1) := by positivity
  have hmul := mul_le_mul_of_nonneg_left (show (3 : ℝ) / 4 ≤
    1 - (((k : ℝ) - 2) * (k - 3)) / (4 * (n - 3)) by linarith) hcoef
  convert hmul using 1 <;> field_simp <;> ring

namespace FinProb

variable {α : Type*} [Fintype α]


/-- First two inclusion-exclusion terms in factorial-moment form. -/
theorem positive_event_ge_factorial_moments (p : FinProb α) (J : α → ℕ) :
    (∑ x, p.w x * (J x : ℝ)) -
      (∑ x, p.w x * ((J x : ℝ) * ((J x : ℝ) - 1))) / 2 ≤
      (map p (fun x => decide (0 < J x))).w true := by
  have hpoint (j : ℕ) : (j : ℝ) - (j : ℝ) * ((j : ℝ) - 1) / 2 ≤
      if 0 < j then 1 else 0 := by
    by_cases hj0 : j = 0
    · simp [hj0]
    by_cases hj1 : j = 1
    · simp [hj1]
    have hj2 : 2 ≤ j := by omega
    have hj2' : (2 : ℝ) ≤ j := by exact_mod_cast hj2
    have hmul := mul_nonneg (show (0 : ℝ) ≤ j - 1 by linarith)
      (show (0 : ℝ) ≤ j - 2 by linarith)
    simp only [show 0 < j by omega, ↓reduceIte]
    nlinarith
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hpoint (J x)) (p.nonneg x))
  have he (x : α) : p.w x * (if 0 < J x then (1 : ℝ) else 0) =
      (if decide (0 < J x) = true then p.w x else 0) := by
    by_cases h : 0 < J x <;> simp [h]
  have hterm (x : α) :
      p.w x * ((J x : ℝ) - (J x : ℝ) * ((J x : ℝ) - 1) / 2) =
        p.w x * (J x : ℝ) - p.w x * ((J x : ℝ) * ((J x : ℝ) - 1)) / 2 := by ring
  simp only [hterm, Finset.sum_sub_distrib, he] at hs
  rw [← Finset.sum_div] at hs
  simpa only [map_w, decide_eq_true_eq] using hs

/-- Once the actual matching first and second factorial moments have been
computed, this gives (15), including the cases `k = 2` and `k = 3`. -/
theorem matching_event_ge_of_factorial_moments (p : FinProb α) (J : α → ℕ)
    (n k : ℕ) (hn : 6 ≤ n) (hk2 : 2 ≤ k) (hk : k * k ≤ n)
    (hmean : (∑ x, p.w x * (J x : ℝ)) = (k.choose 2 : ℝ) / ((n : ℝ) - 1))
    (hsecond : (∑ x, p.w x * ((J x : ℝ) * ((J x : ℝ) - 1))) =
      6 * (k.choose 4 : ℝ) / (((n : ℝ) - 1) * (n - 3))) :
    3 * ((k : ℝ) * (k - 1) / 2) / (4 * (n - 1)) ≤
      (map p (fun x => decide (0 < J x))).w true := by
  have hm := positive_event_ge_factorial_moments p J
  rw [hmean, hsecond, Nat.cast_choose_two] at hm
  have he : (6 * (k.choose 4 : ℝ) / (((n : ℝ) - 1) * (n - 3))) / 2 =
      3 * (k.choose 4 : ℝ) / (((n : ℝ) - 1) * (n - 3)) := by ring
  rw [he] at hm
  exact (matching_inclusion_exclusion_bound n k hn hk2 hk).trans hm

/-- The two masses of a Bernoulli law sum to one. -/
theorem bool_w_false (p : FinProb Bool) : p.w false = 1 - p.w true := by
  have h := p.sum_eq_one
  simp only [Fintype.sum_bool] at h
  linarith

/-- A coordinate of a finite probability law is at most one. -/
theorem w_le_one (p : FinProb α) (x : α) : p.w x ≤ 1 := by
  rw [← p.sum_eq_one]
  exact Finset.single_le_sum (fun y _ => p.nonneg y) (Finset.mem_univ x)

/-- `dBer` is the usual finite real expression for the entropy of Bool laws. -/
theorem klPos_bool_eq (p q : FinProb Bool) :
    klPos p q = dBer (p.w true) (q.w true) := by
  have hp := bool_w_false p
  have hq := bool_w_false q
  simp only [klPos, Fintype.sum_bool, hp, hq, dBer]
  split_ifs <;> simp_all <;> ring

/-- Absolute continuity for Bool laws, stated in terms of the event mass. -/
theorem supports_bool_iff (p q : FinProb Bool) :
    Supports p q ↔ (q.w true = 0 → p.w true = 0) ∧
      (q.w true = 1 → p.w true = 1) := by
  constructor
  · intro hs
    refine ⟨hs true, ?_⟩
    intro hq
    have h := hs false (by rw [bool_w_false q, hq]; ring)
    rw [bool_w_false p] at h
    linarith
  · rintro ⟨ht, hf⟩ b hb
    cases b
    · have hq : q.w true = 1 := by rw [bool_w_false q] at hb; linarith
      rw [bool_w_false p, hf hq]
      ring
    · exact ht hb

/-- Robust entropy of Bernoulli laws, including all four boundary masses. -/
theorem kl_bool_eq (p q : FinProb Bool) :
    kl p q = dBerFull (p.w true) (q.w true) := by
  have hb : ¬ Supports p q ↔
      (q.w true = 0 ∧ p.w true ≠ 0) ∨
        (q.w true = 1 ∧ p.w true ≠ 1) := by
    rw [supports_bool_iff]
    tauto
  by_cases hs : Supports p q
  · rw [kl_of_support hs, dBerFull, if_neg (by intro h; exact (hb.mpr h) hs),
      klPos_bool_eq]
  · rw [kl_of_not_support hs, dBerFull, if_pos (hb.mp hs)]

/-- Binary data processing for an arbitrary event, with no support premise. -/
theorem dBerFull_event_le_kl (p q : FinProb α) (event : α → Bool) :
    dBerFull ((map p event).w true) ((map q event).w true) ≤ kl p q := by
  rw [← kl_bool_eq]
  exact kl_map_le p q event

/-- A fully supported or singular reference law obeys the same rare-event
relative-entropy witness. This is the event-level analytic implication in
Proposition 3.4. -/
theorem kl_ge_event_charge (p q : FinProb α) (event : α → Bool)
    (p₀ q₀ : ℝ) (hq₀p₀ : q₀ < p₀)
    (hp : p₀ ≤ (map p event).w true) (hq : (map q event).w true ≤ q₀) :
    ((p₀ * log (p₀ / (Real.exp 1 * q₀)) : ℝ) : EReal) ≤ kl p q := by
  exact (dBerFull_ge_event_charge ((map q event).nonneg true) hq hq₀p₀ hp
    (w_le_one (map p event) true)).trans (dBerFull_event_le_kl p q event)

/-- Proposition 3.4's quantitative bound for any pair of laws obeying the
matching lower estimate and feasible-product upper estimate on one event. -/
theorem kl_ge_matching_event (p q : FinProb α) (event : α → Bool)
    (n k : ℕ) (β : ℝ) (hn : 6 ≤ n) (hk2 : 2 ≤ k) (hk : k * k ≤ n)
    (hβ : 0 ≤ β) (hβ1 : β < 3 / (4 * ((n : ℝ) - 1)))
    (hp : 3 * ((k : ℝ) * (k - 1) / 2) / (4 * (n - 1)) ≤ (map p event).w true)
    (hq : (map q event).w true ≤ ((k : ℝ) * (k - 1) / 2) * β) :
    (((3 * (k : ℝ) * (k - 1) / (8 * (n - 1))) *
      log (3 / (4 * Real.exp 1 * (n - 1) * β)) : ℝ) : EReal) ≤ kl p q := by
  exact (prop_3_4_scalar n k β _ _ hn hk2 hk hβ hβ1
    ((map q event).nonneg true) (w_le_one (map p event) true) hp hq).trans
      (dBerFull_event_le_kl p q event)

/-- The first bound of Theorem 3.1 from the matching and incidence event
estimates and its original field-size parameter hypothesis. -/
theorem kl_ge_logarithmic_event (p q : FinProb α) (event : α → Bool)
    (n k r : ℕ) (θ : ℝ) (hn : 6 ≤ n) (hk2 : 2 ≤ k) (hk : k * k ≤ n)
    (hr : 1 < r) (hθ : 0 < θ) (hθ1 : θ < 1 / 2)
    (hparam : 2 * Real.exp 1 * ((n : ℝ) - 1) ≤ (r : ℝ) ^ ((1 : ℝ) / 2 - θ))
    (hp : 3 * ((k : ℝ) * (k - 1) / 2) / (4 * (n - 1)) ≤ (map p event).w true)
    (hq : (map q event).w true ≤ ((k : ℝ) * (k - 1) / 2) * (3 / (2 * Real.sqrt r))) :
    (((3 * θ * (k : ℝ) * (k - 1) * log ((r : ℝ) ^ 2)) /
      (16 * (n - 1)) : ℝ) : EReal) ≤ kl p q := by
  exact (thm_3_1_scalar n k r θ _ _ hn hk2 hk hr hθ hθ1 hparam
    ((map q event).nonneg true) (w_le_one (map p event) true) hp hq).trans
      (dBerFull_event_le_kl p q event)

end FinProb

end Paper06
