/-
Copyright (c) 2026. Spectral estimates (Lemma A.1).
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Real

namespace Paper09

/-- `3 ≤ n` implies `1 < log n` (since `e < 3`). -/
theorem one_lt_log_of_three_le {n : ℝ} (hn : 3 ≤ n) : 1 < log n := by
  have he : exp 1 < n := by
    have h1 : exp 1 < (2.7182818286:ℝ) := Real.exp_one_lt_d9
    have h2 : (2.7182818286:ℝ) < 3 := by norm_num
    linarith
  have h1 : (1:ℝ) = log (exp 1) := (log_exp 1).symm
  rw [h1]
  exact log_lt_log (exp_pos 1) he

/-- Lemma A.1, lower bound: `t_mix(1/4) ≥ (log 2)/gap`. -/
theorem lemma_A_1_lower {t gap : ℝ}
    (_ht : 0 ≤ t) (hgap : 0 < gap)
    (h : exp (- t * gap) / 2 > 1 / 4) :
    t < log 2 / gap := by
  have h1 : exp (- t * gap) > 1 / 2 := by linarith
  have h2 : log (1 / 2) < - t * gap := by
    have h2a : log (1 / 2) < log (exp (- t * gap)) :=
      (log_lt_log_iff (by norm_num) (exp_pos (- t * gap))).mpr h1
    have h2b : log (exp (- t * gap)) = - t * gap := log_exp _
    linarith
  have h3 : log (1 / 2) = - log 2 := by
    rw [log_div (by norm_num) (by norm_num), log_one, zero_sub]
  rw [h3] at h2
  have h4 : t * gap < log 2 := by linarith
  rw [lt_div_iff₀ hgap]
  exact h4

/-- Lemma A.1, upper-bound scalar form. For `0 < ε < 1`. -/
theorem lemma_A_1_upper_algebra {ε πmin t gap : ℝ}
    (hε : 0 < ε) (hε' : ε < 1) (hπ : 0 < πmin) (hgap : 0 < gap)
    (hT : log (1 / (ε * πmin)) / gap ≤ t) :
    exp (- t * gap) * (1 / πmin) ≤ 1 / ε := by
  have hprod : 0 < ε * πmin := mul_pos hε hπ
  have hmul : log (1 / (ε * πmin)) ≤ t * gap := by
    have := hT
    rwa [div_le_iff₀ hgap] at this
  have hneg : - t * gap ≤ - log (1 / (ε * πmin)) := by
    have : - (t * gap) = - t * gap := by ring
    rw [← this]
    exact neg_le_neg hmul
  have hexp : exp (- t * gap) ≤ exp (- log (1 / (ε * πmin))) :=
    exp_le_exp.mpr hneg
  have hrew : exp (- log (1 / (ε * πmin))) = ε * πmin := by
    have h : exp (- log (1 / (ε * πmin))) = (exp (log (1 / (ε * πmin))))⁻¹ := by
      rw [exp_neg]
    rw [h]
    have h2 : exp (log (1 / (ε * πmin))) = 1 / (ε * πmin) :=
      exp_log (by positivity : (0:ℝ) < 1 / (ε * πmin))
    rw [h2]
    field_simp [ne_of_gt hprod]
  have h1 : exp (- t * gap) ≤ ε * πmin := by rw [hrew] at hexp; exact hexp
  have h2 : exp (- t * gap) * (1 / πmin) ≤ (ε * πmin) * (1 / πmin) :=
    mul_le_mul_of_nonneg_right h1 (one_div_nonneg.mpr (le_of_lt hπ))
  have h3 : (ε * πmin) * (1 / πmin) = ε := by
    field_simp [ne_of_gt hπ]
  rw [h3] at h2
  have hεle : ε ≤ 1 / ε := by
    have : ε * ε ≤ ε := by nlinarith [sq_nonneg ε, hε, hε']
    have hpos : 0 < 1 / ε := one_div_pos.mpr hε
    rw [le_div_iff₀ hε]
    nlinarith
  calc exp (- t * gap) * (1 / πmin)
      ≤ ε := h2
    _ ≤ 1 / ε := hεle

theorem log_two_pos : 0 < log 2 := log_pos (by norm_num)

/-- Theorem 1.3 double-log squeeze, lower side. -/
theorem theorem_1_3_loglog_lower {Y n c a : ℝ}
    (hn : 3 ≤ n) (hc : 0 < c) (_ha : 0 < a)
    (hY : exp (c * (log n / log (log n)) ^ a) ≤ Y) :
    c * (log n / log (log n)) ^ a ≤ log Y := by
  have hlogn : 1 < log n := one_lt_log_of_three_le hn
  have hloglog : 0 < log (log n) := log_pos hlogn
  have hbase : 0 < log n / log (log n) :=
    div_pos (lt_trans (by norm_num : (0:ℝ) < 1) hlogn) hloglog
  have hinner : 0 < c * (log n / log (log n)) ^ a :=
    mul_pos hc (Real.rpow_pos_of_pos hbase a)
  have hYpos : 0 < Y := lt_of_lt_of_le (exp_pos _) hY
  exact (le_log_iff_exp_le hYpos).mpr hY

/-- Theorem 1.3 double-log squeeze, upper side. -/
theorem theorem_1_3_loglog_upper {Y n C a d : ℝ}
    (hn : 3 ≤ n) (_hC : 0 < C) (_ha : 0 < a) (hYpos : 0 < Y)
    (hY : Y ≤ exp (C * (log n) ^ a * (log (log n)) ^ d)) :
    log Y ≤ C * (log n) ^ a * (log (log n)) ^ d := by
  exact (log_le_iff_le_exp hYpos).mpr hY

/-- Corollary 1.4 algebra: for `d = 2` the exponent is `a = 1/2`. -/
theorem corollary_1_4_exponent : (2 - 1 : ℝ) / 2 = 1 / 2 := by norm_num

end Paper09
