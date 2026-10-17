import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

/-!
# Continuous factor models: core definitions and elementary estimates

Section 1–2 of the paper.  All definitions and inequalities in this file are
completely proved (no `sorry`, no extra axioms).
-/

noncomputable section

open scoped Real BigOperators

namespace Paper08

/-! ## Square-root and dyadic constants -/

lemma two_rpow_neg_half_eq_inv_sqrt :
    (2:ℝ) ^ (-(1:ℝ) / 2) = 1 / Real.sqrt 2 := by
  have h1 : (0:ℝ) ≤ 2 := by norm_num
  have hexp : (-(1:ℝ) / 2) = -((1:ℝ) / 2) := by ring
  rw [hexp, Real.rpow_neg h1]
  have h2 : (2:ℝ) ^ ((1:ℝ) / 2) = Real.sqrt 2 := (Real.sqrt_eq_rpow 2).symm
  rw [h2]
  field_simp

lemma sqrt_two_gt_one : (1:ℝ) < Real.sqrt 2 := by
  have h : Real.sqrt 2 = (2:ℝ) ^ ((1:ℝ) / 2) := Real.sqrt_eq_rpow 2
  rw [h]
  exact Real.one_lt_rpow (by norm_num) (by norm_num)

lemma two_rpow_neg_half_lt_one : (2:ℝ) ^ (-(1:ℝ) / 2) < 1 := by
  rw [two_rpow_neg_half_eq_inv_sqrt]
  have h : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rw [div_lt_one h]
  exact sqrt_two_gt_one

lemma one_sub_two_rpow_neg_half_pos :
    0 < (1:ℝ) - (2:ℝ) ^ (-(1:ℝ) / 2) := by
  have := two_rpow_neg_half_lt_one
  linarith

/-- `C₀ = (1 - 2^{-1/2})^{-1}` of Lemma 3.1. -/
def C0 : ℝ := (1 - (2:ℝ) ^ (-(1:ℝ) / 2))⁻¹

lemma C0_pos : 0 < C0 := by
  unfold C0
  exact inv_pos.mpr one_sub_two_rpow_neg_half_pos

lemma C0_lt_four : C0 < 4 := by
  unfold C0
  have hden : (0:ℝ) < 1 - (2:ℝ) ^ (-(1:ℝ) / 2) := one_sub_two_rpow_neg_half_pos
  rw [inv_lt_iff_one_lt_mul₀ hden]
  rw [two_rpow_neg_half_eq_inv_sqrt]
  have hs : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hne : (Real.sqrt 2:ℝ) ≠ 0 := ne_of_gt hs
  have hlt : Real.sqrt 2 < 4 := by
    rw [Real.sqrt_lt (by norm_num : (0:ℝ) ≤ 2) (by norm_num : (0:ℝ) ≤ 4)]
    norm_num
  field_simp
  have hsq : (Real.sqrt 2:ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg 2, hsq, hlt]

/-- `α ≤ 2^α` for every natural number (used in (3.9)). -/
lemma nat_le_two_pow (α : ℕ) : (α:ℝ) ≤ (2:ℝ) ^ α := by
  induction α with
  | zero => norm_num
  | succ k ih =>
    have hp : ((k + 1 : ℕ) : ℝ) = (k:ℝ) + 1 := by norm_cast
    have htwo : (2:ℝ) ^ (k + 1 : ℕ) = (2:ℝ) ^ k * 2 := pow_succ _ _
    rw [hp, htwo]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; norm_num
    · have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
      nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 2) k]

/-! ## Logarithm bounds -/

/-- Tangent-line bound from the right: `log a - log b ≤ (a - b)/b` for `a,b > 0`. -/
lemma log_sub_log_le_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.log a - Real.log b ≤ (a - b) / b := by
  have h : Real.log (a / b) ≤ a / b - 1 :=
    Real.log_le_sub_one_of_pos (div_pos ha hb)
  have hdiv : Real.log (a / b) = Real.log a - Real.log b :=
    Real.log_div ha.ne' hb.ne'
  have hrew : a / b - 1 = (a - b) / b := by field_simp
  linarith

/-- `|log a - log b| ≤ |a - b|` whenever `a, b ≥ 1`. -/
lemma log_abs_sub_le_abs_sub {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| := by
  have hap : 0 < a := by linarith
  have hbp : 0 < b := by linarith
  have hab : |a - b| = |b - a| := abs_sub_comm a b
  rcases le_total a b with hle | hle
  · -- a ≤ b
    have hlog : Real.log a ≤ Real.log b := by
      rw [Real.log_le_log_iff hap hbp]; exact hle
    have hnonpos : Real.log a - Real.log b ≤ 0 := by linarith
    have habsab : |a - b| = b - a := by
      rw [abs_of_nonpos (by linarith : a - b ≤ 0)]
      ring
    rw [abs_of_nonpos hnonpos, habsab]
    have := log_sub_log_le_div hbp hap
    -- this : log b - log a ≤ (b - a)/a
    have hdiv : (b - a) / a ≤ b - a := by
      rw [div_le_iff₀ hap]
      nlinarith
    linarith
  · -- b ≤ a
    have hlog : Real.log b ≤ Real.log a := by
      rw [Real.log_le_log_iff hbp hap]; exact hle
    have hnonneg : (0:ℝ) ≤ Real.log a - Real.log b := by linarith
    have habsab : |a - b| = a - b := by
      exact abs_of_nonneg (by linarith : 0 ≤ a - b)
    rw [abs_of_nonneg hnonneg, habsab]
    have := log_sub_log_le_div hap hbp
    -- this : log a - log b ≤ (a - b)/b
    have hdiv : (a - b) / b ≤ a - b := by
      rw [div_le_iff₀ hbp]
      nlinarith
    linarith

/-- `0 ≤ Real.log y ≤ 1` for `y ∈ [1,2]`. -/
lemma log_nonneg_le_one {y : ℝ} (hy1 : 1 ≤ y) (hy2 : y ≤ 2) :
    0 ≤ Real.log y ∧ Real.log y ≤ 1 := by
  refine ⟨Real.log_nonneg hy1, ?_⟩
  have hlt : Real.log 2 < Real.log (Real.exp 1) := by
    rw [Real.log_lt_log_iff (by norm_num) (Real.exp_pos 1)]
    exact lt_trans (by norm_num : (2:ℝ) < 2.7182818283) Real.exp_one_gt_d9
  have he : Real.log (Real.exp 1) = 1 := Real.log_exp 1
  have hlog2 : Real.log 2 < 1 := by linarith
  have hmono : Real.log y ≤ Real.log 2 := by
    rw [Real.log_le_log_iff (by linarith : (0:ℝ) < y) (by norm_num : (0:ℝ) < 2)]
    exact hy2
  linarith

/-- Product of powers: `∏_{a∈s} C^a = C^{∑ a}` for `C > 0`. -/
lemma prod_rpow_eq {αs : Finset ℕ} {C : ℝ} (hC : 0 < C) :
    (∏ a ∈ αs, C ^ ((a:ℝ))) = C ^ (∑ a ∈ αs, ((a:ℝ) : ℝ)) :=
  (Real.rpow_sum_of_pos (a := C) hC (fun n : ℕ => ((n:ℝ) : ℝ)) αs).symm

/-- (3.9): if `C ≥ 1` and `∑ a ≤ s` then `∏_{a∈s} C^a ≤ C^s`. -/
lemma prod_rpow_le_rpow_of_sum_le {αs : Finset ℕ} {C s : ℝ}
    (hC : 1 ≤ C)
    (hsum : (∑ a ∈ αs, ((a:ℝ) : ℝ)) ≤ s) :
    (∏ a ∈ αs, C ^ ((a:ℝ))) ≤ C ^ s := by
  have hpos : 0 < C := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) hC
  rw [prod_rpow_eq hpos]
  exact Real.rpow_le_rpow_of_exponent_le hC hsum

end Paper08
