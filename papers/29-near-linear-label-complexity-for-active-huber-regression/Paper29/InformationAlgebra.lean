import Paper29.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-! Explicit Bernoulli KL calculation used by equation (4.9).
This file does not assume mutual-information or adaptive-transcript bounds. -/
noncomputable section
namespace Paper29.InformationAlgebra

def bernoulliKL (p q : ℝ) : ℝ :=
  p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))

lemma biased_bernoulli_kl (β : ℝ) (hβ : 0 ≤ β) (hβhi : β ≤ 1 / 4) :
    bernoulliKL (1 / 2 + β) (1 / 2 - β) =
      2 * β * Real.log ((1 + 2 * β) / (1 - 2 * β)) := by
  have hp : 0 < (1 / 2 : ℝ) + β := by linarith
  have hq : 0 < (1 / 2 : ℝ) - β := by linarith
  have hr : 0 < (1 + 2 * β) / (1 - 2 * β) := div_pos (by linarith) (by linarith)
  have hratio : ((1 / 2 : ℝ) + β) / (1 / 2 - β) =
      (1 + 2 * β) / (1 - 2 * β) := by
    apply (div_eq_div_iff (ne_of_gt hq) (by linarith : 1 - 2 * β ≠ 0)).2
    ring
  have hinv : ((1 / 2 : ℝ) - β) / (1 / 2 + β) =
      (((1 / 2 : ℝ) + β) / (1 / 2 - β))⁻¹ := by rw [inv_div]
  simp only [bernoulliKL]
  have hsub1 : (1 : ℝ) - (1 / 2 + β) = 1 / 2 - β := by ring
  have hsub2 : (1 : ℝ) - (1 / 2 - β) = 1 / 2 + β := by ring
  rw [hsub1, hsub2, hinv, Real.log_inv, hratio]
  ring

lemma biased_bernoulli_reverse_kl (β : ℝ) (hβ : 0 ≤ β) (hβhi : β ≤ 1 / 4) :
    bernoulliKL (1 / 2 - β) (1 / 2 + β) =
      bernoulliKL (1 / 2 + β) (1 / 2 - β) := by
  simp only [bernoulliKL]
  have hsub1 : (1 : ℝ) - (1 / 2 + β) = 1 / 2 - β := by ring
  have hsub2 : (1 : ℝ) - (1 / 2 - β) = 1 / 2 + β := by ring
  rw [hsub1, hsub2]
  ring

lemma biased_bernoulli_kl_bound (β : ℝ) (hβ : 0 ≤ β) (hβhi : β ≤ 1 / 4) :
    bernoulliKL (1 / 2 + β) (1 / 2 - β) ≤ 16 * β ^ 2 := by
  rw [biased_bernoulli_kl β hβ hβhi]
  have hd : 0 < 1 - 2 * β := by linarith
  have hn : 0 < 1 + 2 * β := by linarith
  have hl := Real.log_le_sub_one_of_pos (div_pos hn hd)
  have hfrac : (1 + 2 * β) / (1 - 2 * β) - 1 ≤ 8 * β := by
    have hrat : (1 + 2 * β) / (1 - 2 * β) ≤ 8 * β + 1 := by
      apply (div_le_iff₀ hd).2
      nlinarith [mul_nonneg hβ (show 0 ≤ 1 - 4 * β by linarith)]
    linarith
  have hlog : Real.log ((1 + 2 * β) / (1 - 2 * β)) ≤ 8 * β := hl.trans hfrac
  nlinarith [mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2 * β by positivity)]

end Paper29.InformationAlgebra
