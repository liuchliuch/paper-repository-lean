import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs

/-! Exact rates (2.11) and the elementary `N⁻¹ ≤ r_d(N)` used in Section 7. -/
noncomputable section
namespace Paper38.Model

/-- The regularized sharp Gaussian empirical-measure rates as printed in (2.11). -/
def rate (d N : ℕ) : ℝ :=
  if d = 1 then (N : ℝ)⁻¹ * (1 + Real.log (Real.log (Real.exp (Real.exp 1) + N)))
  else if d = 2 then (N : ℝ)⁻¹ * (1 + Real.log N) ^ 2
  else (N : ℝ) ^ (-(2 : ℝ) / d)

/-- The double logarithm is finite and at least one even for the smallest
sample sizes; no asymptotic replacement has been made. -/
lemma regularized_loglog_ge_one (N : ℕ) :
    1 ≤ Real.log (Real.log (Real.exp (Real.exp 1) + N)) := by
  have hbase : Real.exp (Real.exp 1) ≤ Real.exp (Real.exp 1) + N := le_add_of_nonneg_right (Nat.cast_nonneg N)
  have hlog : Real.exp 1 ≤ Real.log (Real.exp (Real.exp 1) + N) := by
    calc
      Real.exp 1 = Real.log (Real.exp (Real.exp 1)) := (Real.log_exp _).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) hbase
  calc
    1 = Real.log (Real.exp 1) := (Real.log_exp _).symm
    _ ≤ _ := Real.log_le_log (Real.exp_pos _) hlog

/-- The exact rates dominate the sample-mean rate in every source dimension. -/
theorem inv_sampleSize_le_rate (d N : ℕ) (hd : 1 ≤ d) (hN : 1 ≤ N) :
    (N : ℝ)⁻¹ ≤ rate d N := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hNr
  unfold rate
  split_ifs with hd1 hd2
  · have h := regularized_loglog_ge_one N
    nlinarith [inv_pos.mpr hNpos]
  · have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNr
    have hsq : (1 : ℝ) ≤ (1 + Real.log (N : ℝ)) ^ 2 := by nlinarith
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hsq (inv_nonneg.mpr hNpos.le)
  · have hdr : (2 : ℝ) ≤ d := by
      have : 2 ≤ d := Nat.succ_le_of_lt (lt_of_le_of_ne hd (Ne.symm hd1))
      exact_mod_cast this
    have hexp : (-1 : ℝ) ≤ -(2 : ℝ) / d := by
      apply (le_div_iff₀ (lt_of_lt_of_le (by norm_num) hdr)).mpr
      linarith
    simpa only [Real.rpow_neg_one] using Real.rpow_le_rpow_of_exponent_le hNr hexp

theorem rate_pos (d N : ℕ) (hd : 1 ≤ d) (hN : 1 ≤ N) : 0 < rate d N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  exact (inv_pos.mpr hNr).trans_le (inv_sampleSize_le_rate d N hd hN)

end Paper38.Model
