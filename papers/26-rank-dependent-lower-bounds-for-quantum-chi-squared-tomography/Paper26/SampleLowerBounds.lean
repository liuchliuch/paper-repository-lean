import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The local algebra in Section 3.3.  The preceding geometric and posterior
theorems must supply the success inequalities.  This module proves their four
sample consequences, with one universal small-accuracy threshold; it does not
define a learner by assuming a lower bound on its own success probability. -/
noncomputable section

namespace Paper26.SampleLowerBounds

/-- The constant term uses at most one third of the success requirement. -/
theorem samples_of_success {C k m n S : ℝ}
    (hC : 0 < C) (hk : 0 < k) (hm : 0 < m)
    (hsmall : C * k ≤ 1 / 3) (hS : 2 / 3 ≤ S)
    (hbound : S ≤ C * k * (1 + n / m)) :
    m / (3 * C * k) ≤ n := by
  have hsignal : 1 / 3 ≤ C * k * (n / m) := by nlinarith
  apply (div_le_iff₀ (by positivity : 0 < 3 * C * k)).2
  have hmultiply := (le_div_iff₀ hm).1
    (show 1 / 3 ≤ C * k * n / m by simpa only [mul_div_assoc] using hsignal)
  nlinarith

theorem sqrt_ratio_le_one {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) :
    Real.sqrt (r / s) ≤ 1 := by
  have hs : 0 < s := hr.trans_le hrs
  exact (Real.sqrt_le_one).2 ((div_le_one hs).2 hrs)

/-- A concrete universal threshold works for both accuracy exponents. -/
def accuracyThreshold (C : ℝ) : ℝ := min 1 (1 / (3 * C))

theorem accuracyThreshold_pos {C : ℝ} (hC : 0 < C) :
    0 < accuracyThreshold C := lt_min (by norm_num) (by positivity)

theorem bures_small {C r s ε : ℝ} (hC : 0 < C) (hr : 0 < r)
    (hrs : r ≤ s) (hε : 0 < ε) (hsmall : ε ≤ accuracyThreshold C) :
    C * (ε * Real.sqrt (r / s)) ≤ 1 / 3 := by
  have hεC : ε ≤ 1 / (3 * C) := hsmall.trans (min_le_right _ _)
  have hmul := (le_div_iff₀ (by positivity : 0 < 3 * C)).1 hεC
  have hsqrt := sqrt_ratio_le_one hr hrs
  have := mul_le_mul_of_nonneg_left hsqrt (by positivity : 0 ≤ C * ε)
  nlinarith

theorem right_small {C r s ε : ℝ} (hC : 0 < C) (hr : 0 < r)
    (hrs : r ≤ s) (hε : 0 < ε) (hsmall : ε ≤ accuracyThreshold C) :
    C * (r * ε ^ 2 / s) ≤ 1 / 3 := by
  have hs : 0 < s := hr.trans_le hrs
  have hε1 : ε ≤ 1 := hsmall.trans (min_le_left _ _)
  have hεC : ε ≤ 1 / (3 * C) := hsmall.trans (min_le_right _ _)
  have hmul := (le_div_iff₀ (by positivity : 0 < 3 * C)).1 hεC
  have hrats : r / s ≤ 1 := (div_le_one hs).2 hrs
  have hratio := mul_le_mul_of_nonneg_right hrats (sq_nonneg ε)
  have heps : ε ^ 2 ≤ ε := by nlinarith
  have hterm : r * ε ^ 2 / s ≤ ε := by
    calc
      r * ε ^ 2 / s = r / s * ε ^ 2 := by ring
      _ ≤ ε ^ 2 := by simpa only [one_mul] using hratio
      _ ≤ ε := heps
  nlinarith

theorem bures_collective {C r s ε n S : ℝ} (hC : 0 < C) (hr : 0 < r)
    (hrs : r ≤ s) (hε : 0 < ε) (hsmall : ε ≤ accuracyThreshold C)
    (hS : 2 / 3 ≤ S)
    (hbound : S ≤ C * ε * Real.sqrt (r / s) * (1 + n / (r * s))) :
    (1 / (3 * C)) * (Real.sqrt r * s * Real.sqrt s / ε) ≤ n := by
  have hs : 0 < s := hr.trans_le hrs
  have hsqrt : 0 < Real.sqrt (r / s) := Real.sqrt_pos.2 (div_pos hr hs)
  have h := samples_of_success hC (mul_pos hε hsqrt) (mul_pos hr hs)
    (bures_small hC hr hrs hε hsmall) hS (by simpa only [mul_assoc] using hbound)
  have heq : r * s / (3 * C * (ε * Real.sqrt (r / s))) =
      (1 / (3 * C)) * (Real.sqrt r * s * Real.sqrt s / ε) := by
    rw [Real.sqrt_div hr.le]
    have hsr : Real.sqrt r ≠ 0 := (Real.sqrt_pos.2 hr).ne'
    have hss : Real.sqrt s ≠ 0 := (Real.sqrt_pos.2 hs).ne'
    field_simp
    nlinarith [Real.sq_sqrt hr.le, Real.sq_sqrt hs.le]
  rwa [heq] at h

theorem bures_one_copy {C r s ε n S : ℝ} (hC : 0 < C) (hr : 0 < r)
    (hrs : r ≤ s) (hε : 0 < ε) (hsmall : ε ≤ accuracyThreshold C)
    (hS : 2 / 3 ≤ S)
    (hbound : S ≤ C * ε * Real.sqrt (r / s) * (1 + n / (r ^ 2 * s))) :
    (1 / (3 * C)) * (r * Real.sqrt r * s * Real.sqrt s / ε) ≤ n := by
  have hs : 0 < s := hr.trans_le hrs
  have hsqrt : 0 < Real.sqrt (r / s) := Real.sqrt_pos.2 (div_pos hr hs)
  have h := samples_of_success hC (mul_pos hε hsqrt)
    (mul_pos (sq_pos_of_pos hr) hs) (bures_small hC hr hrs hε hsmall) hS
    (by simpa only [mul_assoc] using hbound)
  have heq : r ^ 2 * s / (3 * C * (ε * Real.sqrt (r / s))) =
      (1 / (3 * C)) * (r * Real.sqrt r * s * Real.sqrt s / ε) := by
    rw [Real.sqrt_div hr.le]
    have hsr : Real.sqrt r ≠ 0 := (Real.sqrt_pos.2 hr).ne'
    have hss : Real.sqrt s ≠ 0 := (Real.sqrt_pos.2 hs).ne'
    field_simp
    nlinarith [Real.sq_sqrt hr.le, Real.sq_sqrt hs.le]
  rwa [heq] at h

theorem right_collective {C r s ε n S : ℝ} (hC : 0 < C) (hr : 0 < r)
    (hrs : r ≤ s) (hε : 0 < ε) (hsmall : ε ≤ accuracyThreshold C)
    (hS : 2 / 3 ≤ S)
    (hbound : S ≤ C * (r * ε ^ 2 / s) * (1 + n / (r * s))) :
    (1 / (3 * C)) * (s ^ 2 / ε ^ 2) ≤ n := by
  have hs : 0 < s := hr.trans_le hrs
  have h := samples_of_success hC (by positivity : 0 < r * ε ^ 2 / s)
    (mul_pos hr hs) (right_small hC hr hrs hε hsmall) hS hbound
  have heq : r * s / (3 * C * (r * ε ^ 2 / s)) =
      (1 / (3 * C)) * (s ^ 2 / ε ^ 2) := by field_simp
  rwa [heq] at h

theorem right_one_copy {C r s ε n S : ℝ} (hC : 0 < C) (hr : 0 < r)
    (hrs : r ≤ s) (hε : 0 < ε) (hsmall : ε ≤ accuracyThreshold C)
    (hS : 2 / 3 ≤ S)
    (hbound : S ≤ C * (r * ε ^ 2 / s) * (1 + n / (r ^ 2 * s))) :
    (1 / (3 * C)) * (r * s ^ 2 / ε ^ 2) ≤ n := by
  have hs : 0 < s := hr.trans_le hrs
  have h := samples_of_success hC (by positivity : 0 < r * ε ^ 2 / s)
    (mul_pos (sq_pos_of_pos hr) hs) (right_small hC hr hrs hε hsmall) hS hbound
  have heq : r ^ 2 * s / (3 * C * (r * ε ^ 2 / s)) =
      (1 / (3 * C)) * (r * s ^ 2 / ε ^ 2) := by field_simp
  rwa [heq] at h

end Paper26.SampleLowerBounds
