import Paper38.Stability
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Paper38.Stability

open Real

/-- The positive logarithm entry time used in equation (5.6). -/
noncomputable def logEntryTime (C radius rate : ℝ) : ℝ :=
  max (log (C/radius)) 0 / rate

/-- Nonnegativity of the logarithmic entry time. -/
theorem logEntryTime_nonneg {C radius rate : ℝ} (hrate : 0 < rate) :
    0 ≤ logEntryTime C radius rate := by
  exact div_nonneg (le_max_right _ _) hrate.le

/-- Exact logarithmic time sufficient to enter and remain below a positive
threshold under an exponential attraction estimate. This is the scalar content
of equation (5.6), including the case where the positive logarithm vanishes. -/
theorem exp_bound_after_logEntryTime {C radius rate t : ℝ}
    (hC : 0 ≤ C) (hradius : 0 < radius) (hrate : 0 < rate)
    (ht : logEntryTime C radius rate ≤ t) :
    C * exp (-rate*t) ≤ radius := by
  by_cases hzero : C = 0
  · simpa [hzero] using hradius.le
  have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hzero)
  have hratio : 0 < C/radius := div_pos hCpos hradius
  have htime : max (log (C/radius)) 0 ≤ t*rate := (div_le_iff₀ hrate).mp ht
  have hlog : log (C/radius) ≤ rate*t := by
    nlinarith [le_max_left (log (C/radius)) 0]
  have hratio_bound : C/radius ≤ exp (rate*t) := by
    calc
      C/radius = exp (log (C/radius)) := (exp_log hratio).symm
      _ ≤ exp (rate*t) := exp_le_exp.mpr hlog
  have hCbound : C ≤ radius * exp (rate*t) := by
    nlinarith [(div_le_iff₀ hradius).mp hratio_bound]
  calc
    C * exp (-rate*t) ≤ (radius * exp (rate*t)) * exp (-rate*t) :=
      mul_le_mul_of_nonneg_right hCbound (exp_pos _).le
    _ = radius := by
      rw [mul_assoc, ← exp_add]
      simp

end Paper38.Stability
