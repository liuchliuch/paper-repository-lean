import CalibrationDistance.LowerProcessBounds
import CalibrationDistance.LowerProcessMoments
import CalibrationDistance.LowerProcessDeterministic

/-! The complete energy split under the actual mean-reverting auxiliary law.
No moment, energy identity, or conditional independence estimate is a premise
of the two auxiliary lower-bound theorems below. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CalibrationDistance.Protocol

theorem integral_varianceTotal_ge_good_rounds (K : BehavioralForecaster)
    (B : RandomizedAdversary) (a T : ℕ) (ha : 1 ≤ a) :
    (3 / 16 : ℝ) * ((T : ℝ) - ∫ h, badTotal K T h ∂law K B T) ≤
      ∫ h, varianceTotal K a T h ∂law K B T := by
  have hb := integrable_badTotal K B T
  have hl : Integrable (fun h => (3 / 16 : ℝ) * ((T : ℝ) - badTotal K T h))
      (law K B T) := ((integrable_const (T : ℝ)).sub hb).const_mul _
  calc
    (3 / 16 : ℝ) * ((T : ℝ) - ∫ h, badTotal K T h ∂law K B T) =
        ∫ h, (3 / 16 : ℝ) * ((T : ℝ) - badTotal K T h) ∂law K B T := by
      rw [integral_const_mul, integral_sub (integrable_const (T : ℝ)) hb]
      simp
    _ ≤ ∫ h, varianceTotal K a T h ∂law K B T :=
      integral_mono hl (integrable_varianceTotal K a ha B T)
        (varianceTotal_ge_good_rounds K a T ha)

/-- The actual second moment in the small-energy branch, with the threshold
left as a numerical parameter so both source constants use the same proof. -/
theorem zetaTotal_second_moment_small_energy (K : BehavioralForecaster)
    (T : ℕ) (hT : 2 ≤ T) {c : ℝ} (hc : 0 < c)
    (hsmall : (∫ h, energyTotal K (lowerExponent T) T h
        ∂law K (meanRevertingAdversary K (lowerExponent T)
          (lowerExponent_pos (by exact_mod_cast hT))) T) <
      c * lowerScale T (lowerExponent T)) :
    (3 / 16 : ℝ) * (1 - 16 * c) * T ≤
      ∫ h, zetaTotal K (lowerExponent T) T h ^ 2
        ∂law K (meanRevertingAdversary K (lowerExponent T)
          (lowerExponent_pos (by exact_mod_cast hT))) T := by
  let a := lowerExponent (T : ℝ)
  have ha : 1 ≤ a := lowerExponent_pos (by exact_mod_cast hT)
  let B := meanRevertingAdversary K a ha
  have hn := integral_badTotal_small_energy K B T hT hc hsmall
  have hv := integral_varianceTotal_ge_good_rounds K B a T ha
  rw [integral_zetaTotal_sq_eq_variance K a ha T]
  linarith

/-- The randomized-forecast auxiliary expected lower bound, (5.9)/(5.17).
Theorem 5.1 subsequently fixes the auxiliary adversary's tape. -/
theorem randomized_auxiliary_lower (K : BehavioralForecaster) (T : ℕ) (hT : 2 ≤ T) :
    Real.sqrt (T : ℝ) / 4320 ≤
      ∫ h, pathLoss T h ∂law K
        (meanRevertingAdversary K (lowerExponent T)
          (lowerExponent_pos (by exact_mod_cast hT))) T := by
  have hTr : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hTp : (0 : ℝ) < T := by linarith
  have hn : 0 < T := by omega
  let a := lowerExponent (T : ℝ)
  have ha : 1 ≤ a := lowerExponent_pos hTr
  let B := meanRevertingAdversary K a ha
  change Real.sqrt (T : ℝ) / 4320 ≤ ∫ h, pathLoss T h ∂law K B T
  by_cases hlarge : lowerScale T a / 720 ≤ ∫ h, energyTotal K a T h ∂law K B T
  · exact randomized_high_energy (lowerScale_bounds hTr).1 hlarge
      (energyTotal_loss_lower K a ha T)
  · have hsmall : (∫ h, energyTotal K a T h ∂law K B T) <
        (1 / 720 : ℝ) * lowerScale T a := by
      have hh := lt_of_not_ge hlarge
      simpa only [div_eq_mul_inv, one_mul, mul_comm] using hh
    have h2 : (11 / 60 : ℝ) * T ≤
        ∫ h, zetaTotal K a T h ^ 2 ∂law K B T := by
      have hh := zetaTotal_second_moment_small_energy K T hT
        (by norm_num : (0 : ℝ) < 1 / 720) hsmall
      norm_num at hh ⊢
      exact hh
    have h4 := zetaTotal_fourth_moment K a ha T hn
    have hi := moment_interpolation_cubic_of_bound
      (zetaTotal_hasSubgaussianMGF K a ha T).aemeasurable
      (Filter.Eventually.of_forall (cumulative_abs_le (zetaIncrement K a)
        (zetaIncrement_abs_le K a ha) T))
    have hz := randomized_abs_moment_lower hTp
      (integral_nonneg (fun _ => abs_nonneg _)) h2 h4 hi
    have hd0 := driftTotal_integral_bound K B a T ha hn
      (by norm_num : (0 : ℝ) ≤ 1 / 720) (by norm_num : (1 / 720 : ℝ) ≤ 1) hsmall.le
    have hd : (∫ h, |driftTotal K a T h| ∂law K B T) ≤
        Real.sqrt (T : ℝ) / Real.sqrt 720 := by
      rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one] at hd0
      simpa only [div_eq_mul_inv, one_mul, mul_comm] using hd0
    exact (randomized_low_energy hTp hz hd (zeta_drift_loss_lower K a ha T)).le

/-- The deterministic-forecast auxiliary expected lower bound, (5.19)/(5.21).
Theorem 5.2 subsequently selects one fixed outcome string. -/
theorem deterministic_auxiliary_lower {T : ℕ} (F : DeterministicForecaster T) (hT : 2 ≤ T) :
    Real.sqrt (T : ℝ) / 1200 ≤
      ∫ h, pathLoss T h ∂law (deterministicBehavioral F)
        (meanRevertingAdversary (deterministicBehavioral F) (lowerExponent T)
          (lowerExponent_pos (by exact_mod_cast hT))) T := by
  have hTr : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hTp : (0 : ℝ) < T := by linarith
  have hn : 0 < T := by omega
  let K := deterministicBehavioral F
  let a := lowerExponent (T : ℝ)
  have ha : 1 ≤ a := lowerExponent_pos hTr
  let B := meanRevertingAdversary K a ha
  change Real.sqrt (T : ℝ) / 1200 ≤ ∫ h, pathLoss T h ∂law K B T
  by_cases hlarge : lowerScale T a / 200 ≤ ∫ h, energyTotal K a T h ∂law K B T
  · exact deterministic_high_energy (lowerScale_bounds hTr).1 hlarge
      (energyTotal_loss_lower K a ha T)
  · have hsmall : (∫ h, energyTotal K a T h ∂law K B T) <
        (1 / 200 : ℝ) * lowerScale T a := by
      have hh := lt_of_not_ge hlarge
      simpa only [div_eq_mul_inv, one_mul, mul_comm] using hh
    have h2 : (69 / 400 : ℝ) * T ≤
        ∫ h, zetaTotal K a T h ^ 2 ∂law K B T := by
      have hh := zetaTotal_second_moment_small_energy K T hT
        (by norm_num : (0 : ℝ) < 1 / 200) hsmall
      norm_num at hh ⊢
      exact hh
    have h4 := deterministic_zetaTotal_fourth_moment F a ha T hn
    have hi := moment_interpolation_cubic_of_bound
      (zetaTotal_hasSubgaussianMGF K a ha T).aemeasurable
      (Filter.Eventually.of_forall (cumulative_abs_le (zetaIncrement K a)
        (zetaIncrement_abs_le K a ha) T))
    have hz := deterministic_abs_moment_lower hTp
      (integral_nonneg (fun _ => abs_nonneg _)) h2 h4 hi
    have hd0 := driftTotal_integral_bound K B a T ha hn
      (by norm_num : (0 : ℝ) ≤ 1 / 200) (by norm_num : (1 / 200 : ℝ) ≤ 1) hsmall.le
    have hd : (∫ h, |driftTotal K a T h| ∂law K B T) ≤
        Real.sqrt (T : ℝ) / Real.sqrt 200 := by
      rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one] at hd0
      simpa only [div_eq_mul_inv, one_mul, mul_comm] using hd0
    exact (deterministic_low_energy hTp hz hd (zeta_drift_loss_lower K a ha T)).le

end CalibrationDistance.Protocol
