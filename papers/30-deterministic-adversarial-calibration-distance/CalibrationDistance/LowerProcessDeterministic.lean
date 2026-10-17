import CalibrationDistance.LowerProcess
import CalibrationDistance.DeterministicProtocol
import CalibrationDistance.MomentsTails

/-! Specializing the actual history process to deterministic forecasting removes
the forecast-innovation term and improves the cumulative exponential parameter. -/

open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators NNReal

namespace CalibrationDistance.Protocol
noncomputable section

theorem deterministic_zetaIncrement_mgf {T : ℕ} (F : DeterministicForecaster T)
    (a : ℕ) (ha : 1 ≤ a) (n : ℕ) (h : History n) (t : ℝ) :
    (∫ r, Real.exp (t * zetaIncrement (deterministicBehavioral F) a n (h,r))
      ∂transition (deterministicBehavioral F)
        (meanRevertingAdversary (deterministicBehavioral F) a ha) n h) ≤
      Real.exp (t^2/8) := by
  rw [meanReverting_transition, deterministicBehavioral_apply]
  simpa only [zetaIncrement, stepZeta, boolValue, deterministicBehavioral_mean] using
    deterministic_step_mgf_le (deterministicPrediction F n h)
      (lowerQ_mem_Icc ha (deterministicPrediction F n h).property) t

/-- The exact cumulative parameter `n/4` used in Appendix A.3. -/
theorem deterministic_zetaTotal_hasSubgaussianMGF {T : ℕ} (F : DeterministicForecaster T)
    (a : ℕ) (ha : 1 ≤ a) (n : ℕ) :
    HasSubgaussianMGF (zetaTotal (deterministicBehavioral F) a n) ((n : ℝ≥0)/4)
      (law (deterministicBehavioral F)
        (meanRevertingAdversary (deterministicBehavioral F) a ha) n) := by
  have hh := cumulative_hasSubgaussianMGF (deterministicBehavioral F)
    (meanRevertingAdversary (deterministicBehavioral F) a ha)
    (zetaIncrement (deterministicBehavioral F) a)
    (measurable_zetaIncrement _ a ha) (zetaIncrement_abs_le _ a ha)
    (1/4 : ℝ≥0) (fun k h t => by
      convert deterministic_zetaIncrement_mgf F a ha k h t using 1 <;> norm_num <;> ring) n
  simpa only [div_eq_mul_inv, one_mul, zetaTotal] using hh

theorem deterministic_realizedVariances_zero {T : ℕ} (F : DeterministicForecaster T)
    (n : ℕ) (h : History n) (i : Fin n) :
    realizedVariances (deterministicBehavioral F) n h i = 0 := by
  simp [realizedVariances, deterministicBehavioral_variance]

/-- The randomized fourth moment (A.4) follows from the true law's cumulative
mgf and the proved layer-cake integral. -/
theorem zetaTotal_fourth_moment (K : BehavioralForecaster) (a : ℕ) (ha : 1 ≤ a)
    (n : ℕ) (hn : 0 < n) :
    (∫ h, (zetaTotal K a n h)^4 ∂law K (meanRevertingAdversary K a ha) n) ≤
      4 * (n : ℝ)^2 := by
  have hp : (0 : ℝ≥0) < (n : ℝ≥0)/2 := by exact div_pos (Nat.cast_pos.mpr hn) (by norm_num)
  have hh := fourth_moment_le_of_subgaussian (zetaTotal_hasSubgaussianMGF K a ha n) hp
  norm_num at hh ⊢
  nlinarith

/-- The deterministic fourth moment in (5.20), under the genuine auxiliary law. -/
theorem deterministic_zetaTotal_fourth_moment {T : ℕ} (F : DeterministicForecaster T)
    (a : ℕ) (ha : 1 ≤ a) (n : ℕ) (hn : 0 < n) :
    (∫ h, (zetaTotal (deterministicBehavioral F) a n h)^4
      ∂law (deterministicBehavioral F)
        (meanRevertingAdversary (deterministicBehavioral F) a ha) n) ≤ (n : ℝ)^2 := by
  have hp : (0 : ℝ≥0) < (n : ℝ≥0)/4 := by exact div_pos (Nat.cast_pos.mpr hn) (by norm_num)
  have hh := fourth_moment_le_of_subgaussian
    (deterministic_zetaTotal_hasSubgaussianMGF F a ha n) hp
  norm_num at hh ⊢
  nlinarith

end
end CalibrationDistance.Protocol
