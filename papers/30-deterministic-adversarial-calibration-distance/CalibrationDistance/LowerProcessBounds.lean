import CalibrationDistance.LowerProcess
import CalibrationDistance.LowerDriftIntegral

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CalibrationDistance.Protocol

theorem lower_realizedMeans_measurable (K : BehavioralForecaster) (T : ℕ) (i : Fin T) :
    Measurable (fun h => realizedMeans K T h i) :=
  (measurable_mean K i.val).comp (measurable_pastAt T i)

theorem lower_realizedVariances_measurable (K : BehavioralForecaster) (T : ℕ) (i : Fin T) :
    Measurable (fun h => realizedVariances K T h i) :=
  (measurable_variance K i.val).comp (measurable_pastAt T i)

theorem lower_realizedMeans_mem (K : BehavioralForecaster) (T : ℕ) (h : History T) (i : Fin T) :
    realizedMeans K T h i ∈ Set.Icc (0 : ℝ) 1 := mean_mem K i.val _

theorem lower_realizedVariances_mem (K : BehavioralForecaster) (T : ℕ) (h : History T) (i : Fin T) :
    realizedVariances K T h i ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨variance_nonneg K i.val _, variance_le_one K i.val _⟩

theorem energyTotal_eq_lowerEnergy (K : BehavioralForecaster) (a T : ℕ) :
    energyTotal K a T = lowerEnergy a (realizedMeans K T) (realizedVariances K T) := by
  funext h
  exact energyTotal_eq_sum K a T h

theorem driftTotal_eq_lowerDriftTotal (K : BehavioralForecaster) (a T : ℕ) :
    driftTotal K a T = lowerDriftTotal a (realizedMeans K T) := by
  funext h
  exact driftTotal_eq_sum K a T h

/-- The drift estimate (A.5) instantiated on the actual trajectory law. -/
theorem driftTotal_integral_bound (K : BehavioralForecaster) (B : RandomizedAdversary)
    (a T : ℕ) (ha : 1 ≤ a) (hT : 0 < T) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hsmall : (∫ h, energyTotal K a T h ∂law K B T) ≤ c * lowerScale T a) :
    (∫ h, |driftTotal K a T h| ∂law K B T) ≤ Real.sqrt c * Real.sqrt T := by
  rw [energyTotal_eq_lowerEnergy] at hsmall
  rw [driftTotal_eq_lowerDriftTotal]
  have hh := lower_drift_integral_bound (ν := law K B T) ha
    (fun i => (lower_realizedMeans_measurable K T i).aemeasurable)
    (fun i => (lower_realizedVariances_measurable K T i).aemeasurable)
    (lower_realizedMeans_mem K T) (lower_realizedVariances_mem K T)
    (by simpa using hT) hc0 hc1 (by simpa using hsmall)
  simpa using hh

theorem lower_badTotal_eq_sum (K : BehavioralForecaster) (T : ℕ) (h : History T) :
    badTotal K T h = ∑ i : Fin T,
      if (1 / 4 : ℝ) < |realizedMeans K T h i - 1 / 2| then (1 : ℝ) else 0 := by
  exact cumulative_eq_sum (badIncrement K) T h

/-- The pathwise bad-round inequality in Appendix A.1, under the real protocol. -/
theorem badTotal_le_energyTotal (K : BehavioralForecaster) (a T : ℕ) (h : History T) :
    badTotal K T h ≤ (4 : ℝ) ^ (a + 1) * energyTotal K a T h := by
  rw [lower_badTotal_eq_sum, energyTotal_eq_sum]
  exact lower_bad_count a (fun i => realizedMeans K T h i - 1 / 2)
    (realizedVariances K T h) (fun i => variance_nonneg K i.val _)

theorem lower_varianceTotal_eq_sum (K : BehavioralForecaster) (a T : ℕ) (h : History T) :
    varianceTotal K a T h = ∑ i : Fin T,
      (lowerQ a (realizedMeans K T h i) * (1 - lowerQ a (realizedMeans K T h i)) +
        realizedVariances K T h i) :=
  cumulative_eq_sum _ T h

/-- The pathwise variance comparison preceding martingale orthogonality (A.2). -/
theorem varianceTotal_ge_good_rounds (K : BehavioralForecaster) (a T : ℕ)
    (ha : 1 ≤ a) (h : History T) :
    (3 / 16 : ℝ) * ((T : ℝ) - badTotal K T h) ≤ varianceTotal K a T h := by
  rw [lower_varianceTotal_eq_sum, lower_badTotal_eq_sum]
  simpa only [Fintype.card_fin] using lower_variance_sum ha
    (realizedMeans K T h) (realizedVariances K T h)
    (lower_realizedMeans_mem K T h) (fun i => variance_nonneg K i.val _)

theorem lower_integrable_badTotal (K : BehavioralForecaster) (B : RandomizedAdversary) (T : ℕ) :
    Integrable (badTotal K T) (law K B T) :=
  integrable_cumulative K B (badIncrement K) (measurable_badIncrement K)
    (badIncrement_abs_le K) T

theorem lower_integrable_energyTotal (K : BehavioralForecaster) (B : RandomizedAdversary)
    (a T : ℕ) : Integrable (energyTotal K a T) (law K B T) := by
  rw [energyTotal_eq_lowerEnergy]
  exact integrable_lowerEnergy a
    (fun i => (lower_realizedMeans_measurable K T i).aemeasurable)
    (fun i => (lower_realizedVariances_measurable K T i).aemeasurable)
    (lower_realizedMeans_mem K T) (lower_realizedVariances_mem K T)

theorem lower_integral_energyTotal_nonneg (K : BehavioralForecaster) (B : RandomizedAdversary)
    (a T : ℕ) : 0 ≤ ∫ h, energyTotal K a T h ∂law K B T := by
  rw [energyTotal_eq_lowerEnergy]
  exact integral_nonneg (lowerEnergy_nonneg a (fun h i => variance_nonneg K i.val _))

/-- Expected bad count is controlled by actual expected energy. -/
theorem integral_badTotal_le_energyTotal (K : BehavioralForecaster) (B : RandomizedAdversary)
    (a T : ℕ) :
    (∫ h, badTotal K T h ∂law K B T) ≤
      (4 : ℝ) ^ (a + 1) * ∫ h, energyTotal K a T h ∂law K B T := by
  rw [← integral_const_mul]
  exact integral_mono (lower_integrable_badTotal K B T)
    ((lower_integrable_energyTotal K B a T).const_mul _) (badTotal_le_energyTotal K a T)

/-- The small-energy bad-count estimate, including the logarithmic choice of `a`. -/
theorem integral_badTotal_small_energy (K : BehavioralForecaster) (B : RandomizedAdversary)
    (T : ℕ) (hT : 2 ≤ T) {c : ℝ} (hc : 0 < c)
    (hsmall : (∫ h, energyTotal K (lowerExponent T) T h ∂law K B T) <
      c * lowerScale T (lowerExponent T)) :
    (∫ h, badTotal K T h ∂law K B T) < 16 * c * T := by
  have hTr : (2 : ℝ) ≤ T := by exact_mod_cast hT
  exact lower_bad_expectation (by linarith) hc (lowerScale_bounds hTr).2
    (lower_integral_energyTotal_nonneg K B _ T) hsmall (lowerExponent_bad_factor hTr)
    (integral_badTotal_le_energyTotal K B _ T)

end CalibrationDistance.Protocol
