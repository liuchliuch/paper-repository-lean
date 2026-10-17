import CalibrationDistance.LowerProcess
import CalibrationDistance.CumulativeSecond
import CalibrationDistance.LowerWitness

open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators

namespace CalibrationDistance.Protocol
noncomputable section

theorem measurable_realizedMeans (K : BehavioralForecaster) (n : ℕ) :
    Measurable (realizedMeans K n) := by
  apply measurable_pi_lambda
  intro t
  exact (measurable_mean K t.val).comp (measurable_pastAt n t)

theorem measurable_realizedVariances (K : BehavioralForecaster) (n : ℕ) :
    Measurable (realizedVariances K n) := by
  apply measurable_pi_lambda
  intro t
  exact (measurable_variance K t.val).comp (measurable_pastAt n t)

theorem realizedMeans_mem (K : BehavioralForecaster) (n : ℕ) (h : History n) (t : Fin n) :
    realizedMeans K n h t ∈ Icc (0 : ℝ) 1 := mean_mem K t.val _

theorem realizedVariances_nonneg (K : BehavioralForecaster) (n : ℕ) (h : History n) (t : Fin n) :
    0 ≤ realizedVariances K n h t := variance_nonneg K t.val _

theorem realizedVariances_le_one (K : BehavioralForecaster) (n : ℕ) (h : History n) (t : Fin n) :
    realizedVariances K n h t ≤ 1 := variance_le_one K t.val _

theorem varianceIncrement_bounds (K : BehavioralForecaster) (a : ℕ) (ha : 1 ≤ a)
    (n : ℕ) (h : History (n+1)) :
    0 ≤ varianceIncrement K a n h ∧ varianceIncrement K a n h ≤ 2 := by
  have hq := lowerQ_mem_Icc ha (mean_mem K n h.1)
  have hv0 := variance_nonneg K n h.1
  have hv1 := variance_le_one K n h.1
  unfold varianceIncrement
  constructor
  · exact add_nonneg (mul_nonneg hq.1 (by linarith [hq.2])) hv0
  · nlinarith [sq_nonneg (lowerQ a (mean K n h.1))]

theorem energyIncrement_abs_le (K : BehavioralForecaster) (a n : ℕ) (h : History (n+1)) :
    |energyIncrement K a n h| ≤ 2 := by
  rw [abs_of_nonneg (energyIncrement_bounds K a n h).1]
  exact (energyIncrement_bounds K a n h).2

theorem varianceIncrement_abs_le (K : BehavioralForecaster) (a : ℕ) (ha : 1 ≤ a)
    (n : ℕ) (h : History (n+1)) : |varianceIncrement K a n h| ≤ 2 := by
  rw [abs_of_nonneg (varianceIncrement_bounds K a ha n h).1]
  exact (varianceIncrement_bounds K a ha n h).2

theorem badTotal_eq_sum (K : BehavioralForecaster) (n : ℕ) (h : History n) :
    badTotal K n h = ∑ t : Fin n,
      if (1 / 4 : ℝ) < |realizedMeans K n h t - 1 / 2| then (1 : ℝ) else 0 :=
  cumulative_eq_sum _ n h

theorem varianceTotal_eq_sum (K : BehavioralForecaster) (a n : ℕ) (h : History n) :
    varianceTotal K a n h = ∑ t : Fin n,
      (lowerQ a (realizedMeans K n h t) * (1-lowerQ a (realizedMeans K n h t)) +
        realizedVariances K n h t) := cumulative_eq_sum _ n h

lemma cumulative_nonneg_of_increment (d : (n : ℕ) → History (n+1) → ℝ)
    (hd : ∀ n h, 0 ≤ d n h) : ∀ n h, 0 ≤ cumulative d n h
  | 0, _ => le_refl 0
  | n+1, h => add_nonneg (cumulative_nonneg_of_increment d hd n h.1) (hd n h)

theorem energyTotal_nonneg (K : BehavioralForecaster) (a n : ℕ) (h : History n) :
    0 ≤ energyTotal K a n h :=
  cumulative_nonneg_of_increment _ (fun i h => (energyIncrement_bounds K a i h).1) n h

theorem varianceTotal_nonneg (K : BehavioralForecaster) (a : ℕ) (ha : 1 ≤ a)
    (n : ℕ) (h : History n) : 0 ≤ varianceTotal K a n h :=
  cumulative_nonneg_of_increment _ (fun i h => (varianceIncrement_bounds K a ha i h).1) n h

theorem badTotal_nonneg (K : BehavioralForecaster) (n : ℕ) (h : History n) :
    0 ≤ badTotal K n h := by
  apply cumulative_nonneg_of_increment _ _ n h
  intro i hi
  unfold badIncrement
  split_ifs <;> norm_num

theorem integrable_energyTotal (K : BehavioralForecaster) (a : ℕ)
    (B : RandomizedAdversary) (n : ℕ) : Integrable (energyTotal K a n) (law K B n) :=
  integrable_cumulative K B _ (measurable_energyIncrement K a)
    (energyIncrement_abs_le K a) n

theorem integrable_driftTotal (K : BehavioralForecaster) (a : ℕ) (ha : 1 ≤ a)
    (B : RandomizedAdversary) (n : ℕ) : Integrable (driftTotal K a n) (law K B n) :=
  integrable_cumulative K B _ (measurable_driftIncrement K a ha) (driftIncrement_abs_le K a ha) n

theorem integrable_zetaTotal (K : BehavioralForecaster) (a : ℕ) (ha : 1 ≤ a)
    (B : RandomizedAdversary) (n : ℕ) : Integrable (zetaTotal K a n) (law K B n) :=
  integrable_cumulative K B _ (measurable_zetaIncrement K a ha) (zetaIncrement_abs_le K a ha) n

theorem integrable_witnessTotal (K : BehavioralForecaster) (B : RandomizedAdversary) (n : ℕ) :
    Integrable (witnessTotal n) (law K B n) :=
  integrable_cumulative K B _ measurable_witnessIncrement witnessIncrement_abs_le n

theorem integrable_badTotal (K : BehavioralForecaster) (B : RandomizedAdversary) (n : ℕ) :
    Integrable (badTotal K n) (law K B n) :=
  integrable_cumulative K B _ (measurable_badIncrement K) (badIncrement_abs_le K) n

theorem integrable_varianceTotal (K : BehavioralForecaster) (a : ℕ) (ha : 1 ≤ a)
    (B : RandomizedAdversary) (n : ℕ) : Integrable (varianceTotal K a n) (law K B n) :=
  integrable_cumulative K B _ (measurable_varianceIncrement K a ha)
    (varianceIncrement_abs_le K a ha) n

/-- Expected energy equals the expected fixed linear witness, derived from the real transition. -/
theorem integral_witnessTotal_eq_energy (K : BehavioralForecaster) (a : ℕ) (ha : 1 ≤ a) (n : ℕ) :
    (∫ h, witnessTotal n h ∂law K (meanRevertingAdversary K a ha) n) =
      ∫ h, energyTotal K a n h ∂law K (meanRevertingAdversary K a ha) n := by
  rw [witnessTotal, integral_cumulative_eq_sum K _ _ measurable_witnessIncrement witnessIncrement_abs_le,
    energyTotal, integral_cumulative_eq_sum K _ _ (measurable_energyIncrement K a)
      (energyIncrement_abs_le K a)]
  apply Finset.sum_congr rfl
  intro i hi
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun h => by
    change (∫ r, stepEnergy r ∂transition K (meanRevertingAdversary K a ha) i h) = _
    rw [stepEnergy_integral K a ha i h]
    simp [energyIncrement]

/-- The exact cumulative second moment in (A.2), with the variance innovation included. -/
theorem integral_zetaTotal_sq_eq_variance (K : BehavioralForecaster) (a : ℕ) (ha : 1 ≤ a) (n : ℕ) :
    (∫ h, zetaTotal K a n h ^ 2 ∂law K (meanRevertingAdversary K a ha) n) =
      ∫ h, varianceTotal K a n h ∂law K (meanRevertingAdversary K a ha) n := by
  rw [zetaTotal, integral_cumulative_sq_eq_sum K _ _ (measurable_zetaIncrement K a ha)
    (zetaIncrement_abs_le K a ha) (zetaIncrement_centered K a ha),
    varianceTotal, integral_cumulative_eq_sum K _ _ (measurable_varianceIncrement K a ha)
      (varianceIncrement_abs_le K a ha)]
  apply Finset.sum_congr rfl
  intro i hi
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun h => by
    change (∫ r, (stepZeta _ _ r)^2 ∂transition K (meanRevertingAdversary K a ha) i h) = _
    rw [stepZeta_integral_sq K a ha i h]
    simp [varianceIncrement]

/-- Equation (5.7) for the actual randomized-forecast auxiliary law. -/
theorem energyTotal_loss_lower (K : BehavioralForecaster) (a : ℕ) (ha : 1 ≤ a) (n : ℕ) :
    (2 / 3 : ℝ) * (∫ h, energyTotal K a n h ∂law K (meanRevertingAdversary K a ha) n) ≤
      ∫ h, pathLoss n h ∂law K (meanRevertingAdversary K a ha) n := by
  rw [← integral_witnessTotal_eq_energy K a ha n]
  have h := integral_linear_witness_le
    (ν := law K (meanRevertingAdversary K a ha) n)
    (P := forecasts n) (Y := outcomes n)
    (fun i => ((measurable_pi_apply i).comp (measurable_forecasts n)).aemeasurable)
    (fun i => ((measurable_pi_apply i).comp (measurable_outcomes n)).aemeasurable)
    (Filter.Eventually.of_forall (forecasts_mem n))
    (Filter.Eventually.of_forall (outcomes_valid n))
    (integrable_pathLoss K _ n)
  have heq : lowerLinearWitness (forecasts n) (outcomes n) = witnessTotal n := by
    funext h
    exact (witnessTotal_eq_sum n h).symm
  simpa only [heq] using h

/-- Reverse triangle and the genuine total-residual witness, equation (5.17). -/
theorem zeta_drift_loss_lower (K : BehavioralForecaster) (a : ℕ) (ha : 1 ≤ a) (n : ℕ) :
    (∫ h, |zetaTotal K a n h| ∂law K (meanRevertingAdversary K a ha) n) -
      (∫ h, |driftTotal K a n h| ∂law K (meanRevertingAdversary K a ha) n) ≤
        ∫ h, pathLoss n h ∂law K (meanRevertingAdversary K a ha) n := by
  exact integral_residual_difference_le
    (Filter.Eventually.of_forall (forecasts_mem n))
    (Filter.Eventually.of_forall (outcomes_valid n))
    (integrable_zetaTotal K a ha _ n) (integrable_driftTotal K a ha _ n)
    (integrable_pathLoss K _ n)
    (Filter.Eventually.of_forall (zetaTotal_residual K a n))

end
end CalibrationDistance.Protocol
