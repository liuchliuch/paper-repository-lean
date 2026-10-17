import CalibrationDistance.Cumulative
import CalibrationDistance.ProtocolStep
import CalibrationDistance.ProtocolLoss
import CalibrationDistance.MomentsStep

/-! The actual energy, drift and martingale residual on the simultaneous-play
history space. All predictable coordinates are evaluated on the true past. -/

open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators NNReal

namespace CalibrationDistance.Protocol
noncomputable section

/-- Public history just before a specified completed round. -/
def pastAt : (n : ℕ) → History n → (t : Fin n) → History t.val
  | 0, _, i => Fin.elim0 i
  | n+1, h, i => Fin.lastCases (motive := fun j => History j.val) h.1
      (fun j => pastAt n h.1 j) i

theorem measurable_pastAt : ∀ n (i : Fin n),
    Measurable (fun h : History n => pastAt n h i)
  | 0, i => Fin.elim0 i
  | n+1, i => by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa [pastAt] using (measurable_fst :
          Measurable (Prod.fst : History n × Round → History n))
      · simpa [pastAt] using (measurable_pastAt n j).comp measurable_fst

/-- A cumulative observable really is the finite sum of its realized increments. -/
theorem cumulative_eq_sum (d : (n : ℕ) → History (n+1) → ℝ) :
    ∀ n (h : History n), cumulative d n h =
      ∑ t : Fin n, d t.val (pastAt n h t, roundAt n h t)
  | 0, _ => by simp [cumulative]
  | n+1, h => by
      rw [cumulative, Fin.sum_univ_castSucc, cumulative_eq_sum d n h.1]
      congr 1
      · apply Finset.sum_congr rfl
        intro t ht
        simp [pastAt, roundAt]
      · simp [pastAt, roundAt]

def energyIncrement (K : BehavioralForecaster) (a n : ℕ) (h : History (n+1)) : ℝ :=
  |mean K n h.1 - 1/2|^(a+1) + variance K n h.1

def driftIncrement (K : BehavioralForecaster) (a n : ℕ) (h : History (n+1)) : ℝ :=
  lowerDrift a (mean K n h.1)

def zetaIncrement (K : BehavioralForecaster) (a n : ℕ) (h : History (n+1)) : ℝ :=
  stepZeta (mean K n h.1) (lowerQ a (mean K n h.1)) h.2

def witnessIncrement (n : ℕ) (h : History (n+1)) : ℝ := stepEnergy h.2

def badIncrement (K : BehavioralForecaster) (n : ℕ) (h : History (n+1)) : ℝ :=
  if (1/4 : ℝ) < |mean K n h.1-1/2| then 1 else 0

def varianceIncrement (K : BehavioralForecaster) (a n : ℕ) (h : History (n+1)) : ℝ :=
  lowerQ a (mean K n h.1) * (1-lowerQ a (mean K n h.1)) + variance K n h.1

def realizedMeans (K : BehavioralForecaster) (n : ℕ) (h : History n) : Fin n → ℝ :=
  fun t => mean K t.val (pastAt n h t)

def realizedVariances (K : BehavioralForecaster) (n : ℕ) (h : History n) : Fin n → ℝ :=
  fun t => variance K t.val (pastAt n h t)

def energyTotal (K : BehavioralForecaster) (a : ℕ) := cumulative (energyIncrement K a)
def driftTotal (K : BehavioralForecaster) (a : ℕ) := cumulative (driftIncrement K a)
def zetaTotal (K : BehavioralForecaster) (a : ℕ) := cumulative (zetaIncrement K a)
def witnessTotal := cumulative witnessIncrement
def badTotal (K : BehavioralForecaster) := cumulative (badIncrement K)
def varianceTotal (K : BehavioralForecaster) (a : ℕ) := cumulative (varianceIncrement K a)

theorem measurable_energyIncrement (K : BehavioralForecaster) (a n : ℕ) :
    Measurable (energyIncrement K a n) :=
  (((measurable_mean K n).comp measurable_fst).sub measurable_const).abs.pow_const (a+1) |>.add
    ((measurable_variance K n).comp measurable_fst)

theorem measurable_driftIncrement (K : BehavioralForecaster) (a : ℕ) (ha : 1 ≤ a) (n : ℕ) :
    Measurable (driftIncrement K a n) :=
  (continuous_lowerDrift ha).measurable.comp ((measurable_mean K n).comp measurable_fst)

theorem measurable_zetaIncrement (K : BehavioralForecaster) (a : ℕ) (ha : 1 ≤ a) (n : ℕ) :
    Measurable (zetaIncrement K a n) := by
  have hm := (measurable_mean K n).comp (measurable_fst :
    Measurable (Prod.fst : History n × Round → History n))
  have hq := (continuous_lowerQ ha).measurable.comp hm
  have hp := measurable_subtype_coe.comp (measurable_fst.comp (measurable_snd :
    Measurable (Prod.snd : History n × Round → Round)))
  have hy := continuous_boolValue.measurable.comp (measurable_snd.comp (measurable_snd :
    Measurable (Prod.snd : History n × Round → Round)))
  exact (hy.sub hq).sub (hp.sub hm)

theorem measurable_witnessIncrement (n : ℕ) : Measurable (witnessIncrement n) :=
  continuous_stepEnergy.measurable.comp measurable_snd

theorem measurable_badIncrement (K : BehavioralForecaster) (n : ℕ) :
    Measurable (badIncrement K n) := by
  unfold badIncrement
  exact Measurable.ite (measurableSet_lt measurable_const
    (((measurable_mean K n).comp measurable_fst).sub measurable_const).abs)
    measurable_const measurable_const

theorem measurable_varianceIncrement (K : BehavioralForecaster) (a : ℕ) (ha : 1 ≤ a) (n : ℕ) :
    Measurable (varianceIncrement K a n) := by
  have hq : Measurable (fun h : History (n+1) => lowerQ a (mean K n h.1)) :=
    (continuous_lowerQ ha).measurable.comp ((measurable_mean K n).comp measurable_fst)
  exact (hq.mul (measurable_const.sub hq)).add ((measurable_variance K n).comp measurable_fst)

theorem energyIncrement_bounds (K : BehavioralForecaster) (a n : ℕ) (h : History (n+1)) :
    0 ≤ energyIncrement K a n h ∧ energyIncrement K a n h ≤ 2 := by
  have he : |mean K n h.1-1/2| ≤ 1 :=
    abs_sub_le_one_of_mem (mean_mem K n h.1) (by constructor <;> norm_num)
  have hp : |mean K n h.1-1/2|^(a+1) ≤ 1 := by
    simpa using pow_le_pow_left₀ (abs_nonneg _) he (a+1)
  constructor
  · exact add_nonneg (pow_nonneg (abs_nonneg _) _) (variance_nonneg K n h.1)
  · dsimp [energyIncrement]
    linarith [variance_le_one K n h.1]

theorem driftIncrement_abs_le (K : BehavioralForecaster) (a : ℕ) (ha : 1 ≤ a)
    (n : ℕ) (h : History (n+1)) : |driftIncrement K a n h| ≤ 1 := by
  rw [driftIncrement, abs_lowerDrift a ha]
  have he : |mean K n h.1-1/2| ≤ 1 :=
    abs_sub_le_one_of_mem (mean_mem K n h.1) (by constructor <;> norm_num)
  simpa using pow_le_pow_left₀ (abs_nonneg _) he a

theorem zetaIncrement_abs_le (K : BehavioralForecaster) (a : ℕ) (ha : 1 ≤ a)
    (n : ℕ) (h : History (n+1)) : |zetaIncrement K a n h| ≤ 2 :=
  abs_stepZeta_le_two (mean_mem K n h.1) (lowerQ_mem_Icc ha (mean_mem K n h.1)) h.2

theorem witnessIncrement_abs_le (n : ℕ) (h : History (n+1)) :
    |witnessIncrement n h| ≤ 1/2 := abs_stepEnergy_le_half h.2

theorem badIncrement_abs_le (K : BehavioralForecaster) (n : ℕ) (h : History (n+1)) :
    |badIncrement K n h| ≤ 1 := by unfold badIncrement; split_ifs <;> norm_num

theorem energyTotal_eq_sum (K : BehavioralForecaster) (a n : ℕ) (h : History n) :
    energyTotal K a n h = ∑ t : Fin n,
      (|realizedMeans K n h t-1/2|^(a+1) + realizedVariances K n h t) :=
  cumulative_eq_sum _ n h

theorem driftTotal_eq_sum (K : BehavioralForecaster) (a n : ℕ) (h : History n) :
    driftTotal K a n h = ∑ t : Fin n, lowerDrift a (realizedMeans K n h t) :=
  cumulative_eq_sum _ n h

theorem zetaTotal_residual (K : BehavioralForecaster) (a : ℕ) :
    ∀ n (h : History n), (∑ t : Fin n, (outcomes n h t - forecasts n h t)) =
      zetaTotal K a n h - driftTotal K a n h
  | 0, _ => by simp [zetaTotal, driftTotal, cumulative]
  | n+1, h => by
      rw [Fin.sum_univ_castSucc]
      simp only [outcomes, forecasts, roundAt, Fin.lastCases_castSucc, Fin.lastCases_last]
      change (∑ t : Fin n, (outcomes n h.1 t-forecasts n h.1 t)) +
        (boolValue h.2.2 - (h.2.1:ℝ)) =
        (zetaTotal K a n h.1 + zetaIncrement K a n h) -
        (driftTotal K a n h.1 + driftIncrement K a n h)
      rw [zetaTotal_residual K a n h.1]
      simp only [zetaIncrement, driftIncrement, stepZeta, lowerQ]
      ring

theorem witnessTotal_eq_sum : ∀ n (h : History n), witnessTotal n h =
    ∑ t : Fin n, (1/2-forecasts n h t) * (outcomes n h t-forecasts n h t)
  | 0, _ => by simp [witnessTotal, cumulative]
  | n+1, h => by
      rw [Fin.sum_univ_castSucc]
      simp only [outcomes, forecasts, roundAt, Fin.lastCases_castSucc, Fin.lastCases_last]
      change witnessTotal n h.1 + stepEnergy h.2 =
        (∑ t : Fin n, (1/2-forecasts n h.1 t) * (outcomes n h.1 t-forecasts n h.1 t)) + _
      rw [witnessTotal_eq_sum n h.1]
      rfl

theorem zetaIncrement_centered (K : BehavioralForecaster) (a : ℕ) (ha : 1 ≤ a)
    (n : ℕ) (h : History n) :
    (∫ r, zetaIncrement K a n (h,r) ∂transition K (meanRevertingAdversary K a ha) n h) = 0 :=
  stepZeta_integral K a ha n h

theorem zetaIncrement_mgf (K : BehavioralForecaster) (a : ℕ) (ha : 1 ≤ a)
    (n : ℕ) (h : History n) (t : ℝ) :
    (∫ r, Real.exp (t * zetaIncrement K a n (h,r))
      ∂transition K (meanRevertingAdversary K a ha) n h) ≤ Real.exp (t^2/4) := by
  rw [meanReverting_transition]
  exact simultaneous_step_mgf_le (K.kernel n h) (lowerQ_mem_Icc ha (mean_mem K n h)) t

/-- Appendix A.1's cumulative sub-Gaussian parameter, for every real-valued
behavioral forecasting kernel. -/
theorem zetaTotal_hasSubgaussianMGF (K : BehavioralForecaster) (a : ℕ) (ha : 1 ≤ a) (n : ℕ) :
    HasSubgaussianMGF (zetaTotal K a n) ((n : ℝ≥0)/2)
      (law K (meanRevertingAdversary K a ha) n) := by
  have hh := cumulative_hasSubgaussianMGF K (meanRevertingAdversary K a ha)
    (zetaIncrement K a) (measurable_zetaIncrement K a ha) (zetaIncrement_abs_le K a ha)
    (1/2 : ℝ≥0) (fun k h t => by
      convert zetaIncrement_mgf K a ha k h t using 1 <;> norm_num <;> ring) n
  simpa only [div_eq_mul_inv, one_mul, zetaTotal] using hh

end
end CalibrationDistance.Protocol
