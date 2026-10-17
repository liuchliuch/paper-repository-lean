import CalibrationDistance.ProtocolUniform
import CalibrationDistance.LowerStep
import Mathlib.MeasureTheory.Function.LocallyIntegrable

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory ENNReal

namespace CalibrationDistance.Protocol

noncomputable section

set_option maxHeartbeats 800000

def boolValue (b : Bool) : ℝ := if b then 1 else 0

@[fun_prop] theorem continuous_boolValue : Continuous boolValue := continuous_of_discreteTopology

@[simp] theorem boolValue_true : boolValue true = 1 := rfl
@[simp] theorem boolValue_false : boolValue false = 0 := rfl

def stepZeta (μ q : ℝ) (r : Round) : ℝ :=
  (boolValue r.2 - q) - ((r.1 : ℝ) - μ)

def stepEnergy (r : Round) : ℝ :=
  (1/2 - (r.1 : ℝ)) * (boolValue r.2 - (r.1 : ℝ))

@[fun_prop] theorem continuous_stepZeta (μ q : ℝ) : Continuous (stepZeta μ q) := by
  unfold stepZeta
  fun_prop

@[fun_prop] theorem continuous_stepEnergy : Continuous stepEnergy := by
  unfold stepEnergy
  fun_prop

/-- The round space is compact, so continuous polynomial observables are integrable. -/
theorem integrable_round_continuous (ρ : Measure Round) [IsFiniteMeasure ρ]
    {f : Round → ℝ} (hf : Continuous f) : Integrable f ρ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- Integrating the independent Bernoulli coordinate first. -/
theorem integral_round_bernoulli (ρ : Measure Probability) [IsProbabilityMeasure ρ]
    {q : ℝ} (hq : q ∈ Icc (0:ℝ) 1) {f : Round → ℝ} (hf : Continuous f) :
    (∫ r, f r ∂ρ.prod (bernoulliMeasure q)) =
      ∫ p, q * f (p,true) + (1-q) * f (p,false) ∂ρ := by
  rw [MeasureTheory.integral_prod _ (integrable_round_continuous _ hf)]
  simp_rw [integral_bernoulliMeasure hq]

/-- The actual history-dependent mean-reverting auxiliary coin. -/
noncomputable def meanRevertingAdversary (K : BehavioralForecaster) (a : ℕ)
    (ha : 1 ≤ a) : RandomizedAdversary :=
  bernoulliAdversary (fun n h => lowerQ a (mean K n h))
    (fun n => (continuous_lowerQ ha).measurable.comp (measurable_mean K n))

theorem meanReverting_transition (K : BehavioralForecaster) (a : ℕ) (ha : 1 ≤ a)
    (n : ℕ) (h : History n) :
    transition K (meanRevertingAdversary K a ha) n h =
      (K.kernel n h).prod (bernoulliMeasure (lowerQ a (mean K n h))) := by
  rw [transition_apply]
  change (K.kernel n h).prod
    (bernoulliKernel (fun h => lowerQ a (mean K n h))
      ((continuous_lowerQ ha).measurable.comp (measurable_mean K n)) h) = _
  rw [bernoulliKernel_apply]

/-- The first conditional moment in (5.11) vanishes under the real product transition. -/
theorem stepZeta_integral (K : BehavioralForecaster) (a : ℕ) (ha : 1 ≤ a)
    (n : ℕ) (h : History n) :
    (∫ r, stepZeta (mean K n h) (lowerQ a (mean K n h)) r
      ∂transition K (meanRevertingAdversary K a ha) n h) = 0 := by
  rw [meanReverting_transition, integral_round_bernoulli (K.kernel n h) (lowerQ_mem_Icc ha (mean_mem K n h))
    (continuous_stepZeta _ _)]
  have heq : (fun p : Probability =>
      lowerQ a (mean K n h) * stepZeta (mean K n h) (lowerQ a (mean K n h)) (p,true) +
      (1-lowerQ a (mean K n h)) * stepZeta (mean K n h) (lowerQ a (mean K n h)) (p,false)) =
      fun p : Probability => -((p:ℝ)-mean K n h) := by
    funext p
    simp only [stepZeta, boolValue_true, boolValue_false]
    ring
  rw [heq, integral_neg, integral_sub (integrable_forecast K n h) (integrable_const _)]
  simp [mean]

theorem integrable_variance (K : BehavioralForecaster) (n : ℕ) (h : History n) :
    Integrable (fun p : Probability => ((p:ℝ)-mean K n h)^2) (K.kernel n h) := by
  apply Continuous.integrable_of_hasCompactSupport (by fun_prop)
  exact HasCompactSupport.of_compactSpace _

/-- The conditional second-moment identity (5.12). -/
theorem stepZeta_integral_sq (K : BehavioralForecaster) (a : ℕ) (ha : 1 ≤ a)
    (n : ℕ) (h : History n) :
    (∫ r, (stepZeta (mean K n h) (lowerQ a (mean K n h)) r)^2
      ∂transition K (meanRevertingAdversary K a ha) n h) =
      lowerQ a (mean K n h) * (1-lowerQ a (mean K n h)) + variance K n h := by
  rw [meanReverting_transition, integral_round_bernoulli (K.kernel n h) (lowerQ_mem_Icc ha (mean_mem K n h))
    ((continuous_stepZeta _ _).pow 2)]
  have heq : (fun p : Probability =>
      lowerQ a (mean K n h) * (stepZeta (mean K n h) (lowerQ a (mean K n h)) (p,true))^2 +
      (1-lowerQ a (mean K n h)) * (stepZeta (mean K n h) (lowerQ a (mean K n h)) (p,false))^2) =
      fun p : Probability => lowerQ a (mean K n h) * (1-lowerQ a (mean K n h)) +
        ((p:ℝ)-mean K n h)^2 := by
    funext p
    simp only [stepZeta, boolValue_true, boolValue_false]
    ring
  rw [heq, integral_add (integrable_const _) (integrable_variance K n h)]
  simp [variance]

/-- The conditional energy identity (5.6), including forecast innovation variance. -/
theorem stepEnergy_integral (K : BehavioralForecaster) (a : ℕ) (ha : 1 ≤ a)
    (n : ℕ) (h : History n) :
    (∫ r, stepEnergy r ∂transition K (meanRevertingAdversary K a ha) n h) =
      |mean K n h-1/2|^(a+1) + variance K n h := by
  rw [meanReverting_transition, integral_round_bernoulli (K.kernel n h) (lowerQ_mem_Icc ha (mean_mem K n h))
    continuous_stepEnergy]
  calc
    _ = ∫ p : Probability, (1/2-(p:ℝ)) *
        (lowerQ a (mean K n h)-(p:ℝ)) ∂K.kernel n h := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun p => by
        simp only [stepEnergy, boolValue_true, boolValue_false]
        ring
    _ = |mean K n h-1/2|^(a+1) + variance K n h :=
      lower_step_energy_integral a measurable_subtype_coe.aemeasurable
        (Filter.Eventually.of_forall fun p => p.property)

end
end CalibrationDistance.Protocol

namespace CalibrationDistance.Protocol

theorem boolValue_mem (b : Bool) : boolValue b ∈ Icc (0:ℝ) 1 := by
  cases b <;> norm_num [boolValue]

theorem abs_sub_le_one_of_mem {x y : ℝ} (hx : x ∈ Icc (0:ℝ) 1)
    (hy : y ∈ Icc (0:ℝ) 1) : |x-y| ≤ 1 := by
  rw [abs_le]
  constructor <;> linarith [hx.1,hx.2,hy.1,hy.2]

theorem abs_stepZeta_le_two {μ q : ℝ} (hμ : μ ∈ Icc (0:ℝ) 1)
    (hq : q ∈ Icc (0:ℝ) 1) (r : Round) : |stepZeta μ q r| ≤ 2 := by
  calc
    |stepZeta μ q r| ≤ |boolValue r.2-q| + |(r.1:ℝ)-μ| := abs_sub _ _
    _ ≤ 1+1 := add_le_add (abs_sub_le_one_of_mem (boolValue_mem _) hq)
      (abs_sub_le_one_of_mem r.1.property hμ)
    _ = 2 := by norm_num

theorem abs_stepEnergy_le_half (r : Round) : |stepEnergy r| ≤ 1/2 := by
  have hp : |1/2-(r.1:ℝ)| ≤ 1/2 := by
    rw [abs_le]
    constructor <;> linarith [r.1.property.1,r.1.property.2]
  have hy := abs_sub_le_one_of_mem (boolValue_mem r.2) r.1.property
  calc
    |stepEnergy r| = |1/2-(r.1:ℝ)| * |boolValue r.2-(r.1:ℝ)| := abs_mul _ _
    _ ≤ (1/2)*1 := mul_le_mul hp hy (abs_nonneg _) (by norm_num)
    _ = 1/2 := by ring

theorem variance_le_one (K : BehavioralForecaster) (n : ℕ) (h : History n) :
    variance K n h ≤ 1 := by
  calc
    variance K n h ≤ ∫ _p : Probability, (1:ℝ) ∂K.kernel n h := by
      apply integral_mono (integrable_variance K n h) (integrable_const 1)
      intro p
      have hp := abs_sub_le_one_of_mem p.property (mean_mem K n h)
      have hp0 := abs_nonneg ((p:ℝ)-mean K n h)
      nlinarith [sq_abs ((p:ℝ)-mean K n h)]
    _ = 1 := by simp

end CalibrationDistance.Protocol
