import CalibrationDistance.Core
import CalibrationDistance.Finite
import CalibrationDistance.Protocol

/-! The paper's actual calibration loss on the Ionescu--Tulcea trajectory law.
Measurability is derived from forecast continuity and the finite outcome space;
neither the loss nor its integrability is an assumed protocol field. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace CalibrationDistance.Protocol

def binaryOutcomes (T : ℕ) (h : History T) : Fin T → Bool :=
  fun i => (roundAt T h i).2

def realOutcomes {T : ℕ} (y : Fin T → Bool) : Fin T → ℝ :=
  fun i => if y i then 1 else 0

theorem realOutcomes_valid {T : ℕ} (y : Fin T → Bool) : Valid (realOutcomes y) := by
  intro i
  unfold realOutcomes
  cases y i <;> norm_num

theorem outcomes_valid (T : ℕ) (h : History T) : Valid (outcomes T h) := by
  intro i
  rcases outcomes_binary T h i with hi | hi <;> rw [hi] <;> norm_num

theorem measurable_binaryOutcomes (T : ℕ) : Measurable (binaryOutcomes T) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_snd.comp (measurable_roundAt T i)

/-- Joint Borel measurability on the continuous forecast and finite outcome spaces. -/
theorem measurable_binary_calDist (T : ℕ) :
    Measurable (fun z : (Fin T → ℝ) × (Fin T → Bool) => calDist z.1 (realOutcomes z.2)) := by
  apply measurable_from_prod_countable_left
  intro y
  exact (continuous_calDist (realOutcomes_valid y)).measurable

noncomputable def pathLoss (T : ℕ) (h : History T) : ℝ :=
  calDist (forecasts T h) (outcomes T h)

theorem measurable_pathLoss (T : ℕ) : Measurable (pathLoss T) := by
  have hm := (measurable_binary_calDist T).comp
    ((measurable_forecasts T).prodMk (measurable_binaryOutcomes T))
  exact hm

theorem pathLoss_nonneg (T : ℕ) (h : History T) : 0 ≤ pathLoss T h :=
  calDist_nonneg (outcomes_valid T h)

theorem pathLoss_le_horizon (T : ℕ) (h : History T) : pathLoss T h ≤ T := by
  simpa only [Fintype.card_fin] using
    calDist_le_card (forecasts_mem T h) (outcomes_valid T h)

theorem norm_pathLoss_le_horizon (T : ℕ) (h : History T) : ‖pathLoss T h‖ ≤ T := by
  rw [Real.norm_eq_abs, abs_of_nonneg (pathLoss_nonneg T h)]
  exact pathLoss_le_horizon T h

theorem integrable_pathLoss (K : BehavioralForecaster) (B : RandomizedAdversary) (T : ℕ) :
    Integrable (pathLoss T) (law K B T) :=
  integrable_bounded_loss K B T (pathLoss T) (measurable_pathLoss T) T
    (norm_pathLoss_le_horizon T)

noncomputable def expectedCalDist (K : BehavioralForecaster) (A : Adversary) (T : ℕ) : ℝ :=
  expectation K A T (pathLoss T)

theorem expectedCalDist_nonneg (K : BehavioralForecaster) (A : Adversary) (T : ℕ) :
    0 ≤ expectedCalDist K A T :=
  integral_nonneg (pathLoss_nonneg T)

theorem expectedCalDist_le_horizon (K : BehavioralForecaster) (A : Adversary) (T : ℕ) :
    expectedCalDist K A T ≤ T := by
  calc
    expectedCalDist K A T ≤ ∫ _h : History T, (T : ℝ) ∂law K A.randomized T :=
      integral_mono (integrable_pathLoss K A.randomized T) (integrable_const (T : ℝ))
        (pathLoss_le_horizon T)
    _ = T := by simp

theorem integrable_parameter_pathLoss {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (K : BehavioralForecaster)
    (A : ParametricAdversary Ω) (T : ℕ) :
    Integrable (fun z : Ω × History T => pathLoss T z.2) (parameterJointLaw ν K A T) :=
  integrable_parameter_loss ν K A T (pathLoss T) (measurable_pathLoss T) T
    (norm_pathLoss_le_horizon T)

/-- Fixing the adversary's auxiliary tape applies to the actual CalDist loss without
an extra integrability premise. This is the averaging step used in §5.1. -/
theorem exists_fixed_parameter_calDist {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (K : BehavioralForecaster)
    (A : ParametricAdversary Ω) (T : ℕ) :
    ∃ w, (∫ z, pathLoss T z.2 ∂parameterJointLaw ν K A T) ≤
      expectedCalDist K (A.section w) T :=
  exists_fixed_parameter ν K A T (pathLoss T) (integrable_parameter_pathLoss ν K A T)

end CalibrationDistance.Protocol
