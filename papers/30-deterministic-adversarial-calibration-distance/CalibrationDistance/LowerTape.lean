import CalibrationDistance.ProtocolLoss
import CalibrationDistance.ProtocolStep
import CalibrationDistance.ProtocolTape

/-! Removing the auxiliary adversary randomization in §5.1.

The theorem below compares two genuinely generated trajectory laws.  The only
randomness being fixed is the independent unit-uniform adversary tape.  No
moment estimate or lower bound is a premise of the transfer theorem.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace CalibrationDistance.Protocol

/-- Fubini and the exact tape-mixture marginal fix a deterministic Borel,
past-adaptive adversary with at least the auxiliary Bernoulli expected loss. -/
theorem exists_deterministic_adversary_ge_bernoulli
    (K : BehavioralForecaster) (q : (n : ℕ) → History n → ℝ)
    (hq : ∀ n, Measurable (q n)) (T : ℕ) :
    ∃ A : Adversary,
      (∫ h, pathLoss T h ∂law K (bernoulliAdversary q hq) T) ≤
        expectedCalDist K A T := by
  let ν := finiteTapeMeasure unitUniform T
  let B := finiteThresholdAdversary T q hq
  obtain ⟨w, hw⟩ := exists_fixed_parameter_calDist ν K B T
  refine ⟨B.section w, ?_⟩
  have hm : (parameterJointLaw ν K B T).snd =
      law K (bernoulliAdversary q hq) T := uniformTapeJointLaw_snd K q hq T
  have hi : (∫ h, pathLoss T h ∂(parameterJointLaw ν K B T).snd) =
      ∫ z, pathLoss T z.2 ∂parameterJointLaw ν K B T := by
    exact integral_map (φ := Prod.snd) measurable_snd.aemeasurable
      (measurable_pathLoss T).aestronglyMeasurable
  rw [hm] at hi
  exact hi.le.trans hw

/-- The source's mean-reverting auxiliary adversary can always be replaced by
a deterministic past-adaptive one without decreasing expected CalDist. -/
theorem exists_deterministic_adversary_ge_auxiliary
    (K : BehavioralForecaster) (a : ℕ) (ha : 1 ≤ a) (T : ℕ) :
    ∃ A : Adversary,
      (∫ h, pathLoss T h ∂law K (meanRevertingAdversary K a ha) T) ≤
        expectedCalDist K A T :=
  exists_deterministic_adversary_ge_bernoulli K
    (fun n h => lowerQ a (mean K n h))
    (fun n => (continuous_lowerQ ha).measurable.comp (measurable_mean K n)) T

end CalibrationDistance.Protocol
