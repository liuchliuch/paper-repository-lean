import Paper26.PureTensorSuccess
import Paper26.PureLowerArithmetic
import Paper26.HaarLossBalls
import Paper26.LossMeasurability
import Paper26.JordanLossMeasurability

/-!
# Actual collective pure-state and qubit sample lower bounds

The inputs are the standard symmetric-projector theorem and the already
specified classical Haar/volume inputs.  Actual `Learner.LearnsRank` implies
prior-average success at least `2/3`; that implication is proved here, not
supplied as a success-rate parameter.  The actual symmetric tensor argument
and the full Haar loss balls then imply the scalar power constraint.

For all `m ≥ 1`, including `m=1` (qubits), small positive divergence accuracy
requires `n ≥ m*sqrt(m)/(18*exp(1)^2*ε)` for chiB and
`n ≥ m^2/(54*exp(1)^2*ε^2)` for chiR.  Joint loss measurability is discharged
by the actual singular-inclusive loss measurability modules.  Outcomes are
arbitrary measurable spaces and outputs are unrestricted density matrices.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal
open MeasureTheory

namespace Paper26.PureCollectiveLowerBounds

open QuantumModel HaarFrames HaarTruncation CollectiveModel SymmetricSupport

abbrev StateIndex (m : ℕ) := Fin 1 ⊕ Fin m
abbrev PureFrame (m : ℕ) := Frame (StateIndex m) (Fin 1)

/-- Existing raw inputs shared by both Haar loss-ball theorems. No field
states a probability bound, successful volume, or sample lower bound. -/
structure CommonHaarInputs (m : ℕ) where
  truncation : TruncatedHaarInput
  properNull : ProperSubspaceNullInput (StateIndex m) (Fin 1)
  metric : TailMass.BuresMetricInput (StateIndex m)
  compression : TailMassBridges.RawCompressionInput (StateIndex m) (Fintype.card (Fin 1))
  ballVolume : ScalarTailBall.EuclideanBallVolumeInput (Fin m) (Fin 1)
  haar : Measure (PureFrame m)
  isHaar : IsHaarFrameDistribution haar

structure BuresHaarInputs (m : ℕ) where
  common : CommonHaarInputs m
  lyapunov : TailConvexity.LyapunovPositivityInput (Fin m)
  brunnMinkowski : TailVolume.BrunnMinkowskiInput (Fin m) (Fin 1)
  unitaryLebesgue : TailVolume.UnitaryLebesgueInput (Fin m) (Fin 1)

structure RightHaarInputs (m : ℕ) where
  common : CommonHaarInputs m
  rowScaling : RightTailVolume.PositiveRowScalingInput (Fin m) (Fin 1)

variable {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- Uniform actual rank-one learning guarantees imply true Haar-average
success. The rank bound is proved for each actual frame density. -/
theorem learnsRank_average_lower (A : Learner (StateIndex m) Ω n)
    (μ : Measure (PureFrame m)) [IsProbabilityMeasure μ]
    (loss : Density (StateIndex m) → Density (StateIndex m) → ℝ≥0∞) (ε : ℝ≥0∞)
    (hA : A.LearnsRank loss 1 ε ((2 : ℝ≥0∞) / 3)) :
    (2 : ℝ≥0∞) / 3 ≤ ∫⁻ U, A.successProbability loss U.density ε ∂μ := by
  calc
    _ = ∫⁻ _U : PureFrame m, (2 : ℝ≥0∞) / 3 ∂μ := by simp
    _ ≤ _ := lintegral_mono (fun U => (hA U.density (by
      rw [Frame.density_rank]
      simp only [Fintype.card_fin, le_refl])).2)

/-- The symmetric projector has positive rank even for the empty tensor. -/
theorem symmetric_rank_pos (P : SymmetricProjectorInput (StateIndex m) n) :
    0 < P.projector.matrix.rank := by
  rw [P.dimension]
  apply Nat.choose_pos
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

/-- Actual learning, actual tensor support, and a successful-volume component
bound imply the power constraint; no final success-rate premise is used. -/
theorem learnsRank_dimension_volume (P : SymmetricProjectorInput (StateIndex m) n)
    (A : Learner (StateIndex m) Ω n) (μ : Measure (PureFrame m))
    [IsProbabilityMeasure μ]
    (loss : Density (StateIndex m) → Density (StateIndex m) → ℝ≥0∞)
    (ε v : ℝ≥0∞)
    (hA : A.LearnsRank loss 1 ε ((2 : ℝ≥0∞) / 3))
    (hgood : MeasurableSet {z : PureFrame m × Ω |
      loss z.1.density (A.estimator.estimate z.2) ≤ ε})
    (hvolume : ∀ τ : Density (StateIndex m), μ {U | loss U.density τ ≤ ε} ≤ v) :
    (2 : ℝ≥0∞) / 3 ≤ ((n + m).choose n : ℝ≥0∞) * v := by
  have h := (learnsRank_average_lower A μ loss ε hA).trans
    (PureTensorSuccess.average_success_le_dimension_volume P (symmetric_rank_pos P)
      A μ loss ε v hgood hvolume)
  have hd : n + Fintype.card (StateIndex m) - 1 = n + m := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  simpa only [hd] using h

lemma real_power_constraint (n m : ℕ) {v : ℝ} (hv : 0 ≤ v)
    (h : (2 : ℝ≥0∞) / 3 ≤ ((n + m).choose n : ℝ≥0∞) * ENNReal.ofReal (v ^ m)) :
    2 / 3 ≤ ((n + m).choose n : ℝ) * v ^ m := by
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity :
    0 ≤ ((n + m).choose n : ℝ) * v ^ m)).mp
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  norm_num only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3),
    ENNReal.ofReal_ofNat]
  exact h

/-- The actual chiB learner implies the exact pure tensor/Haar power constraint. -/
theorem bures_power_constraint (hm : 0 < m) (V : BuresHaarInputs m)
    (P : SymmetricProjectorInput (StateIndex m) n) (A : Learner (StateIndex m) Ω n)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 4)
    (hA : A.BuresSuccess 1 (ENNReal.ofReal ε)) :
    2 / 3 ≤ ((n + m).choose n : ℝ) *
      (6 * Real.exp 1 * ε * Real.sqrt (1 / (m : ℝ))) ^ m := by
  letI := V.common.isHaar.probability
  apply real_power_constraint n m (by positivity)
  apply learnsRank_dimension_volume P A V.common.haar chiB (ENNReal.ofReal ε) _ hA
    (JordanLossMeasurability.measurableSet_frame_estimator_success A.estimator _)
  intro τ
  simpa only [Nat.cast_one, one_mul, Nat.one_mul] using
    HaarLossBalls.theorem_2_4_bures 1 m (by omega) (by omega)
      V.common.truncation V.common.properNull V.common.metric V.common.compression
      V.lyapunov V.brunnMinkowski V.unitaryLebesgue V.common.ballVolume
      V.common.haar V.common.isHaar τ hε hε1

/-- The actual chiR learner implies the singular-inclusive right-inverse power constraint. -/
theorem right_power_constraint (hm : 0 < m) (V : RightHaarInputs m)
    (P : SymmetricProjectorInput (StateIndex m) n) (A : Learner (StateIndex m) Ω n)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 4)
    (hA : A.RightSuccess 1 (ENNReal.ofReal ε)) :
    2 / 3 ≤ ((n + m).choose n : ℝ) * (18 * Real.exp 1 * ε ^ 2 / (m : ℝ)) ^ m := by
  letI := V.common.isHaar.probability
  apply real_power_constraint n m (by positivity)
  apply learnsRank_dimension_volume P A V.common.haar chiR (ENNReal.ofReal ε) _ hA
    (LossMeasurability.measurableSet_frame_estimator_success A.estimator _)
  intro τ
  simpa only [Nat.cast_one, mul_one, Nat.one_mul] using
    HaarLossBalls.theorem_2_4_right 1 m (by omega) (by omega)
      V.common.truncation V.common.properNull V.common.metric V.common.compression
      V.rowScaling V.common.ballVolume V.common.haar V.common.isHaar τ hε hε1

/-- Explicit dimension-free rate constants obtained from the binomial dimension estimate. -/
def buresRateConstant : ℝ := 6 * Real.exp 1 ^ 2

def rightRateConstant : ℝ := 18 * Real.exp 1 ^ 2

/-- One positive accuracy threshold works for both pure-state losses and all m≥1. -/
def accuracyThreshold : ℝ := min (1 / 4)
  (min (SampleLowerBounds.accuracyThreshold buresRateConstant)
    (SampleLowerBounds.accuracyThreshold rightRateConstant))

theorem accuracyThreshold_pos : 0 < accuracyThreshold := by
  apply lt_min (by norm_num)
  exact lt_min (SampleLowerBounds.accuracyThreshold_pos (by unfold buresRateConstant; positivity))
    (SampleLowerBounds.accuracyThreshold_pos (by unfold rightRateConstant; positivity))

/-- Actual pure-state chiB sample lower bound, including the qubit case m=1. -/
theorem pure_bures_lower (hm : 0 < m) (V : BuresHaarInputs m)
    (P : SymmetricProjectorInput (StateIndex m) n) (A : Learner (StateIndex m) Ω n)
    {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ accuracyThreshold)
    (hA : A.BuresSuccess 1 (ENNReal.ofReal ε)) :
    (m : ℝ) * Real.sqrt m / (18 * Real.exp 1 ^ 2 * ε) ≤ n := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hp := bures_power_constraint hm V P A hε (hsmall.trans (min_le_left _ _)) hA
  have hb := PureLowerArithmetic.linear_base_lower n m hm
    (by positivity : 0 ≤ 6 * Real.exp 1 * ε * Real.sqrt (1 / (m : ℝ))) hp
  have hrate : 2 / 3 ≤ buresRateConstant * ε * Real.sqrt (1 / (m : ℝ)) *
      (1 + (n : ℝ) / m) := by
    convert hb using 1
    unfold buresRateConstant
    field_simp
    ring
  have hsmall' : ε ≤ SampleLowerBounds.accuracyThreshold buresRateConstant :=
    (hsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
  have h := SampleLowerBounds.bures_collective
    (C := buresRateConstant) (r := 1) (s := (m : ℝ)) (n := (n : ℝ)) (S := 2 / 3)
    (by unfold buresRateConstant; positivity) (by norm_num) (by exact_mod_cast hm)
    hε hsmall' le_rfl (by simpa only [one_mul] using hrate)
  convert h using 1
  simp only [Real.sqrt_one, one_mul, buresRateConstant]
  field_simp
  ring

/-- Actual pure-state chiR sample lower bound, including m=1. -/
theorem pure_right_lower (hm : 0 < m) (V : RightHaarInputs m)
    (P : SymmetricProjectorInput (StateIndex m) n) (A : Learner (StateIndex m) Ω n)
    {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ accuracyThreshold)
    (hA : A.RightSuccess 1 (ENNReal.ofReal ε)) :
    (m : ℝ) ^ 2 / (54 * Real.exp 1 ^ 2 * ε ^ 2) ≤ n := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hp := right_power_constraint hm V P A hε (hsmall.trans (min_le_left _ _)) hA
  have hb := PureLowerArithmetic.linear_base_lower n m hm
    (by positivity : 0 ≤ 18 * Real.exp 1 * ε ^ 2 / (m : ℝ)) hp
  have hrate : 2 / 3 ≤ rightRateConstant * (1 * ε ^ 2 / (m : ℝ)) *
      (1 + (n : ℝ) / (1 * m)) := by
    convert hb using 1
    unfold rightRateConstant
    field_simp
    ring
  have hsmall' : ε ≤ SampleLowerBounds.accuracyThreshold rightRateConstant :=
    (hsmall.trans (min_le_right _ _)).trans (min_le_right _ _)
  have h := SampleLowerBounds.right_collective
    (C := rightRateConstant) (r := 1) (s := (m : ℝ)) (n := (n : ℝ)) (S := 2 / 3)
    (by unfold rightRateConstant; positivity) (by norm_num) (by exact_mod_cast hm)
    hε hsmall' le_rfl hrate
  convert h using 1
  simp only [rightRateConstant]
  field_simp
  ring

/-- The qubit chiB exception is closed directly by the pure tensor argument. -/
theorem qubit_bures_lower (V : BuresHaarInputs 1)
    (P : SymmetricProjectorInput (StateIndex 1) n) (A : Learner (StateIndex 1) Ω n)
    {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ accuracyThreshold)
    (hA : A.BuresSuccess 1 (ENNReal.ofReal ε)) :
    1 / (18 * Real.exp 1 ^ 2 * ε) ≤ n := by
  simpa only [Nat.cast_one, Real.sqrt_one, one_mul] using
    pure_bures_lower (by norm_num : 0 < 1) V P A hε hsmall hA

/-- The qubit chiR exception is closed with its squared-accuracy rate. -/
theorem qubit_right_lower (V : RightHaarInputs 1)
    (P : SymmetricProjectorInput (StateIndex 1) n) (A : Learner (StateIndex 1) Ω n)
    {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ accuracyThreshold)
    (hA : A.RightSuccess 1 (ENNReal.ofReal ε)) :
    1 / (54 * Real.exp 1 ^ 2 * ε ^ 2) ≤ n := by
  simpa only [Nat.cast_one, one_pow] using
    pure_right_lower (by norm_num : 0 < 1) V P A hε hsmall hA

end Paper26.PureCollectiveLowerBounds
