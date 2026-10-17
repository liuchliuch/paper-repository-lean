import Paper26.CollectiveLowerBounds
import Paper26.PureCollectiveLowerBounds
import Paper26.RankReduction

/-!
# Collective rates in every nontrivial dimension and rank

The actual rank-`r` learning promise is restricted to
`k = min r (d / 2)`. The graph argument handles `k * (d-k) ≥ 2`;
the remaining case is the actual pure qubit experiment. A single positive
constant and accuracy threshold work for both losses and all dimensions.

All external parameters below are the previously specified raw matrix,
Haar, smooth-prior, Sobolev and symmetric-tensor inputs. No field states
a successful volume, Fisher budget, success rate, or sample lower bound.
In particular no Sobolev input in real dimension two is requested for the
qubit branch.

The ambient space is explicitly `Fin k ⊕ Fin (d-k)`, whose cardinal is
proved to equal `d`. Transport to an arbitrary finite ambient index and
representation of a general operator-valued POVM by the dominated learner
model are separate issues; neither is asserted in this module.
-/

noncomputable section
open scoped ENNReal
open MeasureTheory

namespace Paper26.CollectiveMainLowerBounds

open QuantumModel CollectiveModel SymmetricSupport

/-- The raw geometric inputs, without a nonzero-rank typeclass in the
bundle's type. This permits stating the reduced-rank result before deriving
positivity of its rank. -/
structure RawVolumeInputs (k s : ℕ) where
  chart : ChartVolume.GraphChartInput
  truncation : HaarTruncation.TruncatedHaarInput
  properNull : ∀ [Nonempty (Fin k)],
    HaarTruncation.ProperSubspaceNullInput (Fin k ⊕ Fin s) (Fin k)
  metric : TailMass.BuresMetricInput (Fin k ⊕ Fin s)
  compression : TailMassBridges.RawCompressionInput (Fin k ⊕ Fin s) (Fintype.card (Fin k))
  lyapunov : TailConvexity.LyapunovPositivityInput (Fin s)
  brunnMinkowski : TailVolume.BrunnMinkowskiInput (Fin s) (Fin k)
  unitaryLebesgue : TailVolume.UnitaryLebesgueInput (Fin s) (Fin k)
  ballVolume : ScalarTailBall.EuclideanBallVolumeInput (Fin s) (Fin k)
  rowScaling : RightTailVolume.PositiveRowScalingInput (Fin s) (Fin k)
  haar : Measure (HaarTruncation.FrameSpace k s)
  isHaar : HaarFrames.IsHaarFrameDistribution haar

def RawVolumeInputs.toVolumeInputs {k s : ℕ} [NeZero k] (V : RawVolumeInputs k s) :
    CollectiveLowerBounds.VolumeInputs k s where
  chart := V.chart
  truncation := V.truncation
  properNull := V.properNull
  metric := V.metric
  compression := V.compression
  lyapunov := V.lyapunov
  brunnMinkowski := V.brunnMinkowski
  unitaryLebesgue := V.unitaryLebesgue
  ballVolume := V.ballVolume
  rowScaling := V.rowScaling
  haar := V.haar
  isHaar := V.isHaar

def RawVolumeInputs.toCommonPure {m : ℕ} (V : RawVolumeInputs 1 m) :
    PureCollectiveLowerBounds.CommonHaarInputs m where
  truncation := V.truncation
  properNull := V.properNull
  metric := V.metric
  compression := V.compression
  ballVolume := V.ballVolume
  haar := V.haar
  isHaar := V.isHaar

def RawVolumeInputs.toBuresPure {m : ℕ} (V : RawVolumeInputs 1 m) :
    PureCollectiveLowerBounds.BuresHaarInputs m where
  common := V.toCommonPure
  lyapunov := V.lyapunov
  brunnMinkowski := V.brunnMinkowski
  unitaryLebesgue := V.unitaryLebesgue

def RawVolumeInputs.toRightPure {m : ℕ} (V : RawVolumeInputs 1 m) :
    PureCollectiveLowerBounds.RightHaarInputs m where
  common := V.toCommonPure
  rowScaling := V.rowScaling

/-- The four generic analytic inputs used only in the graph branch. -/
structure AnalysisInputs (p : ℕ) where
  sobolev : H1PosteriorBound.TalentiH1SharpInput p
  coarse : H1PosteriorBound.TalentiCoarseInput p
  product : WeakPosteriorIdentity.WeakLocallyLipschitzProductInput p
  unique : WeakPosteriorIdentity.WeakDerivativeUniquenessInput p

/-- Restriction of an actual learning promise to a smaller rank class. -/
theorem learnsRank_mono {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] {n k r : ℕ} (A : Learner ι Ω n)
    (loss : Density ι → Density ι → ℝ≥0∞) (ε q : ℝ≥0∞)
    (hkr : k ≤ r) (hA : A.LearnsRank loss r ε q) :
    A.LearnsRank loss k ε q := by
  intro ρ hρ
  exact hA ρ (hρ.trans hkr)

/-- A common coefficient for the two chart and two qubit estimates. -/
def baseConstant (C : ℝ) : ℝ :=
  min (1 / (3 * CollectiveLowerBounds.buresRateConstant C))
    (min (1 / (3 * CollectiveLowerBounds.rightRateConstant C))
      (min (1 / (18 * Real.exp 1 ^ 2)) (1 / (54 * Real.exp 1 ^ 2))))

def sampleConstant (C : ℝ) : ℝ := baseConstant C / 32

def accuracyThreshold (C : ℝ) : ℝ :=
  min (CollectiveLowerBounds.accuracyThreshold C)
    PureCollectiveLowerBounds.accuracyThreshold

theorem baseConstant_pos {C : ℝ} (hC : 0 < C) : 0 < baseConstant C := by
  have hB := CollectiveLowerBounds.buresRateConstant_pos hC
  have hR := CollectiveLowerBounds.rightRateConstant_pos hC
  unfold baseConstant
  positivity

theorem sampleConstant_pos {C : ℝ} (hC : 0 < C) : 0 < sampleConstant C :=
  div_pos (baseConstant_pos hC) (by norm_num)

theorem accuracyThreshold_pos {C : ℝ} (hC : 0 < C) : 0 < accuracyThreshold C :=
  lt_min (CollectiveLowerBounds.accuracyThreshold_pos hC)
    PureCollectiveLowerBounds.accuracyThreshold_pos

theorem baseConstant_le_chart_bures (C : ℝ) :
    baseConstant C ≤ 1 / (3 * CollectiveLowerBounds.buresRateConstant C) :=
  min_le_left _ _

theorem baseConstant_le_chart_right (C : ℝ) :
    baseConstant C ≤ 1 / (3 * CollectiveLowerBounds.rightRateConstant C) :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem baseConstant_le_qubit_bures (C : ℝ) :
    baseConstant C ≤ 1 / (18 * Real.exp 1 ^ 2) :=
  (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))

theorem baseConstant_le_qubit_right (C : ℝ) :
    baseConstant C ≤ 1 / (54 * Real.exp 1 ^ 2) :=
  (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))

variable {k s n : ℕ} [NeZero k] {Ω : Type*} [MeasurableSpace Ω]

/-- Both graph and endpoint proofs give this one reduced Bures rate. -/
theorem reduced_bures (V : RawVolumeInputs k s) (hk : 0 < k) (hks : k ≤ s)
    (An : 2 ≤ k * s → AnalysisInputs (2 * k * s))
    (P : SymmetricProjectorInput (Fin k ⊕ Fin s) n)
    (A : Learner (Fin k ⊕ Fin s) Ω n)
    (G : GraphFisherBudget.GraphTangentInput) {C ε : ℝ} (hC : 0 < C)
    (N : GraphPrior.NZSmoothLocalPriorInput C) (hε : 0 < ε)
    (hsmall : ε ≤ accuracyThreshold C)
    (hA : A.BuresSuccess k (ENNReal.ofReal ε)) :
    baseConstant C * (Real.sqrt (k : ℝ) * s * Real.sqrt (s : ℝ) / ε) ≤ (n : ℝ) := by
  by_cases hprod : 2 ≤ k * s
  · let B := An hprod
    have hb := CollectiveLowerBounds.bures_collective A V.toVolumeInputs hk hks hprod
      B.sobolev B.coarse B.product B.unique G hC N hε
      (hsmall.trans (min_le_left _ _)) hA
    exact (mul_le_mul_of_nonneg_right (baseConstant_le_chart_bures C) (by positivity)).trans hb
  · have hs : 0 < s := hk.trans_le hks
    have hmul : k * s = 1 := by have hpos := Nat.mul_pos hk hs; omega
    obtain ⟨rfl, rfl⟩ := mul_eq_one.mp hmul
    have hb := PureCollectiveLowerBounds.qubit_bures_lower V.toBuresPure P A hε
      (hsmall.trans (min_le_right _ _)) hA
    simp only [Nat.cast_one, Real.sqrt_one, one_mul] at ⊢
    calc
      baseConstant C * (1 / ε) ≤ (1 / (18 * Real.exp 1 ^ 2)) * (1 / ε) :=
        mul_le_mul_of_nonneg_right (baseConstant_le_qubit_bures C) (by positivity)
      _ = 1 / (18 * Real.exp 1 ^ 2 * ε) := by ring
      _ ≤ (n : ℝ) := hb

/-- Both graph and endpoint proofs give this one reduced right-inverse rate. -/
theorem reduced_right (V : RawVolumeInputs k s) (hk : 0 < k) (hks : k ≤ s)
    (An : 2 ≤ k * s → AnalysisInputs (2 * k * s))
    (P : SymmetricProjectorInput (Fin k ⊕ Fin s) n)
    (A : Learner (Fin k ⊕ Fin s) Ω n)
    (G : GraphFisherBudget.GraphTangentInput) {C ε : ℝ} (hC : 0 < C)
    (N : GraphPrior.NZSmoothLocalPriorInput C) (hε : 0 < ε)
    (hsmall : ε ≤ accuracyThreshold C)
    (hA : A.RightSuccess k (ENNReal.ofReal ε)) :
    baseConstant C * ((s : ℝ) ^ 2 / ε ^ 2) ≤ (n : ℝ) := by
  by_cases hprod : 2 ≤ k * s
  · let B := An hprod
    have hb := CollectiveLowerBounds.right_collective A V.toVolumeInputs hk hks hprod
      B.sobolev B.coarse B.product B.unique G hC N hε
      (hsmall.trans (min_le_left _ _)) hA
    exact (mul_le_mul_of_nonneg_right (baseConstant_le_chart_right C) (by positivity)).trans hb
  · have hs : 0 < s := hk.trans_le hks
    have hmul : k * s = 1 := by have hpos := Nat.mul_pos hk hs; omega
    obtain ⟨rfl, rfl⟩ := mul_eq_one.mp hmul
    have hb := PureCollectiveLowerBounds.qubit_right_lower V.toRightPure P A hε
      (hsmall.trans (min_le_right _ _)) hA
    simp only [Nat.cast_one, one_pow] at ⊢
    calc
      baseConstant C * (1 / ε ^ 2) ≤ (1 / (54 * Real.exp 1 ^ 2)) * (1 / ε ^ 2) :=
        mul_le_mul_of_nonneg_right (baseConstant_le_qubit_right C) (by positivity)
      _ = 1 / (54 * Real.exp 1 ^ 2 * ε ^ 2) := by ring
      _ ≤ (n : ℝ) := hb

abbrev AmbientIndex (d r : ℕ) :=
  Fin (RankReduction.reducedRank d r) ⊕ Fin (d - RankReduction.reducedRank d r)

/-- The named ambient index has the original dimension, including all
nontrivial cases used below. -/
theorem ambient_card (d r : ℕ) : Fintype.card (AmbientIndex d r) = d := by
  simp only [AmbientIndex, Fintype.card_sum, Fintype.card_fin]
  unfold RankReduction.reducedRank
  omega

omit [NeZero k] in
/-- Theorem 1.2's collective Bures rate on the named ambient index, for
every `d ≥ 2` and `1 ≤ r ≤ d`, including the pure qubit endpoint. -/
theorem bures_collective {d r n : ℕ} (hd : 2 ≤ d) (hr : 1 ≤ r) (hrd : r ≤ d)
    (V : RawVolumeInputs (RankReduction.reducedRank d r) (d - RankReduction.reducedRank d r))
    (An : 2 ≤ RankReduction.reducedRank d r * (d - RankReduction.reducedRank d r) →
      AnalysisInputs (2 * RankReduction.reducedRank d r * (d - RankReduction.reducedRank d r)))
    (P : SymmetricProjectorInput (AmbientIndex d r) n)
    (A : Learner (AmbientIndex d r) Ω n)
    (G : GraphFisherBudget.GraphTangentInput) {C ε : ℝ} (hC : 0 < C)
    (N : GraphPrior.NZSmoothLocalPriorInput C) (hε : 0 < ε)
    (hsmall : ε ≤ accuracyThreshold C)
    (hA : A.BuresSuccess r (ENNReal.ofReal ε)) :
    sampleConstant C * (Real.sqrt (r : ℝ) * d * Real.sqrt (d : ℝ) / ε) ≤ (n : ℝ) := by
  obtain ⟨hk, hkr, hks, _, _⟩ := RankReduction.reducedRank_properties d r hd hr hrd
  letI : NeZero (RankReduction.reducedRank d r) := ⟨hk.ne'⟩
  have hlearn : A.BuresSuccess (RankReduction.reducedRank d r) (ENNReal.ofReal ε) :=
    learnsRank_mono A chiB _ _ hkr hA
  have hb := reduced_bures V hk hks An P A G hC N hε hsmall hlearn
  have hcmp := (RankReduction.compare_reduced_rates d r hd hr hrd).1
  calc
    sampleConstant C * (Real.sqrt (r : ℝ) * d * Real.sqrt (d : ℝ) / ε) ≤
        sampleConstant C *
          (32 * (Real.sqrt (RankReduction.reducedRank d r : ℝ) *
            ((d - RankReduction.reducedRank d r : ℕ) : ℝ) * Real.sqrt ((d - RankReduction.reducedRank d r : ℕ) : ℝ)) / ε) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hcmp hε.le)
        (sampleConstant_pos hC).le
    _ = baseConstant C * (Real.sqrt (RankReduction.reducedRank d r : ℝ) *
        ((d - RankReduction.reducedRank d r : ℕ) : ℝ) * Real.sqrt ((d - RankReduction.reducedRank d r : ℕ) : ℝ) / ε) := by
      unfold sampleConstant
      ring
    _ ≤ (n : ℝ) := hb

omit [NeZero k] in
/-- Theorem 1.2's collective right-inverse rate, with the same positive
universal coefficient and accuracy threshold as the Bures rate. -/
theorem right_collective {d r n : ℕ} (hd : 2 ≤ d) (hr : 1 ≤ r) (hrd : r ≤ d)
    (V : RawVolumeInputs (RankReduction.reducedRank d r) (d - RankReduction.reducedRank d r))
    (An : 2 ≤ RankReduction.reducedRank d r * (d - RankReduction.reducedRank d r) →
      AnalysisInputs (2 * RankReduction.reducedRank d r * (d - RankReduction.reducedRank d r)))
    (P : SymmetricProjectorInput (AmbientIndex d r) n)
    (A : Learner (AmbientIndex d r) Ω n)
    (G : GraphFisherBudget.GraphTangentInput) {C ε : ℝ} (hC : 0 < C)
    (N : GraphPrior.NZSmoothLocalPriorInput C) (hε : 0 < ε)
    (hsmall : ε ≤ accuracyThreshold C)
    (hA : A.RightSuccess r (ENNReal.ofReal ε)) :
    sampleConstant C * ((d : ℝ) ^ 2 / ε ^ 2) ≤ (n : ℝ) := by
  obtain ⟨hk, hkr, hks, _, _⟩ := RankReduction.reducedRank_properties d r hd hr hrd
  letI : NeZero (RankReduction.reducedRank d r) := ⟨hk.ne'⟩
  have hlearn : A.RightSuccess (RankReduction.reducedRank d r) (ENNReal.ofReal ε) :=
    learnsRank_mono A chiR _ _ hkr hA
  have hb := reduced_right V hk hks An P A G hC N hε hsmall hlearn
  have hcmp := (RankReduction.compare_reduced_rates d r hd hr hrd).2.2.1
  calc
    sampleConstant C * ((d : ℝ) ^ 2 / ε ^ 2) ≤ sampleConstant C *
        (32 * ((d - RankReduction.reducedRank d r : ℕ) : ℝ) ^ 2 / ε ^ 2) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hcmp (sq_nonneg ε))
        (sampleConstant_pos hC).le
    _ = baseConstant C * (((d - RankReduction.reducedRank d r : ℕ) : ℝ) ^ 2 / ε ^ 2) := by
      unfold sampleConstant
      ring
    _ ≤ (n : ℝ) := hb

end Paper26.CollectiveMainLowerBounds
