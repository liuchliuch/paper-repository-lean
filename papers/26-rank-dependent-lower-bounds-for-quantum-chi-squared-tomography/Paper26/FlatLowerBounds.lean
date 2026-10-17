import Paper26.AdaptiveOperatorModelTransport
import Paper26.PureMinimax

/-!
# Lower bounds under the flat-family-only learning promise

The input class consists exactly of normalized rank-r orthogonal projectors.
The graph-prior lower-success step uses this promise directly. It does not
assume uniform learning on every rank-at-most-r density. The pure qubit
endpoint follows because every rank-at-most-one density is a rank-one
projector. No prior-average success bound is a parameter.
-/

noncomputable section
open scoped BigOperators ComplexOrder ENNReal NNReal
open MeasureTheory Set

namespace Paper26.FlatLowerBounds
open QuantumModel H1PosteriorBound GraphExperiment CollectiveLowerBounds

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The genuine flat rank-r input class: density matrices P/r for actual
orthogonal projectors P of exactly rankr. -/
def FlatInputs (r : ℕ) : Set (Density ι) :=
  {ρ | ∃ P : OrthogonalProjector ι, P.matrix.rank = r ∧ ρ.matrix = (r : ℝ)⁻¹ • P.matrix}

def LearnsFlat {Y : Type*} [MeasurableSpace Y] {n : ℕ}
    (A : CollectiveModel.Learner ι Y n)
    (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε q : ℝ≥0∞) : Prop :=
  ∀ ρ : Density ι, ρ ∈ FlatInputs r →
    MeasurableSet (A.successSet loss ρ ε) ∧ q ≤ A.successProbability loss ρ ε

universe u
def AdaptiveLearnsFlat {Seed Ω : Type u} [MeasurableSpace Seed] [MeasurableSpace Ω] {n : ℕ}
    (A : AdaptiveModel.Learner ι Seed Ω n)
    (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε q : ℝ≥0∞) : Prop :=
  ∀ ρ : Density ι, ρ ∈ FlatInputs r →
    MeasurableSet (A.successSet loss ρ ε) ∧ q ≤ A.successProbability loss ρ ε

/-- The rank-one endpoint does not strengthen the source promise: all
rank-at-most-one densities are exactly normalized rank-one projectors. -/
theorem mem_flat_one_iff (ρ : Density ι) : ρ ∈ FlatInputs 1 ↔ ρ.matrix.rank ≤ 1 := by
  constructor
  · rintro ⟨P, hP, he⟩
    rw [he]
    simpa only [Nat.cast_one, inv_one, one_smul] using hP.le
  · intro hr
    have he : ρ.matrix.rank = 1 := by have hp := PureMinimax.density_rank_pos ρ; omega
    obtain ⟨P, hP, hρ⟩ := (PureMinimax.pure_density_iff_projector ρ).mp he
    exact ⟨P, hP, by simpa using hρ⟩

theorem learnsRank_one_of_flat {Y : Type*} [MeasurableSpace Y] {n : ℕ}
    (A : CollectiveModel.Learner ι Y n) (loss : Density ι → Density ι → ℝ≥0∞) (ε q : ℝ≥0∞)
    (hA : LearnsFlat A loss 1 ε q) : A.LearnsRank loss 1 ε q :=
  fun ρ hρ => hA ρ ((mem_flat_one_iff ρ).mpr hρ)

theorem embedded_learnsFlat_iff {Seed Ω : Type u} [MeasurableSpace Seed] [MeasurableSpace Ω]
    {n : ℕ} [Nonempty ι] (A : AdaptiveModel.Learner ι Seed Ω n)
    (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε q : ℝ≥0∞) :
    LearnsFlat (AdaptiveCollectiveEmbedding.collectiveLearner A) loss r ε q ↔
      AdaptiveLearnsFlat A loss r ε q := by
  unfold LearnsFlat AdaptiveLearnsFlat
  simp_rw [AdaptiveCollectiveEmbedding.collectiveLearner_successProbability]
  rfl

section Graph
variable {r s n : ℕ} [NeZero r] {Y : Type*} [MeasurableSpace Y]
  (A : CollectiveModel.Learner (StateIndex r s) Y n)

theorem graph_state_mem_flat (θ : Parameter r s) : state θ ∈ FlatInputs r := by
  let X := (MatrixCoordinates.coordinates r s).symm θ
  refine ⟨GraphFamily.projector X, ?_, ?_⟩
  · simpa only [Fintype.card_fin] using GraphFamily.projector_rank X
  · simp [state, GraphFamily.density_matrix, GraphFamily.projector_matrix, X]

/-- The actual flat promise supplies the prior-average success lower bound
on the graph prior. No promise on any nonflat density is used. -/
theorem learnsFlat_le_priorAverageSuccess
    (loss : Density (StateIndex r s) → Density (StateIndex r s) → ℝ≥0∞)
    (ε q : ℝ≥0∞) (h : WeakH1Root (2 * r * s)) (hh : h.mass univ = 1)
    (T : Set (Parameter r s)) (hT : ∀ θ ∉ T, h.root θ = 0)
    (hlearn : LearnsFlat A loss r ε q) :
    q ≤ priorAverageSuccess A h (successParameters A loss ε T) := by
  have hd : AEMeasurable (fun θ => ENNReal.ofReal (h.root θ ^ 2)) volume :=
    (h.root_aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal
  have hn : (∫⁻ θ, ENNReal.ofReal (h.root θ ^ 2)) = 1 := by
    simpa only [WeakH1Root.mass, Measure.restrict_univ] using hh
  have hq : (∫⁻ θ, ENNReal.ofReal (h.root θ ^ 2) * q) = q := by
    simp_rw [mul_comm _ q]
    rw [lintegral_const_mul'' q hd, hn, mul_one]
  calc
    q = ∫⁻ θ, ENNReal.ofReal (h.root θ ^ 2) * q := hq.symm
    _ ≤ priorAverageSuccess A h (successParameters A loss ε T) := by
      apply lintegral_mono
      intro θ
      by_cases hθ : θ ∈ T
      · have he : {y | θ ∈ successParameters A loss ε T y} = A.successSet loss (state θ) ε := by
          ext y
          simp only [successParameters, mem_setOf_eq, hθ, true_and, CollectiveModel.Learner.successSet]
        change ENNReal.ofReal (h.root θ ^ 2) * q ≤
          ENNReal.ofReal (h.root θ ^ 2) * A.outcomeMeasure (state θ)
            {y | θ ∈ successParameters A loss ε T y}
        rw [he]
        exact mul_le_mul_left' (hlearn (state θ) (graph_state_mem_flat θ)).2 _
      · simp only [hT θ hθ, zero_pow two_ne_zero, ENNReal.ofReal_zero, zero_mul]
        exact le_rfl

theorem bures_collective_chart
    (V : VolumeInputs r s) (hr : 0 < r) (hrs : r ≤ s) (hrs2 : 2 ≤ r * s)
    (Sob : TalentiH1SharpInput (2 * r * s)) (Coarse : TalentiCoarseInput (2 * r * s))
    (P : WeakPosteriorIdentity.WeakLocallyLipschitzProductInput (2 * r * s))
    (U : WeakPosteriorIdentity.WeakDerivativeUniquenessInput (2 * r * s))
    (G : GraphFisherBudget.GraphTangentInput) {C ε : ℝ} (hC : 0 < C)
    (N : GraphPrior.NZSmoothLocalPriorInput C) (hε : 0 < ε) (hε1 : ε ≤ 1 / 4)
    (hsmall : ε ≤ SampleLowerBounds.accuracyThreshold (buresRateConstant C))
    (hlearn : LearnsFlat A chiB r (ENNReal.ofReal ε) ((2 : ℝ≥0∞) / 3)) :
    (1 / (3 * buresRateConstant C)) *
      (Real.sqrt (r : ℝ) * s * Real.sqrt (s : ℝ) / ε) ≤ (n : ℝ) := by
  have hp : 3 ≤ 2 * r * s := by nlinarith
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hrsR : (r : ℝ) ≤ s := by exact_mod_cast hrs
  obtain ⟨w, hw⟩ := GraphPrior.exists_halfChart_prior hC N r s hr hrs
  have hu := bures_success_rate A V hp hr hrs Sob Coarse P U G hC w hw hε hε1
  have hl : (2 : ℝ≥0∞) / 3 ≤
      priorAverageSuccess A w.weakRoot (successSection A chiB ε) :=
    learnsFlat_le_priorAverageSuccess A chiB (ENNReal.ofReal ε) ((2 : ℝ≥0∞) / 3)
      w.weakRoot w.weakRoot_normalized (chartDomain r s) (prior_zero_off_chart w) hlearn
  have hrate0 : 0 ≤ buresRateConstant C := (buresRateConstant_pos hC).le
  have huR := ENNReal.toReal_mono ENNReal.ofReal_ne_top hu
  rw [ENNReal.toReal_ofReal (by positivity)] at huR
  exact SampleLowerBounds.bures_collective (buresRateConstant_pos hC) hrR hrsR hε hsmall
    (two_thirds_le_toReal hu hl) huR

/-- The collective right-inverse lower bound on actual flat graph states,
with no joint spectral-loss-measurability premise. -/
theorem right_collective_chart
    (V : VolumeInputs r s) (hr : 0 < r) (hrs : r ≤ s) (hrs2 : 2 ≤ r * s)
    (Sob : TalentiH1SharpInput (2 * r * s)) (Coarse : TalentiCoarseInput (2 * r * s))
    (P : WeakPosteriorIdentity.WeakLocallyLipschitzProductInput (2 * r * s))
    (U : WeakPosteriorIdentity.WeakDerivativeUniquenessInput (2 * r * s))
    (G : GraphFisherBudget.GraphTangentInput) {C ε : ℝ} (hC : 0 < C)
    (N : GraphPrior.NZSmoothLocalPriorInput C) (hε : 0 < ε) (hε1 : ε ≤ 1 / 4)
    (hsmall : ε ≤ SampleLowerBounds.accuracyThreshold (rightRateConstant C))
    (hlearn : LearnsFlat A chiR r (ENNReal.ofReal ε) ((2 : ℝ≥0∞) / 3)) :
    (1 / (3 * rightRateConstant C)) * ((s : ℝ) ^ 2 / ε ^ 2) ≤ (n : ℝ) := by
  have hp : 3 ≤ 2 * r * s := by nlinarith
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hrsR : (r : ℝ) ≤ s := by exact_mod_cast hrs
  obtain ⟨w, hw⟩ := GraphPrior.exists_halfChart_prior hC N r s hr hrs
  have hu := right_success_rate A V hp hr hrs Sob Coarse P U G hC w hw hε hε1
  have hl : (2 : ℝ≥0∞) / 3 ≤
      priorAverageSuccess A w.weakRoot (successSection A chiR ε) :=
    learnsFlat_le_priorAverageSuccess A chiR (ENNReal.ofReal ε) ((2 : ℝ≥0∞) / 3)
      w.weakRoot w.weakRoot_normalized (chartDomain r s) (prior_zero_off_chart w) hlearn
  have hrate0 : 0 ≤ rightRateConstant C := (rightRateConstant_pos hC).le
  have huR := ENNReal.toReal_mono ENNReal.ofReal_ne_top hu
  rw [ENNReal.toReal_ofReal (by positivity)] at huR
  exact SampleLowerBounds.right_collective (rightRateConstant_pos hC) hrR hrsR hε hsmall
    (two_thirds_le_toReal hu hl) huR

end Graph

section AdaptiveGraph
variable {r s n : ℕ} [NeZero r] {Seed Ω : Type u}
  [MeasurableSpace Seed] [MeasurableSpace Ω]
  (A : AdaptiveModel.Learner (StateIndex r s) Seed Ω n)

theorem bures_adaptive_chart
    (V : VolumeInputs r s) (hr : 0 < r) (hrs : r ≤ s) (hrs2 : 2 ≤ r * s)
    (Sob : TalentiH1SharpInput (2 * r * s)) (Coarse : TalentiCoarseInput (2 * r * s))
    (P : WeakPosteriorIdentity.WeakLocallyLipschitzProductInput (2 * r * s))
    (U : WeakPosteriorIdentity.WeakDerivativeUniquenessInput (2 * r * s))
    (G : GraphFisherBudget.GraphTangentInput) {C ε : ℝ} (hC : 0 < C)
    (N : GraphPrior.NZSmoothLocalPriorInput C) (hε : 0 < ε) (hε1 : ε ≤ 1 / 4)
    (hsmall : ε ≤ SampleLowerBounds.accuracyThreshold (buresRateConstant C))
    (hlearn : AdaptiveLearnsFlat A chiB r (ENNReal.ofReal ε) ((2 : ℝ≥0∞) / 3)) :
    (1 / (3 * buresRateConstant C)) *
      ((r : ℝ) * Real.sqrt (r : ℝ) * s * Real.sqrt (s : ℝ) / ε) ≤ (n : ℝ) := by
  have hp : 3 ≤ 2 * r * s := by nlinarith
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hrsR : (r : ℝ) ≤ s := by exact_mod_cast hrs
  obtain ⟨w, hw⟩ := GraphPrior.exists_halfChart_prior hC N r s hr hrs
  have hu := AdaptiveLowerBounds.bures_success_rate A V hp hr hrs Sob Coarse P U G hC w hw hε hε1
  have hl : (2 : ℝ≥0∞) / 3 ≤
      priorAverageSuccess (AdaptiveLowerBounds.embedded A) w.weakRoot (successSection (AdaptiveLowerBounds.embedded A) chiB ε) :=
    learnsFlat_le_priorAverageSuccess (AdaptiveLowerBounds.embedded A) chiB (ENNReal.ofReal ε) ((2 : ℝ≥0∞) / 3)
      w.weakRoot w.weakRoot_normalized (chartDomain r s) (prior_zero_off_chart w)
      ((embedded_learnsFlat_iff A _ _ _ _).2 hlearn)
  have hrate0 : 0 ≤ buresRateConstant C := (buresRateConstant_pos hC).le
  have huR := ENNReal.toReal_mono ENNReal.ofReal_ne_top hu
  rw [ENNReal.toReal_ofReal (by positivity)] at huR
  exact SampleLowerBounds.bures_one_copy (buresRateConstant_pos hC) hrR hrsR hε hsmall
    (two_thirds_le_toReal hu hl) huR

/-- The adaptive right-inverse lower bound on actual flat graph states,
with no joint spectral-loss-measurability premise. -/
theorem right_adaptive_chart
    (V : VolumeInputs r s) (hr : 0 < r) (hrs : r ≤ s) (hrs2 : 2 ≤ r * s)
    (Sob : TalentiH1SharpInput (2 * r * s)) (Coarse : TalentiCoarseInput (2 * r * s))
    (P : WeakPosteriorIdentity.WeakLocallyLipschitzProductInput (2 * r * s))
    (U : WeakPosteriorIdentity.WeakDerivativeUniquenessInput (2 * r * s))
    (G : GraphFisherBudget.GraphTangentInput) {C ε : ℝ} (hC : 0 < C)
    (N : GraphPrior.NZSmoothLocalPriorInput C) (hε : 0 < ε) (hε1 : ε ≤ 1 / 4)
    (hsmall : ε ≤ SampleLowerBounds.accuracyThreshold (rightRateConstant C))
    (hlearn : AdaptiveLearnsFlat A chiR r (ENNReal.ofReal ε) ((2 : ℝ≥0∞) / 3)) :
    (1 / (3 * rightRateConstant C)) * ((r : ℝ) * (s : ℝ) ^ 2 / ε ^ 2) ≤ (n : ℝ) := by
  have hp : 3 ≤ 2 * r * s := by nlinarith
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hrsR : (r : ℝ) ≤ s := by exact_mod_cast hrs
  obtain ⟨w, hw⟩ := GraphPrior.exists_halfChart_prior hC N r s hr hrs
  have hu := AdaptiveLowerBounds.right_success_rate A V hp hr hrs Sob Coarse P U G hC w hw hε hε1
  have hl : (2 : ℝ≥0∞) / 3 ≤
      priorAverageSuccess (AdaptiveLowerBounds.embedded A) w.weakRoot (successSection (AdaptiveLowerBounds.embedded A) chiR ε) :=
    learnsFlat_le_priorAverageSuccess (AdaptiveLowerBounds.embedded A) chiR (ENNReal.ofReal ε) ((2 : ℝ≥0∞) / 3)
      w.weakRoot w.weakRoot_normalized (chartDomain r s) (prior_zero_off_chart w)
      ((embedded_learnsFlat_iff A _ _ _ _).2 hlearn)
  have hrate0 : 0 ≤ rightRateConstant C := (rightRateConstant_pos hC).le
  have huR := ENNReal.toReal_mono ENNReal.ofReal_ne_top hu
  rw [ENNReal.toReal_ofReal (by positivity)] at huR
  exact SampleLowerBounds.right_one_copy (rightRateConstant_pos hC) hrR hrsR hε hsmall
    (two_thirds_le_toReal hu hl) huR

end AdaptiveGraph

section SplitAmbient
open CollectiveMainLowerBounds SymmetricSupport
variable {r s n : ℕ}

/-- The collective bures lower bound assuming only success on flat
rank-r inputs; the qubit branch uses exactly the same weaker promise. -/
theorem bures_collective_split {Y : Type*} [MeasurableSpace Y]
    (V : RawVolumeInputs r s) (hr : 0 < r) (hrs : r ≤ s)
    (An : 2 ≤ r * s → AnalysisInputs (2 * r * s))
    (Q : SymmetricProjectorInput (StateIndex r s) n) (A : CollectiveModel.Learner (StateIndex r s) Y n)
    (G : GraphFisherBudget.GraphTangentInput) {C ε : ℝ} (hC : 0 < C)
    (N : GraphPrior.NZSmoothLocalPriorInput C) (hε : 0 < ε)
    (hsmall : ε ≤ CollectiveMainLowerBounds.accuracyThreshold C)
    (hA : LearnsFlat A chiB r (ENNReal.ofReal ε) ((2 : ℝ≥0∞) / 3)) :
    baseConstant C * (Real.sqrt (r : ℝ) * s * Real.sqrt (s : ℝ) / ε) ≤ (n : ℝ) := by
  letI : NeZero r := ⟨hr.ne'⟩
  by_cases hprod : 2 ≤ r * s
  · let B := An hprod
    have hs := hsmall.trans (min_le_left _ _)
    have hb := bures_collective_chart A V.toVolumeInputs hr hrs hprod
      B.sobolev B.coarse B.product B.unique G hC N hε (hs.trans (min_le_left _ _))
      ((hs.trans (min_le_right _ _)).trans (min_le_left _ _)) hA
    exact (mul_le_mul_of_nonneg_right (baseConstant_le_chart_bures C) (by positivity)).trans hb
  · have hs : 0 < s := hr.trans_le hrs
    have hmul : r * s = 1 := by have hpos := Nat.mul_pos hr hs; omega
    obtain ⟨rfl, rfl⟩ := mul_eq_one.mp hmul
    have hb := PureCollectiveLowerBounds.qubit_bures_lower V.toBuresPure Q A hε
      (hsmall.trans (min_le_right _ _)) (learnsRank_one_of_flat A chiB _ _ hA)
    simp only [Nat.cast_one, Real.sqrt_one, one_mul] at ⊢
    calc
      baseConstant C * (1 / ε) ≤ (1 / (18 * Real.exp 1 ^ 2)) * (1 / ε) :=
        mul_le_mul_of_nonneg_right (baseConstant_le_qubit_bures C) (by positivity)
      _ = 1 / (18 * Real.exp 1 ^ 2 * ε) := by ring
      _ ≤ (n : ℝ) := hb

/-- The collective right lower bound assuming only success on flat
rank-r inputs; the qubit branch uses exactly the same weaker promise. -/
theorem right_collective_split {Y : Type*} [MeasurableSpace Y]
    (V : RawVolumeInputs r s) (hr : 0 < r) (hrs : r ≤ s)
    (An : 2 ≤ r * s → AnalysisInputs (2 * r * s))
    (Q : SymmetricProjectorInput (StateIndex r s) n) (A : CollectiveModel.Learner (StateIndex r s) Y n)
    (G : GraphFisherBudget.GraphTangentInput) {C ε : ℝ} (hC : 0 < C)
    (N : GraphPrior.NZSmoothLocalPriorInput C) (hε : 0 < ε)
    (hsmall : ε ≤ CollectiveMainLowerBounds.accuracyThreshold C)
    (hA : LearnsFlat A chiR r (ENNReal.ofReal ε) ((2 : ℝ≥0∞) / 3)) :
    baseConstant C * ((s : ℝ) ^ 2 / ε ^ 2) ≤ (n : ℝ) := by
  letI : NeZero r := ⟨hr.ne'⟩
  by_cases hprod : 2 ≤ r * s
  · let B := An hprod
    have hs := hsmall.trans (min_le_left _ _)
    have hb := right_collective_chart A V.toVolumeInputs hr hrs hprod
      B.sobolev B.coarse B.product B.unique G hC N hε (hs.trans (min_le_left _ _))
      ((hs.trans (min_le_right _ _)).trans (min_le_right _ _)) hA
    exact (mul_le_mul_of_nonneg_right (baseConstant_le_chart_right C) (by positivity)).trans hb
  · have hs : 0 < s := hr.trans_le hrs
    have hmul : r * s = 1 := by have hpos := Nat.mul_pos hr hs; omega
    obtain ⟨rfl, rfl⟩ := mul_eq_one.mp hmul
    have hb := PureCollectiveLowerBounds.qubit_right_lower V.toRightPure Q A hε
      (hsmall.trans (min_le_right _ _)) (learnsRank_one_of_flat A chiR _ _ hA)
    simp only [Nat.cast_one, one_pow] at ⊢
    calc
      baseConstant C * (1 / ε ^ 2) ≤ (1 / (54 * Real.exp 1 ^ 2)) * (1 / ε ^ 2) :=
        mul_le_mul_of_nonneg_right (baseConstant_le_qubit_right C) (by positivity)
      _ = 1 / (54 * Real.exp 1 ^ 2 * ε ^ 2) := by ring
      _ ≤ (n : ℝ) := hb

/-- The adaptive bures lower bound assuming only success on flat
rank-r inputs; the qubit branch uses exactly the same weaker promise. -/
theorem bures_adaptive_split {Seed Ω : Type u} [MeasurableSpace Seed] [MeasurableSpace Ω]
    (V : RawVolumeInputs r s) (hr : 0 < r) (hrs : r ≤ s)
    (An : 2 ≤ r * s → AnalysisInputs (2 * r * s))
    (Q : SymmetricProjectorInput (StateIndex r s) n) (A : AdaptiveModel.Learner (StateIndex r s) Seed Ω n)
    (G : GraphFisherBudget.GraphTangentInput) {C ε : ℝ} (hC : 0 < C)
    (N : GraphPrior.NZSmoothLocalPriorInput C) (hε : 0 < ε)
    (hsmall : ε ≤ CollectiveMainLowerBounds.accuracyThreshold C)
    (hA : AdaptiveLearnsFlat A chiB r (ENNReal.ofReal ε) ((2 : ℝ≥0∞) / 3)) :
    baseConstant C * ((r : ℝ) * Real.sqrt (r : ℝ) * s * Real.sqrt (s : ℝ) / ε) ≤ (n : ℝ) := by
  letI : NeZero r := ⟨hr.ne'⟩
  by_cases hprod : 2 ≤ r * s
  · let B := An hprod
    have hs := hsmall.trans (min_le_left _ _)
    have hb := bures_adaptive_chart A V.toVolumeInputs hr hrs hprod
      B.sobolev B.coarse B.product B.unique G hC N hε (hs.trans (min_le_left _ _))
      ((hs.trans (min_le_right _ _)).trans (min_le_left _ _)) hA
    exact (mul_le_mul_of_nonneg_right (baseConstant_le_chart_bures C) (by positivity)).trans hb
  · have hs : 0 < s := hr.trans_le hrs
    have hmul : r * s = 1 := by have hpos := Nat.mul_pos hr hs; omega
    obtain ⟨rfl, rfl⟩ := mul_eq_one.mp hmul
    have hb := PureCollectiveLowerBounds.qubit_bures_lower V.toBuresPure Q (AdaptiveCollectiveEmbedding.collectiveLearner A) hε
      (hsmall.trans (min_le_right _ _)) (learnsRank_one_of_flat (AdaptiveCollectiveEmbedding.collectiveLearner A) chiB _ _ ((embedded_learnsFlat_iff A _ _ _ _).2 hA))
    simp only [Nat.cast_one, Real.sqrt_one, one_mul] at ⊢
    calc
      baseConstant C * (1 / ε) ≤ (1 / (18 * Real.exp 1 ^ 2)) * (1 / ε) :=
        mul_le_mul_of_nonneg_right (baseConstant_le_qubit_bures C) (by positivity)
      _ = 1 / (18 * Real.exp 1 ^ 2 * ε) := by ring
      _ ≤ (n : ℝ) := hb

/-- The adaptive right lower bound assuming only success on flat
rank-r inputs; the qubit branch uses exactly the same weaker promise. -/
theorem right_adaptive_split {Seed Ω : Type u} [MeasurableSpace Seed] [MeasurableSpace Ω]
    (V : RawVolumeInputs r s) (hr : 0 < r) (hrs : r ≤ s)
    (An : 2 ≤ r * s → AnalysisInputs (2 * r * s))
    (Q : SymmetricProjectorInput (StateIndex r s) n) (A : AdaptiveModel.Learner (StateIndex r s) Seed Ω n)
    (G : GraphFisherBudget.GraphTangentInput) {C ε : ℝ} (hC : 0 < C)
    (N : GraphPrior.NZSmoothLocalPriorInput C) (hε : 0 < ε)
    (hsmall : ε ≤ CollectiveMainLowerBounds.accuracyThreshold C)
    (hA : AdaptiveLearnsFlat A chiR r (ENNReal.ofReal ε) ((2 : ℝ≥0∞) / 3)) :
    baseConstant C * ((r : ℝ) * (s : ℝ) ^ 2 / ε ^ 2) ≤ (n : ℝ) := by
  letI : NeZero r := ⟨hr.ne'⟩
  by_cases hprod : 2 ≤ r * s
  · let B := An hprod
    have hs := hsmall.trans (min_le_left _ _)
    have hb := right_adaptive_chart A V.toVolumeInputs hr hrs hprod
      B.sobolev B.coarse B.product B.unique G hC N hε (hs.trans (min_le_left _ _))
      ((hs.trans (min_le_right _ _)).trans (min_le_right _ _)) hA
    exact (mul_le_mul_of_nonneg_right (baseConstant_le_chart_right C) (by positivity)).trans hb
  · have hs : 0 < s := hr.trans_le hrs
    have hmul : r * s = 1 := by have hpos := Nat.mul_pos hr hs; omega
    obtain ⟨rfl, rfl⟩ := mul_eq_one.mp hmul
    have hb := PureCollectiveLowerBounds.qubit_right_lower V.toRightPure Q (AdaptiveCollectiveEmbedding.collectiveLearner A) hε
      (hsmall.trans (min_le_right _ _)) (learnsRank_one_of_flat (AdaptiveCollectiveEmbedding.collectiveLearner A) chiR _ _ ((embedded_learnsFlat_iff A _ _ _ _).2 hA))
    simp only [Nat.cast_one, one_pow, one_mul] at ⊢
    calc
      baseConstant C * (1 / ε ^ 2) ≤ (1 / (54 * Real.exp 1 ^ 2)) * (1 / ε ^ 2) :=
        mul_le_mul_of_nonneg_right (baseConstant_le_qubit_right C) (by positivity)
      _ = 1 / (54 * Real.exp 1 ^ 2 * ε ^ 2) := by ring
      _ ≤ (n : ℝ) := hb

end SplitAmbient

section CoordinateFlat
open CoordinateTransport
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Reindexing an actual orthogonal projector preserves its defining matrix
identities; this is used for the flat class itself. -/
def projector (e : ι ≃ κ) (P : OrthogonalProjector ι) : OrthogonalProjector κ where
  matrix := matrix e P.matrix
  hermitian := P.hermitian.submatrix e.symm
  idempotent := by rw [← matrix_mul, P.idempotent]

omit [DecidableEq ι] [DecidableEq κ] in
theorem mem_flat_density_forward (e : ι ≃ κ) (ρ : Density ι) (r : ℕ)
    (h : ρ ∈ FlatInputs r) : density e ρ ∈ FlatInputs r := by
  obtain ⟨P, hP, hρ⟩ := h
  refine ⟨projector e P, ?_, ?_⟩
  · simpa only [projector, matrix_rank] using hP
  · change matrix e ρ.matrix = (r : ℝ)⁻¹ • matrix e P.matrix
    rw [hρ]
    rfl

omit [DecidableEq ι] [DecidableEq κ] in
theorem mem_flat_density (e : ι ≃ κ) (ρ : Density ι) (r : ℕ) :
    density e ρ ∈ FlatInputs r ↔ ρ ∈ FlatInputs r := by
  constructor
  · intro h
    simpa only [density_symm] using mem_flat_density_forward e.symm (density e ρ) r h
  · exact mem_flat_density_forward e ρ r

theorem coordinate_learnsFlat_iff {Y : Type*} [MeasurableSpace Y] {n : ℕ}
    (e : ι ≃ κ) (A : CollectiveModel.Learner ι Y n)
    (Lι : Density ι → Density ι → ℝ≥0∞) (Lκ : Density κ → Density κ → ℝ≥0∞)
    (hL : ∀ ρ σ, Lκ (density e ρ) (density e σ) = Lι ρ σ) (r : ℕ) (ε q : ℝ≥0∞) :
    LearnsFlat (CoordinateTransport.learner e A) Lκ r ε q ↔ LearnsFlat A Lι r ε q := by
  constructor
  · intro h ρ hρ
    have hp := h (density e ρ) ((mem_flat_density e ρ r).mpr hρ)
    simpa only [CoordinateTransport.learner_successSet e A Lι Lκ hL,
      CoordinateTransport.learner_successProbability e A Lι Lκ hL] using hp
  · intro h ρ hρ
    obtain ⟨hm, hp⟩ := h (density e.symm ρ) ((mem_flat_density e.symm ρ r).mpr hρ)
    have hs := CoordinateTransport.learner_successSet e A Lι Lκ hL (density e.symm ρ) ε
    have hprob := CoordinateTransport.learner_successProbability e A Lι Lκ hL (density e.symm ρ) ε
    have hback : density e (density e.symm ρ) = ρ := density_symm e.symm ρ
    rw [hback] at hs hprob
    exact ⟨hs.symm ▸ hm, hprob.symm ▸ hp⟩

theorem coordinate_adaptiveLearnsFlat_iff {Seed Ω : Type u} [MeasurableSpace Seed]
    [MeasurableSpace Ω] {n : ℕ} (e : ι ≃ κ) (A : AdaptiveModel.Learner ι Seed Ω n)
    (Lι : Density ι → Density ι → ℝ≥0∞) (Lκ : Density κ → Density κ → ℝ≥0∞)
    (hL : ∀ ρ σ, Lκ (density e ρ) (density e σ) = Lι ρ σ) (r : ℕ) (ε q : ℝ≥0∞) :
    AdaptiveLearnsFlat (AdaptiveCoordinateTransport.learner e A) Lκ r ε q ↔
      AdaptiveLearnsFlat A Lι r ε q := by
  constructor
  · intro h ρ hρ
    have hp := h (density e ρ) ((mem_flat_density e ρ r).mpr hρ)
    simpa only [AdaptiveCoordinateTransport.learner_successSet e A Lι Lκ hL,
      AdaptiveCoordinateTransport.learner_successProbability e A Lι Lκ hL] using hp
  · intro h ρ hρ
    obtain ⟨hm, hp⟩ := h (density e.symm ρ) ((mem_flat_density e.symm ρ r).mpr hρ)
    have hs := AdaptiveCoordinateTransport.learner_successSet e A Lι Lκ hL (density e.symm ρ) ε
    have hprob := AdaptiveCoordinateTransport.learner_successProbability e A Lι Lκ hL (density e.symm ρ) ε
    have hback : density e (density e.symm ρ) = ρ := density_symm e.symm ρ
    rw [hback] at hs hprob
    exact ⟨hs.symm ▸ hm, hprob.symm ▸ hp⟩

end CoordinateFlat

section FullDimensionFlat
open CollectiveMainLowerBounds SymmetricSupport

/-- Exact dimension-preserving equivalence without reducing the promised
flat rank. The last sentence of Theorem1.2 uses k=r, s=d-r. -/
def flatAmbientEquiv {d r : ℕ} (hcard : Fintype.card ι = d) (hrd : r ≤ d) :
    ι ≃ StateIndex r (d - r) :=
  Fintype.equivOfCardEq (by simpa only [Fintype.card_sum, Fintype.card_fin, Nat.add_sub_of_le hrd] using hcard)

/-- Theorem1.2's flat-family-only collective bures lower bound.
No guarantee on any nonflat density is assumed. -/
theorem bures_collective_flat {Y : Type*} [MeasurableSpace Y] {d r n : ℕ}
    (hcard : Fintype.card ι = d) (hd : 2 ≤ d) (hr : 1 ≤ r) (hhalf : 2 * r ≤ d)
    (V : RawVolumeInputs r (d - r))
    (An : 2 ≤ r * (d - r) → AnalysisInputs (2 * r * (d - r)))
    (Q : SymmetricProjectorInput (StateIndex r (d - r)) n) (A : CollectiveModel.Learner ι Y n)
    (G : GraphFisherBudget.GraphTangentInput) {C ε : ℝ} (hC : 0 < C)
    (N : GraphPrior.NZSmoothLocalPriorInput C) (hε : 0 < ε)
    (hsmall : ε ≤ CollectiveMainLowerBounds.accuracyThreshold C)
    (hA : LearnsFlat A chiB r (ENNReal.ofReal ε) ((2 : ℝ≥0∞) / 3)) :
    sampleConstant C * (Real.sqrt (r : ℝ) * d * Real.sqrt (d : ℝ) / ε) ≤ (n : ℝ) := by
  have hrd : r ≤ d := by omega
  have hrs : r ≤ d - r := by omega
  let e : ι ≃ StateIndex r (d - r) := flatAmbientEquiv hcard hrd
  have hb := bures_collective_split V (by omega : 0 < r) hrs An Q (CoordinateTransport.learner e A)
    G hC N hε hsmall ((coordinate_learnsFlat_iff e A chiB chiB
      (CoordinateTransport.chiB_density e) r _ _).mpr hA)
  have hrR : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hdR : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hsR : (0 : ℝ) ≤ ((d - r : ℕ) : ℝ) := Nat.cast_nonneg _
  have hds : (d : ℝ) ≤ 2 * ((d - r : ℕ) : ℝ) := by exact_mod_cast (show d ≤ 2 * (d - r) by omega)
  have hcmp := (RankReduction.compare_rates hrR hdR hrR hsR (by linarith) hds).1
  calc
    sampleConstant C * (Real.sqrt (r : ℝ) * d * Real.sqrt (d : ℝ) / ε) ≤ sampleConstant C * (32 * (Real.sqrt (r : ℝ) * ((d - r : ℕ) : ℝ) * Real.sqrt ((d - r : ℕ) : ℝ) / ε)) := by
      apply mul_le_mul_of_nonneg_left _ (sampleConstant_pos hC).le
      convert div_le_div_of_nonneg_right hcmp hε.le using 1
      ring
    _ = baseConstant C * (Real.sqrt (r : ℝ) * ((d - r : ℕ) : ℝ) * Real.sqrt ((d - r : ℕ) : ℝ) / ε) := by unfold sampleConstant; ring
    _ ≤ (n : ℝ) := hb

/-- Theorem1.2's flat-family-only collective right lower bound.
No guarantee on any nonflat density is assumed. -/
theorem right_collective_flat {Y : Type*} [MeasurableSpace Y] {d r n : ℕ}
    (hcard : Fintype.card ι = d) (hd : 2 ≤ d) (hr : 1 ≤ r) (hhalf : 2 * r ≤ d)
    (V : RawVolumeInputs r (d - r))
    (An : 2 ≤ r * (d - r) → AnalysisInputs (2 * r * (d - r)))
    (Q : SymmetricProjectorInput (StateIndex r (d - r)) n) (A : CollectiveModel.Learner ι Y n)
    (G : GraphFisherBudget.GraphTangentInput) {C ε : ℝ} (hC : 0 < C)
    (N : GraphPrior.NZSmoothLocalPriorInput C) (hε : 0 < ε)
    (hsmall : ε ≤ CollectiveMainLowerBounds.accuracyThreshold C)
    (hA : LearnsFlat A chiR r (ENNReal.ofReal ε) ((2 : ℝ≥0∞) / 3)) :
    sampleConstant C * ((d : ℝ) ^ 2 / ε ^ 2) ≤ (n : ℝ) := by
  have hrd : r ≤ d := by omega
  have hrs : r ≤ d - r := by omega
  let e : ι ≃ StateIndex r (d - r) := flatAmbientEquiv hcard hrd
  have hb := right_collective_split V (by omega : 0 < r) hrs An Q (CoordinateTransport.learner e A)
    G hC N hε hsmall ((coordinate_learnsFlat_iff e A chiR chiR
      (CoordinateTransport.chiR_density e) r _ _).mpr hA)
  have hrR : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hdR : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hsR : (0 : ℝ) ≤ ((d - r : ℕ) : ℝ) := Nat.cast_nonneg _
  have hds : (d : ℝ) ≤ 2 * ((d - r : ℕ) : ℝ) := by exact_mod_cast (show d ≤ 2 * (d - r) by omega)
  have hcmp := (RankReduction.compare_rates hrR hdR hrR hsR (by linarith) hds).2.2.1
  calc
    sampleConstant C * ((d : ℝ) ^ 2 / ε ^ 2) ≤ sampleConstant C * (32 * (((d - r : ℕ) : ℝ) ^ 2 / ε ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (sampleConstant_pos hC).le
      convert div_le_div_of_nonneg_right hcmp (sq_nonneg ε) using 1
      ring
    _ = baseConstant C * (((d - r : ℕ) : ℝ) ^ 2 / ε ^ 2) := by unfold sampleConstant; ring
    _ ≤ (n : ℝ) := hb

/-- Theorem1.2's flat-family-only adaptive bures lower bound.
No guarantee on any nonflat density is assumed. -/
theorem bures_adaptive_flat {Seed Ω : Type u} [MeasurableSpace Seed] [MeasurableSpace Ω] {d r n : ℕ}
    (hcard : Fintype.card ι = d) (hd : 2 ≤ d) (hr : 1 ≤ r) (hhalf : 2 * r ≤ d)
    (V : RawVolumeInputs r (d - r))
    (An : 2 ≤ r * (d - r) → AnalysisInputs (2 * r * (d - r)))
    (Q : SymmetricProjectorInput (StateIndex r (d - r)) n) (A : AdaptiveModel.Learner ι Seed Ω n)
    (G : GraphFisherBudget.GraphTangentInput) {C ε : ℝ} (hC : 0 < C)
    (N : GraphPrior.NZSmoothLocalPriorInput C) (hε : 0 < ε)
    (hsmall : ε ≤ CollectiveMainLowerBounds.accuracyThreshold C)
    (hA : AdaptiveLearnsFlat A chiB r (ENNReal.ofReal ε) ((2 : ℝ≥0∞) / 3)) :
    sampleConstant C * ((r : ℝ) * Real.sqrt (r : ℝ) * d * Real.sqrt (d : ℝ) / ε) ≤ (n : ℝ) := by
  have hrd : r ≤ d := by omega
  have hrs : r ≤ d - r := by omega
  let e : ι ≃ StateIndex r (d - r) := flatAmbientEquiv hcard hrd
  have hb := bures_adaptive_split V (by omega : 0 < r) hrs An Q (AdaptiveCoordinateTransport.learner e A)
    G hC N hε hsmall ((coordinate_adaptiveLearnsFlat_iff e A chiB chiB
      (CoordinateTransport.chiB_density e) r _ _).mpr hA)
  have hrR : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hdR : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hsR : (0 : ℝ) ≤ ((d - r : ℕ) : ℝ) := Nat.cast_nonneg _
  have hds : (d : ℝ) ≤ 2 * ((d - r : ℕ) : ℝ) := by exact_mod_cast (show d ≤ 2 * (d - r) by omega)
  have hcmp := (RankReduction.compare_rates hrR hdR hrR hsR (by linarith) hds).2.1
  calc
    sampleConstant C * ((r : ℝ) * Real.sqrt (r : ℝ) * d * Real.sqrt (d : ℝ) / ε) ≤ sampleConstant C * (32 * ((r : ℝ) * Real.sqrt (r : ℝ) * ((d - r : ℕ) : ℝ) * Real.sqrt ((d - r : ℕ) : ℝ) / ε)) := by
      apply mul_le_mul_of_nonneg_left _ (sampleConstant_pos hC).le
      convert div_le_div_of_nonneg_right hcmp hε.le using 1
      ring
    _ = baseConstant C * ((r : ℝ) * Real.sqrt (r : ℝ) * ((d - r : ℕ) : ℝ) * Real.sqrt ((d - r : ℕ) : ℝ) / ε) := by unfold sampleConstant; ring
    _ ≤ (n : ℝ) := hb

/-- Theorem1.2's flat-family-only adaptive right lower bound.
No guarantee on any nonflat density is assumed. -/
theorem right_adaptive_flat {Seed Ω : Type u} [MeasurableSpace Seed] [MeasurableSpace Ω] {d r n : ℕ}
    (hcard : Fintype.card ι = d) (hd : 2 ≤ d) (hr : 1 ≤ r) (hhalf : 2 * r ≤ d)
    (V : RawVolumeInputs r (d - r))
    (An : 2 ≤ r * (d - r) → AnalysisInputs (2 * r * (d - r)))
    (Q : SymmetricProjectorInput (StateIndex r (d - r)) n) (A : AdaptiveModel.Learner ι Seed Ω n)
    (G : GraphFisherBudget.GraphTangentInput) {C ε : ℝ} (hC : 0 < C)
    (N : GraphPrior.NZSmoothLocalPriorInput C) (hε : 0 < ε)
    (hsmall : ε ≤ CollectiveMainLowerBounds.accuracyThreshold C)
    (hA : AdaptiveLearnsFlat A chiR r (ENNReal.ofReal ε) ((2 : ℝ≥0∞) / 3)) :
    sampleConstant C * ((r : ℝ) * (d : ℝ) ^ 2 / ε ^ 2) ≤ (n : ℝ) := by
  have hrd : r ≤ d := by omega
  have hrs : r ≤ d - r := by omega
  let e : ι ≃ StateIndex r (d - r) := flatAmbientEquiv hcard hrd
  have hb := right_adaptive_split V (by omega : 0 < r) hrs An Q (AdaptiveCoordinateTransport.learner e A)
    G hC N hε hsmall ((coordinate_adaptiveLearnsFlat_iff e A chiR chiR
      (CoordinateTransport.chiR_density e) r _ _).mpr hA)
  have hrR : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hdR : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hsR : (0 : ℝ) ≤ ((d - r : ℕ) : ℝ) := Nat.cast_nonneg _
  have hds : (d : ℝ) ≤ 2 * ((d - r : ℕ) : ℝ) := by exact_mod_cast (show d ≤ 2 * (d - r) by omega)
  have hcmp := (RankReduction.compare_rates hrR hdR hrR hsR (by linarith) hds).2.2.2
  calc
    sampleConstant C * ((r : ℝ) * (d : ℝ) ^ 2 / ε ^ 2) ≤ sampleConstant C * (32 * ((r : ℝ) * ((d - r : ℕ) : ℝ) ^ 2 / ε ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (sampleConstant_pos hC).le
      convert div_le_div_of_nonneg_right hcmp (sq_nonneg ε) using 1
      ring
    _ = baseConstant C * ((r : ℝ) * ((d - r : ℕ) : ℝ) ^ 2 / ε ^ 2) := by unfold sampleConstant; ring
    _ ≤ (n : ℝ) := hb

end FullDimensionFlat

section RawOperatorFlat
open CollectiveModel CollectiveMainLowerBounds SymmetricSupport

def OperatorLearnsFlat {Y : Type*} [MeasurableSpace Y] {n : ℕ}
    (A : OperatorPOVMTransport.OperatorLearner ι Y n)
    (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε q : ℝ≥0∞) : Prop :=
  ∀ ρ : Density ι, ρ ∈ FlatInputs r →
    MeasurableSet (A.successSet loss ρ ε) ∧ q ≤ A.successProbability loss ρ ε

def OperatorAdaptiveLearnsFlat {Seed Ω : Type u} [MeasurableSpace Seed] [MeasurableSpace Ω] {n : ℕ}
    (A : AdaptiveOperatorModelTransport.OperatorLearner ι Seed Ω n)
    (R : OperatorRadonNikodymInput ι Ω)
    (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε q : ℝ≥0∞) : Prop :=
  ∀ ρ : Density ι, ρ ∈ FlatInputs r →
    MeasurableSet (A.successSet loss ρ ε) ∧ q ≤ A.successProbability R loss ρ ε

theorem operator_toDominated_learnsFlat {Y : Type*} [MeasurableSpace Y] {n : ℕ}
    (A : OperatorPOVMTransport.OperatorLearner ι Y n)
    (R : OperatorRadonNikodymInput (Fin n → ι) Y)
    (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε q : ℝ≥0∞)
    (hA : OperatorLearnsFlat A loss r ε q) : LearnsFlat (A.toDominated R) loss r ε q := by
  intro ρ hρ
  obtain ⟨hm, hp⟩ := hA ρ hρ
  refine ⟨hm, ?_⟩
  rw [A.toDominated_successProbability R loss ρ ε hm]
  exact hp

theorem operatorAdaptive_toDominated_learnsFlat {Seed Ω : Type u}
    [MeasurableSpace Seed] [MeasurableSpace Ω] {n : ℕ} [Nonempty ι]
    (A : AdaptiveOperatorModelTransport.OperatorLearner ι Seed Ω n)
    (R : OperatorRadonNikodymInput ι Ω)
    (RJ : ∀ k : Fin n, OperatorRadonNikodymInput ι (AdaptiveModel.History Seed Ω k.val × Ω))
    (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε q : ℝ≥0∞)
    (hA : OperatorAdaptiveLearnsFlat A R loss r ε q) :
    AdaptiveLearnsFlat (A.toDominated R RJ) loss r ε q := by
  intro ρ hρ
  obtain ⟨hm, hp⟩ := hA ρ hρ
  refine ⟨hm, ?_⟩
  rw [A.toDominated_successProbability R RJ loss ρ ε]
  exact hp

/-- Flat-only collective bures main lower bound for an actual raw
operator measurement learner, with arbitrary measurable outcomes. -/
theorem bures_collective_operator_flat {Y : Type*} [MeasurableSpace Y] {d r n : ℕ}
    (hcard : Fintype.card ι = d) (hd : 2 ≤ d) (hr : 1 ≤ r) (hhalf : 2 * r ≤ d)
    (V : RawVolumeInputs r (d - r))
    (An : 2 ≤ r * (d - r) → AnalysisInputs (2 * r * (d - r)))
    (Q : SymmetricProjectorInput (StateIndex r (d - r)) n) (A : OperatorPOVMTransport.OperatorLearner ι Y n)
    (R : OperatorRadonNikodymInput (Fin n → ι) Y)
    (G : GraphFisherBudget.GraphTangentInput) {C ε : ℝ} (hC : 0 < C)
    (N : GraphPrior.NZSmoothLocalPriorInput C) (hε : 0 < ε)
    (hsmall : ε ≤ CollectiveMainLowerBounds.accuracyThreshold C)
    (hA : OperatorLearnsFlat A chiB r (ENNReal.ofReal ε) ((2 : ℝ≥0∞) / 3)) :
    sampleConstant C * (Real.sqrt (r : ℝ) * d * Real.sqrt (d : ℝ) / ε) ≤ (n : ℝ) := by
  exact bures_collective_flat hcard hd hr hhalf V An Q (A.toDominated R)
    G hC N hε hsmall (operator_toDominated_learnsFlat A R chiB r _ _ hA)

/-- Flat-only collective right main lower bound for an actual raw
operator measurement learner, with arbitrary measurable outcomes. -/
theorem right_collective_operator_flat {Y : Type*} [MeasurableSpace Y] {d r n : ℕ}
    (hcard : Fintype.card ι = d) (hd : 2 ≤ d) (hr : 1 ≤ r) (hhalf : 2 * r ≤ d)
    (V : RawVolumeInputs r (d - r))
    (An : 2 ≤ r * (d - r) → AnalysisInputs (2 * r * (d - r)))
    (Q : SymmetricProjectorInput (StateIndex r (d - r)) n) (A : OperatorPOVMTransport.OperatorLearner ι Y n)
    (R : OperatorRadonNikodymInput (Fin n → ι) Y)
    (G : GraphFisherBudget.GraphTangentInput) {C ε : ℝ} (hC : 0 < C)
    (N : GraphPrior.NZSmoothLocalPriorInput C) (hε : 0 < ε)
    (hsmall : ε ≤ CollectiveMainLowerBounds.accuracyThreshold C)
    (hA : OperatorLearnsFlat A chiR r (ENNReal.ofReal ε) ((2 : ℝ≥0∞) / 3)) :
    sampleConstant C * ((d : ℝ) ^ 2 / ε ^ 2) ≤ (n : ℝ) := by
  exact right_collective_flat hcard hd hr hhalf V An Q (A.toDominated R)
    G hC N hε hsmall (operator_toDominated_learnsFlat A R chiR r _ _ hA)

/-- Flat-only adaptive bures main lower bound for an actual raw
operator measurement learner, with arbitrary measurable outcomes. -/
theorem bures_adaptive_operator_flat {Seed Ω : Type u} [MeasurableSpace Seed] [MeasurableSpace Ω] {d r n : ℕ}
    (hcard : Fintype.card ι = d) (hd : 2 ≤ d) (hr : 1 ≤ r) (hhalf : 2 * r ≤ d)
    (V : RawVolumeInputs r (d - r))
    (An : 2 ≤ r * (d - r) → AnalysisInputs (2 * r * (d - r)))
    (Q : SymmetricProjectorInput (StateIndex r (d - r)) n) (A : AdaptiveOperatorModelTransport.OperatorLearner ι Seed Ω n)
    (R : OperatorRadonNikodymInput ι Ω)
    (RJ : ∀ k : Fin n, OperatorRadonNikodymInput ι (AdaptiveModel.History Seed Ω k.val × Ω))
    (G : GraphFisherBudget.GraphTangentInput) {C ε : ℝ} (hC : 0 < C)
    (N : GraphPrior.NZSmoothLocalPriorInput C) (hε : 0 < ε)
    (hsmall : ε ≤ CollectiveMainLowerBounds.accuracyThreshold C)
    (hA : OperatorAdaptiveLearnsFlat A R chiB r (ENNReal.ofReal ε) ((2 : ℝ≥0∞) / 3)) :
    sampleConstant C * ((r : ℝ) * Real.sqrt (r : ℝ) * d * Real.sqrt (d : ℝ) / ε) ≤ (n : ℝ) := by
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  exact bures_adaptive_flat hcard hd hr hhalf V An Q (A.toDominated R RJ)
    G hC N hε hsmall (operatorAdaptive_toDominated_learnsFlat A R RJ chiB r _ _ hA)

/-- Flat-only adaptive right main lower bound for an actual raw
operator measurement learner, with arbitrary measurable outcomes. -/
theorem right_adaptive_operator_flat {Seed Ω : Type u} [MeasurableSpace Seed] [MeasurableSpace Ω] {d r n : ℕ}
    (hcard : Fintype.card ι = d) (hd : 2 ≤ d) (hr : 1 ≤ r) (hhalf : 2 * r ≤ d)
    (V : RawVolumeInputs r (d - r))
    (An : 2 ≤ r * (d - r) → AnalysisInputs (2 * r * (d - r)))
    (Q : SymmetricProjectorInput (StateIndex r (d - r)) n) (A : AdaptiveOperatorModelTransport.OperatorLearner ι Seed Ω n)
    (R : OperatorRadonNikodymInput ι Ω)
    (RJ : ∀ k : Fin n, OperatorRadonNikodymInput ι (AdaptiveModel.History Seed Ω k.val × Ω))
    (G : GraphFisherBudget.GraphTangentInput) {C ε : ℝ} (hC : 0 < C)
    (N : GraphPrior.NZSmoothLocalPriorInput C) (hε : 0 < ε)
    (hsmall : ε ≤ CollectiveMainLowerBounds.accuracyThreshold C)
    (hA : OperatorAdaptiveLearnsFlat A R chiR r (ENNReal.ofReal ε) ((2 : ℝ≥0∞) / 3)) :
    sampleConstant C * ((r : ℝ) * (d : ℝ) ^ 2 / ε ^ 2) ≤ (n : ℝ) := by
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  exact right_adaptive_flat hcard hd hr hhalf V An Q (A.toDominated R RJ)
    G hC N hε hsmall (operatorAdaptive_toDominated_learnsFlat A R RJ chiR r _ _ hA)

end RawOperatorFlat

end Paper26.FlatLowerBounds
