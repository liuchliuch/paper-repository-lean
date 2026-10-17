import Paper26.OperatorMeasureConstruction
import Paper26.SourceCopyComplexity
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Repeated single-copy measurements as actual adaptive protocols

A fixed dominated one-copy POVM and a measurable estimator of a finite sample
tuple define an operational adaptive learner.  The seed is a point, and every
round measures one fresh copy with the given POVM.  The product sample law is
proved from the sequential Born kernels.  The associated raw operator protocol
has the same law for every ordinary fixed-space RN witness.
-/

noncomputable section

namespace Paper26.OneCopyProductProtocol

open MeasureTheory ProbabilityTheory QuantumModel ContinuousPOVM
open scoped ENNReal

universe u

variable {ι : Type*} {Ω : Type u} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace Ω]

/-- Separate the last observation from the preceding finite tuple. -/
def tupleSplit (n : ℕ) : (Fin (n + 1) → Ω) ≃ᵐ ((Fin n → Ω) × Ω) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Ω) (Fin.last n)).trans
    MeasurableEquiv.prodComm

/-- Chronological history tupleization, also for the empty history. -/
def historyTuple : (n : ℕ) →
    AdaptiveModel.History PUnit Ω n ≃ᵐ (Fin n → Ω)
  | 0 => MeasurableEquiv.ofUniqueOfUnique PUnit (Fin 0 → Ω)
  | n + 1 => ((historyTuple n).prodCongr (MeasurableEquiv.refl Ω)).trans
      (tupleSplit n).symm

theorem measurable_historyTuple (n : ℕ) : Measurable (historyTuple (Ω := Ω) n) :=
  (historyTuple n).measurable

/-- The new sample occupies the last tuple coordinate; the old tuple is the
initial segment selected by `tupleSplit`. -/
theorem historyTuple_succ_split (n : ℕ) (h : AdaptiveModel.History PUnit Ω n) (y : Ω) :
    tupleSplit n (historyTuple (n + 1) (h, y)) = (historyTuple n h, y) :=
  (tupleSplit n).apply_symm_apply _

theorem historyTuple_succ_last (n : ℕ) (h : AdaptiveModel.History PUnit Ω n) (y : Ω) :
    historyTuple (n + 1) (h, y) (Fin.last n) = y :=
  congrArg Prod.snd (historyTuple_succ_split n h y)

theorem tupleSplit_measurePreserving (ν : Measure Ω) [IsProbabilityMeasure ν] (n : ℕ) :
    MeasurePreserving (tupleSplit n) (Measure.pi (fun _ : Fin (n + 1) => ν))
      ((Measure.pi (fun _ : Fin n => ν)).prod ν) := by
  exact (Measure.measurePreserving_swap).comp
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) (Fin.last n))

/-- The actual one-copy step, with a history-independent POVM. -/
def constantStep (M : DominatedPOVM ι Ω) (H : Type*) [MeasurableSpace H] :
    AdaptiveModel.OneCopyStep ι H Ω where
  reference := Kernel.const H M.reference
  reference_sfinite := inferInstance
  effect := fun _ y => M.effect y
  entry_measurable := fun i j => (M.entry_measurable i j).comp measurable_snd
  positive_ae := fun _ => M.positive_ae
  entry_integrable := fun _ i j => M.entry_integrable i j
  total := fun _ i j => M.total i j

theorem constantStep_bornKernel (M : DominatedPOVM ι Ω) (H : Type*)
    [MeasurableSpace H] (ρ : Density ι) :
    (constantStep M H).bornKernel ρ = Kernel.const H (M.outcomeMeasure ρ) := by
  apply Kernel.ext
  intro h
  rw [AdaptiveModel.OneCopyStep.bornKernel_apply]
  rfl

/-- The genuine `N`-round adaptive learner: one fixed POVM per fresh copy. -/
def learner (M : DominatedPOVM ι Ω) {N : ℕ} (T : Estimator ι (Fin N → Ω)) :
    AdaptiveModel.Learner ι PUnit Ω N where
  seed := Measure.dirac PUnit.unit
  seed_probability := inferInstance
  step := fun k => constantStep M (AdaptiveModel.History PUnit Ω k.val)
  estimator := ⟨fun h => T.estimate (historyTuple N h),
    T.measurable_estimate.comp (measurable_historyTuple N)⟩

/-- The statistical product law consists of the actual single-copy Born laws. -/
def sampleMeasure (M : DominatedPOVM ι Ω) (ρ : Density ι) (N : ℕ) :
    Measure (Fin N → Ω) := Measure.pi (fun _ => M.outcomeMeasure ρ)

instance sampleMeasure_probability (M : DominatedPOVM ι Ω) (ρ : Density ι) (N : ℕ) :
    IsProbabilityMeasure (sampleMeasure M ρ N) := by
  unfold sampleMeasure
  infer_instance

/-- Every prefix, not just the final transcript, has the finite product law. -/
theorem historyTuple_prefixLaw (M : DominatedPOVM ι Ω) {N : ℕ}
    (T : Estimator ι (Fin N → Ω)) (ρ : Density ι) (k : ℕ) (hk : k ≤ N) :
    MeasurePreserving (historyTuple k) ((learner M T).prefixLaw ρ k hk)
      (sampleMeasure M ρ k) := by
  induction k with
  | zero =>
      refine ⟨measurable_historyTuple 0, ?_⟩
      change (Measure.dirac PUnit.unit).map (historyTuple 0) = _
      rw [Measure.map_dirac (measurable_historyTuple 0)]
      exact (Measure.pi_of_empty (fun _ : Fin 0 => M.outcomeMeasure ρ)
        (historyTuple 0 PUnit.unit)).symm
  | succ k ih =>
      change MeasurePreserving (historyTuple (k + 1))
        (((learner M T).prefixLaw ρ k (Nat.le_trans (Nat.le_succ k) hk)).compProd
          ((constantStep M (AdaptiveModel.History PUnit Ω k)).bornKernel ρ)) _
      rw [constantStep_bornKernel, Measure.compProd_const]
      exact (MeasurePreserving.symm (tupleSplit k)
        (tupleSplit_measurePreserving (M.outcomeMeasure ρ) k)).comp
          ((ih (Nat.le_trans (Nat.le_succ k) hk)).prod (MeasurePreserving.id _))

theorem historyTuple_transcriptLaw (M : DominatedPOVM ι Ω) {N : ℕ}
    (T : Estimator ι (Fin N → Ω)) (ρ : Density ι) :
    ((learner M T).transcriptLaw ρ).map (historyTuple N) = sampleMeasure M ρ N :=
  (historyTuple_prefixLaw M T ρ N (Nat.le_refl N)).map_eq

theorem outputLaw_eq (M : DominatedPOVM ι Ω) {N : ℕ}
    (T : Estimator ι (Fin N → Ω)) (ρ : Density ι) :
    (learner M T).outputLaw ρ = (sampleMeasure M ρ N).map T.estimate := by
  rw [← historyTuple_transcriptLaw M T ρ,
    Measure.map_map T.measurable_estimate (measurable_historyTuple N)]
  rfl

/-- The exact statistical success event of the tuple estimator. -/
def sampleSuccessSet {N : ℕ} (T : Estimator ι (Fin N → Ω))
    (loss : Density ι → Density ι → ℝ≥0∞) (ρ : Density ι) (ε : ℝ≥0∞) :
    Set (Fin N → Ω) := {z | loss ρ (T.estimate z) ≤ ε}

theorem sampleSuccessSet_measurable {N : ℕ} (T : Estimator ι (Fin N → Ω))
    (loss : Density ι → Density ι → ℝ≥0∞) (ρ : Density ι)
    (hLoss : Measurable (loss ρ)) (ε : ℝ≥0∞) :
    MeasurableSet (sampleSuccessSet T loss ρ ε) :=
  measurableSet_le (hLoss.comp T.measurable_estimate) measurable_const

theorem successProbability_eq (M : DominatedPOVM ι Ω) {N : ℕ}
    (T : Estimator ι (Fin N → Ω)) (loss : Density ι → Density ι → ℝ≥0∞)
    (ρ : Density ι) (ε : ℝ≥0∞)
    (hm : MeasurableSet (sampleSuccessSet T loss ρ ε)) :
    (learner M T).successProbability loss ρ ε =
      sampleMeasure M ρ N (sampleSuccessSet T loss ρ ε) := by
  rw [← historyTuple_transcriptLaw M T ρ,
    Measure.map_apply (measurable_historyTuple N) hm]
  rfl

/-- Exact equivalence with the statistical learning guarantee.  Event
measurability is transported in both directions by the history equivalence. -/
theorem learner_learnsRank_iff (M : DominatedPOVM ι Ω) {N : ℕ}
    (T : Estimator ι (Fin N → Ω)) (loss : Density ι → Density ι → ℝ≥0∞)
    (r : ℕ) (ε q : ℝ≥0∞) :
    (learner M T).LearnsRank loss r ε q ↔
      ∀ ρ : Density ι, ρ.matrix.rank ≤ r →
        MeasurableSet (sampleSuccessSet T loss ρ ε) ∧
          q ≤ sampleMeasure M ρ N (sampleSuccessSet T loss ρ ε) := by
  constructor
  · intro h ρ hr
    have hm : MeasurableSet (sampleSuccessSet T loss ρ ε) :=
      (historyTuple N).measurableSet_preimage.mp (h ρ hr).1
    exact ⟨hm, by simpa only [successProbability_eq M T loss ρ ε hm] using (h ρ hr).2⟩
  · intro h ρ hr
    refine ⟨(h ρ hr).1.preimage (measurable_historyTuple N), ?_⟩
    rw [successProbability_eq M T loss ρ ε (h ρ hr).1]
    exact (h ρ hr).2

/-- The raw operator-valued step associated with the same actual POVM. -/
def operatorStep (M : DominatedPOVM ι Ω) (H : Type*) [MeasurableSpace H] :
    AdaptiveOperatorModelTransport.OperatorStep ι H Ω where
  measurement := fun _ => OperatorMeasureConstruction.toOperatorPOVM M
  entry_measurable := fun _ _ _ _ => measurable_const

theorem operatorStep_bornKernel (M : DominatedPOVM ι Ω) (H : Type*)
    [MeasurableSpace H] (R : CollectiveModel.OperatorRadonNikodymInput ι Ω)
    (ρ : Density ι) :
    (operatorStep M H).bornKernel R ρ = (constantStep M H).bornKernel ρ := by
  rw [constantStep_bornKernel]
  apply Kernel.ext
  intro h
  exact (OperatorPOVMTransport.outcomeMeasure_eq_of_representation R
    (OperatorMeasureConstruction.toOperatorPOVM M) M
    (OperatorMeasureConstruction.represents M) ρ).symm

/-- An actual raw one-copy protocol, with precisely the same estimator. -/
def operatorLearner (M : DominatedPOVM ι Ω) {N : ℕ}
    (T : Estimator ι (Fin N → Ω)) :
    AdaptiveOperatorModelTransport.OperatorLearner ι PUnit Ω N where
  seed := (learner M T).seed
  seed_probability := (learner M T).seed_probability
  step := fun k => operatorStep M (AdaptiveModel.History PUnit Ω k.val)
  estimator := (learner M T).estimator

theorem operatorLearner_prefixLaw (M : DominatedPOVM ι Ω) {N : ℕ}
    (T : Estimator ι (Fin N → Ω)) (R : CollectiveModel.OperatorRadonNikodymInput ι Ω)
    (ρ : Density ι) (k : ℕ) (hk : k ≤ N) :
    (operatorLearner M T).prefixLaw R ρ k hk = (learner M T).prefixLaw ρ k hk := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change ((operatorLearner M T).prefixLaw R ρ k
        (Nat.le_trans (Nat.le_succ k) hk)).compProd
          ((operatorStep M (AdaptiveModel.History PUnit Ω k)).bornKernel R ρ) = _
      rw [ih _, operatorStep_bornKernel]
      rfl

theorem operatorLearner_transcriptLaw (M : DominatedPOVM ι Ω) {N : ℕ}
    (T : Estimator ι (Fin N → Ω)) (R : CollectiveModel.OperatorRadonNikodymInput ι Ω)
    (ρ : Density ι) :
    (operatorLearner M T).transcriptLaw R ρ = (learner M T).transcriptLaw ρ :=
  operatorLearner_prefixLaw M T R ρ N (Nat.le_refl N)

theorem operatorLearner_tupleLaw (M : DominatedPOVM ι Ω) {N : ℕ}
    (T : Estimator ι (Fin N → Ω)) (R : CollectiveModel.OperatorRadonNikodymInput ι Ω)
    (ρ : Density ι) :
    ((operatorLearner M T).transcriptLaw R ρ).map (historyTuple N) =
      sampleMeasure M ρ N := by
  rw [operatorLearner_transcriptLaw, historyTuple_transcriptLaw]

theorem operatorLearner_outputLaw (M : DominatedPOVM ι Ω) {N : ℕ}
    (T : Estimator ι (Fin N → Ω)) (R : CollectiveModel.OperatorRadonNikodymInput ι Ω)
    (ρ : Density ι) :
    (operatorLearner M T).outputLaw R ρ = (sampleMeasure M ρ N).map T.estimate := by
  change ((operatorLearner M T).transcriptLaw R ρ).map (learner M T).estimator.estimate = _
  rw [operatorLearner_transcriptLaw]
  exact outputLaw_eq M T ρ

theorem operatorLearner_successProbability (M : DominatedPOVM ι Ω) {N : ℕ}
    (T : Estimator ι (Fin N → Ω)) (R : CollectiveModel.OperatorRadonNikodymInput ι Ω)
    (loss : Density ι → Density ι → ℝ≥0∞) (ρ : Density ι) (ε : ℝ≥0∞)
    (hm : MeasurableSet (sampleSuccessSet T loss ρ ε)) :
    (operatorLearner M T).successProbability R loss ρ ε =
      sampleMeasure M ρ N (sampleSuccessSet T loss ρ ε) := by
  change (operatorLearner M T).transcriptLaw R ρ
    ((learner M T).successSet loss ρ ε) = _
  rw [operatorLearner_transcriptLaw]
  exact successProbability_eq M T loss ρ ε hm

/-- A proved statistical product guarantee becomes the source's operational
learning promise, with the same actual loss and unrestricted density output. -/
theorem operatorLearner_learnsRank (M : DominatedPOVM ι Ω) {N : ℕ}
    (T : Estimator ι (Fin N → Ω)) (R : CollectiveModel.OperatorRadonNikodymInput ι Ω)
    (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε q : ℝ≥0∞)
    (h : ∀ ρ : Density ι, ρ.matrix.rank ≤ r →
      MeasurableSet (sampleSuccessSet T loss ρ ε) ∧
        q ≤ sampleMeasure M ρ N (sampleSuccessSet T loss ρ ε)) :
    (operatorLearner M T).LearnsRank R loss r ε q := by
  intro ρ hr
  refine ⟨(h ρ hr).1.preimage (measurable_historyTuple N), ?_⟩
  rw [operatorLearner_successProbability M T R loss ρ ε (h ρ hr).1]
  exact (h ρ hr).2

theorem operatorLearner_learnsRank_iff (M : DominatedPOVM ι Ω) {N : ℕ}
    (T : Estimator ι (Fin N → Ω)) (R : CollectiveModel.OperatorRadonNikodymInput ι Ω)
    (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε q : ℝ≥0∞) :
    (operatorLearner M T).LearnsRank R loss r ε q ↔
      ∀ ρ : Density ι, ρ.matrix.rank ≤ r →
        MeasurableSet (sampleSuccessSet T loss ρ ε) ∧
          q ≤ sampleMeasure M ρ N (sampleSuccessSet T loss ρ ε) := by
  constructor
  · intro h ρ hr
    have hm : MeasurableSet (sampleSuccessSet T loss ρ ε) :=
      (historyTuple N).measurableSet_preimage.mp (h ρ hr).1
    exact ⟨hm, by
      simpa only [operatorLearner_successProbability M T R loss ρ ε hm] using (h ρ hr).2⟩
  · exact operatorLearner_learnsRank M T R loss r ε q

section SourceMinimum

variable {ι Ω : Type} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]

theorem adaptiveAchievable (M : DominatedPOVM ι Ω) {N : ℕ}
    (T : Estimator ι (Fin N → Ω)) (RN : SourceCopyComplexity.AllFixedOperatorRN ι)
    (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε : ℝ≥0∞)
    (h : ∀ ρ : Density ι, ρ.matrix.rank ≤ r →
      MeasurableSet (sampleSuccessSet T loss ρ ε) ∧
        (2 : ℝ≥0∞) / 3 ≤ sampleMeasure M ρ N (sampleSuccessSet T loss ρ ε)) :
    SourceCopyComplexity.adaptiveAchievable RN loss r ε N := by
  exact ⟨PUnit, Ω, inferInstance, inferInstance, operatorLearner M T,
    operatorLearner_learnsRank M T (RN Ω inferInstance) loss r ε _ h⟩

theorem Nonecopy_le (M : DominatedPOVM ι Ω) {N : ℕ}
    (T : Estimator ι (Fin N → Ω)) (RN : SourceCopyComplexity.AllFixedOperatorRN ι)
    (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε : ℝ≥0∞)
    (h : ∀ ρ : Density ι, ρ.matrix.rank ≤ r →
      MeasurableSet (sampleSuccessSet T loss ρ ε) ∧
        (2 : ℝ≥0∞) / 3 ≤ sampleMeasure M ρ N (sampleSuccessSet T loss ρ ε)) :
    SourceCopyComplexity.Nonecopy RN loss r ε ≤ (N : ℝ≥0∞) :=
  CopyComplexity.minimumCopies_le (adaptiveAchievable M T RN loss r ε h)

end SourceMinimum

end Paper26.OneCopyProductProtocol
