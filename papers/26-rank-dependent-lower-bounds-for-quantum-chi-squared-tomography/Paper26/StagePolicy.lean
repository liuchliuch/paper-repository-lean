import Paper26.OneCopyProductProtocol
import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# Sequential stage policies and first-failure bounds

The finite policy law is constructed by actual Markov-kernel composition.
Conditional failure bounds are needed only on histories on which every
previous stage succeeded.  No independence or joint success conclusion is
assumed.  Actual quantum one-copy protocols instantiate this construction
using their Born kernels, and have a native raw operator representation.
-/

noncomputable section

namespace Paper26.StagePolicy

open MeasureTheory ProbabilityTheory QuantumModel ContinuousPOVM AdaptiveModel
open scoped BigOperators ENNReal

universe u

variable {Seed Ω : Type u} [MeasurableSpace Seed] [MeasurableSpace Ω]

/-- A classical sequential policy; quantum instances below use actual Born
kernels.  Tagged finite unions can serve as the common outcome space. -/
structure Policy (Seed Ω : Type u) [MeasurableSpace Seed] [MeasurableSpace Ω]
    (L : ℕ) where
  seed : Measure Seed
  seed_probability : IsProbabilityMeasure seed
  transition : ∀ j : Fin L, Kernel (History Seed Ω j.val) Ω
  transition_markov : ∀ j, IsMarkovKernel (transition j)

namespace Policy

variable {L : ℕ} (P : Policy Seed Ω L)

instance seed_probability' : IsProbabilityMeasure P.seed := P.seed_probability
instance transition_markov' (j : Fin L) : IsMarkovKernel (P.transition j) :=
  P.transition_markov j

/-- The actual sequential law, consuming one supplied stage kernel at each
successor.  These are stages, with no implicit assertion of copy count. -/
def prefixLaw : (k : ℕ) → k ≤ L → Measure (History Seed Ω k)
  | 0, _ => P.seed
  | k + 1, hk => (prefixLaw k (Nat.le_trans (Nat.le_succ k) hk)).compProd
      (P.transition ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩)

instance prefixLaw_probability (k : ℕ) (hk : k ≤ L) :
    IsProbabilityMeasure (P.prefixLaw k hk) := by
  induction k with
  | zero => exact P.seed_probability
  | succ k ih =>
      change IsProbabilityMeasure
        ((P.prefixLaw k (Nat.le_trans (Nat.le_succ k) hk)).compProd
          (P.transition ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩))
      letI := ih (Nat.le_trans (Nat.le_succ k) hk)
      letI := P.transition_markov ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      infer_instance

def transcriptLaw : Measure (History Seed Ω L) := P.prefixLaw L (Nat.le_refl L)

instance transcriptLaw_probability : IsProbabilityMeasure P.transcriptLaw :=
  P.prefixLaw_probability L _

end Policy

/-- `good k` tests the newly completed stage on the entire history including
its outcome.  The values beyond the finite horizon are immaterial. -/
def goodPrefix (good : ∀ k : ℕ, Set (History Seed Ω (k + 1))) :
    (k : ℕ) → Set (History Seed Ω k)
  | 0 => Set.univ
  | k + 1 => Prod.fst ⁻¹' goodPrefix good k ∩ good k

theorem goodPrefix_measurable (good : ∀ k : ℕ, Set (History Seed Ω (k + 1)))
    (hg : ∀ k, MeasurableSet (good k)) (k : ℕ) :
    MeasurableSet (goodPrefix good k) := by
  induction k with
  | zero => exact MeasurableSet.univ
  | succ k ih => exact (ih.preimage measurable_fst).inter (hg k)

/-- First failure at this stage, with every previous stage successful. -/
def firstFailure (good : ∀ k : ℕ, Set (History Seed Ω (k + 1))) (k : ℕ) :
    Set (History Seed Ω (k + 1)) :=
  Prod.fst ⁻¹' goodPrefix good k ∩ (good k)ᶜ

theorem firstFailure_measurable (good : ∀ k : ℕ, Set (History Seed Ω (k + 1)))
    (hg : ∀ k, MeasurableSet (good k)) (k : ℕ) :
    MeasurableSet (firstFailure good k) :=
  ((goodPrefix_measurable good hg k).preimage measurable_fst).inter (hg k).compl

namespace Policy

variable {L : ℕ} (P : Policy Seed Ω L)
  (good : ∀ k : ℕ, Set (History Seed Ω (k + 1)))
  (hg : ∀ k, MeasurableSet (good k)) (δ : ℕ → ℝ≥0∞)

include hg

/-- A genuine conditional bound only on previously successful histories
controls the probability of the first failure. -/
theorem firstFailure_le
    (hc : ∀ k (hk : k < L) h, h ∈ goodPrefix good k →
      P.transition ⟨k, hk⟩ h {y | (h, y) ∉ good k} ≤ δ k)
    (k : ℕ) (hk : k + 1 ≤ L) :
    P.prefixLaw (k + 1) hk (firstFailure good k) ≤ δ k := by
  letI := P.transition_markov ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
  change ((P.prefixLaw k (Nat.le_trans (Nat.le_succ k) hk)).compProd
    (P.transition ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩)) _ ≤ _
  rw [Measure.compProd_apply (firstFailure_measurable good hg k)]
  calc
    _ ≤ ∫⁻ _h, δ k ∂P.prefixLaw k (Nat.le_trans (Nat.le_succ k) hk) := by
      apply lintegral_mono
      intro h
      dsimp only
      by_cases hh : h ∈ goodPrefix good k
      · have he : Prod.mk h ⁻¹' firstFailure good k = {y | (h, y) ∉ good k} := by
          ext y
          simp [firstFailure, hh]
        rw [he]
        exact hc k _ h hh
      · have he : Prod.mk h ⁻¹' firstFailure good k = ∅ := by
          ext y
          simp [firstFailure, hh]
        rw [he, measure_empty]
        exact bot_le
    _ = δ k := by rw [lintegral_const, measure_univ, mul_one]

theorem badPrefix_succ_le
    (hc : ∀ k (hk : k < L) h, h ∈ goodPrefix good k →
      P.transition ⟨k, hk⟩ h {y | (h, y) ∉ good k} ≤ δ k)
    (k : ℕ) (hk : k + 1 ≤ L) :
    P.prefixLaw (k + 1) hk (goodPrefix good (k + 1))ᶜ ≤
      P.prefixLaw k (Nat.le_trans (Nat.le_succ k) hk) (goodPrefix good k)ᶜ + δ k := by
  letI := P.transition_markov ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
  have he : (goodPrefix good (k + 1))ᶜ =
      Prod.fst ⁻¹' (goodPrefix good k)ᶜ ∪ firstFailure good k := by
    ext z
    simp only [goodPrefix, firstFailure, Set.mem_compl_iff, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_union]
    tauto
  have hf : P.prefixLaw (k + 1) hk (Prod.fst ⁻¹' (goodPrefix good k)ᶜ) =
      P.prefixLaw k (Nat.le_trans (Nat.le_succ k) hk) (goodPrefix good k)ᶜ := by
    change ((P.prefixLaw k (Nat.le_trans (Nat.le_succ k) hk)).compProd
      (P.transition ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩))
        (Prod.fst ⁻¹' (goodPrefix good k)ᶜ) = _
    rw [← Measure.fst_apply (goodPrefix_measurable good hg k).compl]
    rw [Measure.fst_compProd]
  rw [he]
  exact (measure_union_le _ _).trans
    (add_le_add (le_of_eq hf) (P.firstFailure_le good hg δ hc k hk))

/-- The finite first-failure union bound, with no independence assumption. -/
theorem badPrefix_le
    (hc : ∀ k (hk : k < L) h, h ∈ goodPrefix good k →
      P.transition ⟨k, hk⟩ h {y | (h, y) ∉ good k} ≤ δ k)
    (k : ℕ) (hk : k ≤ L) :
    P.prefixLaw k hk (goodPrefix good k)ᶜ ≤ ∑ j ∈ Finset.range k, δ j := by
  induction k with
  | zero => simp [goodPrefix]
  | succ k ih =>
      rw [Finset.sum_range_succ]
      exact (P.badPrefix_succ_le good hg δ hc k hk).trans
        (add_le_add (ih _) le_rfl)

theorem allGood_probability_ge
    (hc : ∀ k (hk : k < L) h, h ∈ goodPrefix good k →
      P.transition ⟨k, hk⟩ h {y | (h, y) ∉ good k} ≤ δ k) :
    1 - (∑ j ∈ Finset.range L, δ j) ≤ P.transcriptLaw (goodPrefix good L) := by
  have hb := P.badPrefix_le good hg δ hc L (Nat.le_refl L)
  have he := measure_add_measure_compl (μ := P.transcriptLaw)
    (goodPrefix_measurable good hg L)
  rw [measure_univ] at he
  apply tsub_le_iff_right.mpr
  calc
    1 = P.transcriptLaw (goodPrefix good L) +
        P.transcriptLaw (goodPrefix good L)ᶜ := he.symm
    _ ≤ P.transcriptLaw (goodPrefix good L) + (∑ j ∈ Finset.range L, δ j) :=
      add_le_add_left hb _

/-- Any actual success event containing every all-good transcript inherits
the same probability guarantee. -/
theorem success_probability_ge
    (hc : ∀ k (hk : k < L) h, h ∈ goodPrefix good k →
      P.transition ⟨k, hk⟩ h {y | (h, y) ∉ good k} ≤ δ k)
    (S : Set (History Seed Ω L)) (hs : goodPrefix good L ⊆ S) :
    1 - (∑ j ∈ Finset.range L, δ j) ≤ P.transcriptLaw S :=
  (P.allGood_probability_ge good hg δ hc).trans (measure_mono hs)

theorem allGood_probability_ge_of_budget
    (hc : ∀ k (hk : k < L) h, h ∈ goodPrefix good k →
      P.transition ⟨k, hk⟩ h {y | (h, y) ∉ good k} ≤ δ k)
    (totalFailure : ℝ≥0∞) (hb : (∑ j ∈ Finset.range L, δ j) ≤ totalFailure) :
    1 - totalFailure ≤ P.transcriptLaw (goodPrefix good L) :=
  (tsub_le_tsub_left hb 1).trans (P.allGood_probability_ge good hg δ hc)

end Policy

section Quantum

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ℕ}

/-- Actual quantum kernels instantiate the policy without any assumed
statistical law or independence conclusion. -/
def ofLearner (A : AdaptiveModel.Learner ι Seed Ω L) (ρ : Density ι) :
    Policy Seed Ω L where
  seed := A.seed
  seed_probability := A.seed_probability
  transition := fun j => (A.step j).bornKernel ρ
  transition_markov := fun _ => inferInstance

theorem ofLearner_prefixLaw (A : AdaptiveModel.Learner ι Seed Ω L) (ρ : Density ι)
    (k : ℕ) (hk : k ≤ L) : (ofLearner A ρ).prefixLaw k hk = A.prefixLaw ρ k hk := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change ((ofLearner A ρ).prefixLaw k
        (Nat.le_trans (Nat.le_succ k) hk)).compProd _ = _
      rw [ih _]
      rfl

theorem learner_allGood_probability_ge (A : AdaptiveModel.Learner ι Seed Ω L)
    (ρ : Density ι) (good : ∀ k : ℕ, Set (History Seed Ω (k + 1)))
    (hg : ∀ k, MeasurableSet (good k)) (δ : ℕ → ℝ≥0∞)
    (hc : ∀ k (hk : k < L) h, h ∈ goodPrefix good k →
      (A.step ⟨k, hk⟩).bornKernel ρ h {y | (h, y) ∉ good k} ≤ δ k) :
    1 - (∑ j ∈ Finset.range L, δ j) ≤ A.transcriptLaw ρ (goodPrefix good L) := by
  have h := (ofLearner A ρ).allGood_probability_ge good hg δ hc
  simpa only [Policy.transcriptLaw, ofLearner_prefixLaw, AdaptiveModel.Learner.transcriptLaw]
    using h

end Quantum

section RawRepresentation

variable {ι H : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace H]

/-- At each fixed history, normalize the reference by the actual uniform
state Born law.  The effects retain their actual Born transition kernel. -/
def conditionalPOVM (M : OneCopyStep ι H Ω) (h : H) : DominatedPOVM ι Ω where
  reference := M.normalize.reference h
  reference_finite := inferInstance
  effect := M.normalize.effect h
  entry_measurable := fun i j => Measurable.of_uncurry_left
    (f := fun h y => M.normalizedEffect h y i j)
    (M.normalizedEffect_entry_measurable i j) (x := h)
  positive_ae := M.normalize.positive_ae h
  entry_integrable := M.normalize.entry_integrable h
  total := M.normalize.total h

theorem conditionalPOVM_outcomeMeasure (M : OneCopyStep ι H Ω)
    (h : H) (ρ : Density ι) :
    (conditionalPOVM M h).outcomeMeasure ρ = M.bornKernel ρ h := by
  rw [← M.normalize_bornKernel ρ, OneCopyStep.bornKernel_apply]
  rfl

/-- Native reverse transport from a jointly measurable quantum effect
kernel to a measurable family of actual operator POVMs. -/
def operatorStep (M : OneCopyStep ι H Ω) :
    AdaptiveOperatorModelTransport.OperatorStep ι H Ω where
  measurement := fun h => OperatorMeasureConstruction.toOperatorPOVM (conditionalPOVM M h)
  entry_measurable := by
    intro S hS i j
    have hm : Measurable (fun z : H × Ω =>
        S.indicator (fun y => M.normalize.effect z.1 y i j) z.2) := by
      exact (M.normalize.entry_measurable i j).piecewise
        (hS.preimage measurable_snd) measurable_const
    have hi := hm.stronglyMeasurable.integral_kernel_prod_right'
      (κ := M.normalize.reference)
    simpa only [OperatorMeasureConstruction.toOperatorPOVM, conditionalPOVM,
      integral_indicator hS] using hi.measurable

theorem operatorStep_bornKernel (M : OneCopyStep ι H Ω)
    (R : CollectiveModel.OperatorRadonNikodymInput ι Ω) (ρ : Density ι) :
    (operatorStep M).bornKernel R ρ = M.bornKernel ρ := by
  apply Kernel.ext
  intro h
  calc
    _ = (conditionalPOVM M h).outcomeMeasure ρ :=
      (OperatorPOVMTransport.outcomeMeasure_eq_of_representation R
        (OperatorMeasureConstruction.toOperatorPOVM (conditionalPOVM M h))
        (conditionalPOVM M h) (OperatorMeasureConstruction.represents _) ρ).symm
    _ = M.normalize.bornKernel ρ h := by
      rw [OneCopyStep.bornKernel_apply]
      rfl
    _ = M.bornKernel ρ h := by rw [M.normalize_bornKernel]

variable {N : ℕ}

/-- Every genuine dominated one-copy protocol has a raw operator protocol
with exactly the same seed, copy count, estimator and actual transcript law. -/
def operatorLearner (A : AdaptiveModel.Learner ι Seed Ω N) :
    AdaptiveOperatorModelTransport.OperatorLearner ι Seed Ω N where
  seed := A.seed
  seed_probability := A.seed_probability
  step := fun j => operatorStep (A.step j)
  estimator := A.estimator

theorem operatorLearner_prefixLaw (A : AdaptiveModel.Learner ι Seed Ω N)
    (R : CollectiveModel.OperatorRadonNikodymInput ι Ω) (ρ : Density ι)
    (k : ℕ) (hk : k ≤ N) :
    (operatorLearner A).prefixLaw R ρ k hk = A.prefixLaw ρ k hk := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change ((operatorLearner A).prefixLaw R ρ k
        (Nat.le_trans (Nat.le_succ k) hk)).compProd
          ((operatorStep (A.step ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩)).bornKernel
            R ρ) = _
      rw [ih _, operatorStep_bornKernel]
      rfl

theorem operatorLearner_transcriptLaw (A : AdaptiveModel.Learner ι Seed Ω N)
    (R : CollectiveModel.OperatorRadonNikodymInput ι Ω) (ρ : Density ι) :
    (operatorLearner A).transcriptLaw R ρ = A.transcriptLaw ρ :=
  operatorLearner_prefixLaw A R ρ N (Nat.le_refl N)

theorem operatorLearner_successProbability (A : AdaptiveModel.Learner ι Seed Ω N)
    (R : CollectiveModel.OperatorRadonNikodymInput ι Ω)
    (loss : Density ι → Density ι → ℝ≥0∞) (ρ : Density ι) (ε : ℝ≥0∞) :
    (operatorLearner A).successProbability R loss ρ ε = A.successProbability loss ρ ε := by
  change (operatorLearner A).transcriptLaw R ρ (A.successSet loss ρ ε) = _
  rw [operatorLearner_transcriptLaw]
  rfl

theorem operatorLearner_learnsRank_iff (A : AdaptiveModel.Learner ι Seed Ω N)
    (R : CollectiveModel.OperatorRadonNikodymInput ι Ω)
    (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε q : ℝ≥0∞) :
    (operatorLearner A).LearnsRank R loss r ε q ↔ A.LearnsRank loss r ε q := by
  unfold AdaptiveOperatorModelTransport.OperatorLearner.LearnsRank
    AdaptiveModel.Learner.LearnsRank
  simp only [operatorLearner_successProbability]
  rfl

end RawRepresentation

section ConditionalProducts

variable {H : Type*} [MeasurableSpace H]

/-- Repeated draws from a history-indexed kernel, with that history frozen
during the block.  This is constructed by sequential kernel composition,
followed by appending the new observation to the sample tuple. -/
def tupleKernel (κ : Kernel H Ω) : (N : ℕ) → Kernel H (Fin N → Ω)
  | 0 => Kernel.const H (Measure.dirac (fun i => Fin.elim0 i))
  | N + 1 => ((tupleKernel κ N).compProd (κ.comap Prod.fst measurable_fst)).map
      (OneCopyProductProtocol.tupleSplit N).symm

instance tupleKernel_markov (κ : Kernel H Ω) [IsMarkovKernel κ] (N : ℕ) :
    IsMarkovKernel (tupleKernel κ N) := by
  induction N with
  | zero => change IsMarkovKernel (Kernel.const H (Measure.dirac _)); infer_instance
  | succ N ih =>
      change IsMarkovKernel (((tupleKernel κ N).compProd
        (κ.comap Prod.fst measurable_fst)).map
          (OneCopyProductProtocol.tupleSplit N).symm)
      letI := ih
      exact Kernel.IsMarkovKernel.map _ (MeasurableEquiv.measurable _)

theorem tupleKernel_succ (κ : Kernel H Ω) [IsMarkovKernel κ] (N : ℕ) (h : H) :
    tupleKernel κ (N + 1) h = ((tupleKernel κ N h).prod (κ h)).map
      (OneCopyProductProtocol.tupleSplit N).symm := by
  rw [tupleKernel, Kernel.map_apply _ (MeasurableEquiv.measurable _)]
  congr 1
  apply Measure.ext
  intro S hS
  rw [Kernel.compProd_apply hS, Measure.prod_apply hS]
  apply lintegral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    dsimp only
    rw [Kernel.comap_apply]

/-- The conditional finite product law is a theorem about the sequential
construction, not a statistical input.  The zero-copy block is included. -/
theorem tupleKernel_apply (κ : Kernel H Ω) [IsMarkovKernel κ] (N : ℕ) (h : H) :
    tupleKernel κ N h = Measure.pi (fun _ : Fin N => κ h) := by
  induction N with
  | zero => exact (Measure.pi_of_empty (fun _ : Fin 0 => κ h) _).symm
  | succ N ih =>
      rw [tupleKernel_succ, ih]
      exact (MeasurePreserving.symm (OneCopyProductProtocol.tupleSplit N)
        (OneCopyProductProtocol.tupleSplit_measurePreserving (κ h) N)).map_eq

variable {ι H' : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace H']

/-- A measurable classical policy can choose actual quantum measurement
parameters.  The effects and reference kernel are pulled back together. -/
def pullbackStep (M : OneCopyStep ι H Ω) (f : H' → H) (hf : Measurable f) :
    OneCopyStep ι H' Ω where
  reference := M.reference.comap f hf
  reference_sfinite := inferInstance
  effect := fun h y => M.effect (f h) y
  entry_measurable := fun i j => (M.entry_measurable i j).comp
    ((hf.comp measurable_fst).prodMk measurable_snd)
  positive_ae := fun h => M.positive_ae (f h)
  entry_integrable := fun h => M.entry_integrable (f h)
  total := fun h => M.total (f h)

theorem pullbackStep_bornKernel (M : OneCopyStep ι H Ω) (f : H' → H)
    (hf : Measurable f) (ρ : Density ι) :
    (pullbackStep M f hf).bornKernel ρ = (M.bornKernel ρ).comap f hf := by
  apply Kernel.ext
  intro h
  rw [OneCopyStep.bornKernel_apply, Kernel.comap_apply, OneCopyStep.bornKernel_apply]
  rfl

/-- A block kernel on actual quantum outcomes, consuming `N` identical
one-copy Born transitions with the stage parameter held fixed. -/
def quantumBlockKernel (M : OneCopyStep ι H Ω) (ρ : Density ι) (N : ℕ) :
    Kernel H (Fin N → Ω) := tupleKernel (M.bornKernel ρ) N

instance quantumBlockKernel_markov (M : OneCopyStep ι H Ω) (ρ : Density ι) (N : ℕ) :
    IsMarkovKernel (quantumBlockKernel M ρ N) :=
  tupleKernel_markov _ _

theorem quantumBlockKernel_apply (M : OneCopyStep ι H Ω) (ρ : Density ι)
    (N : ℕ) (h : H) :
    quantumBlockKernel M ρ N h = Measure.pi (fun _ : Fin N => M.bornKernel ρ h) :=
  tupleKernel_apply _ _ _

/-- Each conditional block law is also the actual sample law of a genuine
`N`-copy raw one-copy protocol, for every fixed stage history and every RN
witness.  Consequently a product routine never needs a collective tensor
measurement to justify its operational interpretation. -/
theorem quantumBlockKernel_eq_protocol [Nonempty ι] (M : OneCopyStep ι H Ω)
    (ρ : Density ι) (N : ℕ) (h : H) (T : Estimator ι (Fin N → Ω))
    (R : CollectiveModel.OperatorRadonNikodymInput ι Ω) :
    quantumBlockKernel M ρ N h =
      ((OneCopyProductProtocol.operatorLearner (conditionalPOVM M h) T).transcriptLaw
        R ρ).map (OneCopyProductProtocol.historyTuple N) := by
  rw [OneCopyProductProtocol.operatorLearner_tupleLaw, quantumBlockKernel_apply]
  unfold OneCopyProductProtocol.sampleMeasure
  rw [conditionalPOVM_outcomeMeasure]

end ConditionalProducts

section SourceMinimum

variable {ι Seed Ω : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace Seed] [MeasurableSpace Ω] {N : ℕ}

/-- A native dominated one-copy construction proves an upper bound in the
source's raw operator minimum, with its exact fresh-copy count. -/
theorem Nonecopy_le (A : AdaptiveModel.Learner ι Seed Ω N)
    (RN : SourceCopyComplexity.AllFixedOperatorRN ι)
    (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε : ℝ≥0∞)
    (hA : A.LearnsRank loss r ε ((2 : ℝ≥0∞) / 3)) :
    SourceCopyComplexity.Nonecopy RN loss r ε ≤ (N : ℝ≥0∞) := by
  apply CopyComplexity.minimumCopies_le
  exact ⟨Seed, Ω, inferInstance, inferInstance, operatorLearner A,
    (operatorLearner_learnsRank_iff A (RN Ω inferInstance) loss r ε _).mpr hA⟩

end SourceMinimum

end Paper26.StagePolicy
