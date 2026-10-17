import Paper26.SourceCopyComplexity

/-!
# Theorem 1.2 for the flat family's actual minimum copy counts

The promise is only `ρ = P/r` for a rank-r orthogonal projector P.  Both
minima quantify over arbitrary measurable outcome spaces and unrestricted
density estimators.  The adaptive minimum uses original raw operator POVM
protocols, without assuming a jointly measurable family of RN densities.

Every lower bound is obtained by entering an arbitrary achievable witness
and applying the already proved flat-only lower bound to that actual learner.
The input package uses the actual r and d-r, with no reduced-rank promise.
The constants and accuracy threshold are exactly those of the all-rank main
theorem.  The only RN parameters are the existing generic fixed-space facts.
-/
noncomputable section
open scoped ENNReal
open MeasureTheory

namespace Paper26.FlatCopyComplexity
open QuantumModel CollectiveModel CollectiveMainLowerBounds CopyComplexity FlatLowerBounds

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A single actual collective operator learner works for every flat input.
All outcome spaces and sigma algebras are quantified before the promise. -/
def collectiveAchievable (loss : Density ι → Density ι → ℝ≥0∞)
    (r : ℕ) (ε : ℝ≥0∞) (n : ℕ) : Prop :=
  ∃ (Ω : Type) (mΩ : MeasurableSpace Ω),
    letI := mΩ
    ∃ A : OperatorPOVMTransport.OperatorLearner ι Ω n,
      OperatorLearnsFlat A loss r ε ((2 : ℝ≥0∞) / 3)

/-- A single raw adaptive protocol works for every flat input.  The fixed
RN witness only represents its intrinsic Born law. -/
def adaptiveAchievable (RF : SourceCopyComplexity.AllFixedOperatorRN ι)
    (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε : ℝ≥0∞) (n : ℕ) : Prop :=
  ∃ (Seed Ω : Type) (mSeed : MeasurableSpace Seed) (mΩ : MeasurableSpace Ω),
    letI := mSeed
    letI := mΩ
    ∃ A : AdaptiveOperatorModelTransport.OperatorLearner ι Seed Ω n,
      OperatorAdaptiveLearnsFlat A (RF Ω mΩ) loss r ε ((2 : ℝ≥0∞) / 3)

/-- Minimum collective copy count for the actual flat rank-r family, with
infinity if no finite learner exists. -/
def NcollFlat (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε : ℝ≥0∞) : ℝ≥0∞ :=
  minimumCopies (collectiveAchievable loss r ε)

/-- Minimum raw adaptive copy count for the actual flat rank-r family. -/
def NonecopyFlat (RF : SourceCopyComplexity.AllFixedOperatorRN ι)
    (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε : ℝ≥0∞) : ℝ≥0∞ :=
  minimumCopies (adaptiveAchievable RF loss r ε)

theorem adaptiveAchievable_choice_independent
    (RF RF' : SourceCopyComplexity.AllFixedOperatorRN ι)
    (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε : ℝ≥0∞) (n : ℕ) :
    adaptiveAchievable RF loss r ε n ↔ adaptiveAchievable RF' loss r ε n := by
  exact Iff.rfl

theorem NonecopyFlat_choice_independent (RF RF' : SourceCopyComplexity.AllFixedOperatorRN ι)
    (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε : ℝ≥0∞) :
    NonecopyFlat RF loss r ε = NonecopyFlat RF' loss r ε := by
  rfl

/-- The uniform flat-only promise is exactly the infimum success condition
on the full projector/r family, with its measurable-event requirement. -/
theorem operator_learnsFlat_iff_inf {Ω : Type} [MeasurableSpace Ω] {n : ℕ}
    (A : OperatorPOVMTransport.OperatorLearner ι Ω n)
    (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε q : ℝ≥0∞) :
    OperatorLearnsFlat A loss r ε q ↔
      (∀ ρ : Density ι, ρ ∈ FlatInputs r → MeasurableSet (A.successSet loss ρ ε)) ∧
      q ≤ ⨅ ρ : {ρ : Density ι // ρ ∈ FlatInputs r}, A.successProbability loss ρ.1 ε := by
  constructor
  · intro h
    exact ⟨fun ρ hr => (h ρ hr).1, le_iInf fun ρ => (h ρ.1 ρ.2).2⟩
  · rintro ⟨hm, hp⟩ ρ hr
    exact ⟨hm ρ hr, hp.trans (iInf_le
      (fun η : {ρ : Density ι // ρ ∈ FlatInputs r} => A.successProbability loss η.1 ε)
      ⟨ρ, hr⟩)⟩

theorem operatorAdaptive_learnsFlat_iff_inf {Seed Ω : Type}
    [MeasurableSpace Seed] [MeasurableSpace Ω] {n : ℕ}
    (A : AdaptiveOperatorModelTransport.OperatorLearner ι Seed Ω n)
    (R : OperatorRadonNikodymInput ι Ω)
    (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε q : ℝ≥0∞) :
    OperatorAdaptiveLearnsFlat A R loss r ε q ↔
      (∀ ρ : Density ι, ρ ∈ FlatInputs r → MeasurableSet (A.successSet loss ρ ε)) ∧
      q ≤ ⨅ ρ : {ρ : Density ι // ρ ∈ FlatInputs r}, A.successProbability R loss ρ.1 ε := by
  constructor
  · intro h
    exact ⟨fun ρ hr => (h ρ hr).1, le_iInf fun ρ => (h ρ.1 ρ.2).2⟩
  · rintro ⟨hm, hp⟩ ρ hr
    exact ⟨hm ρ hr, hp.trans (iInf_le
      (fun η : {ρ : Density ι // ρ ∈ FlatInputs r} => A.successProbability R loss η.1 ε)
      ⟨ρ, hr⟩)⟩

/-- Only the disclosed preceding mathematical inputs, at the actual flat
rank r.  The symmetric tower covers all candidate natural copy counts. -/
structure ClassicalInputs (d r : ℕ) (C : ℝ) where
  volume : RawVolumeInputs r (d - r)
  analysis : 2 ≤ r * (d - r) → AnalysisInputs (2 * r * (d - r))
  symmetric : ∀ n : ℕ,
    SymmetricSupport.SymmetricProjectorInput (GraphExperiment.StateIndex r (d - r)) n
  graph : GraphFisherBudget.GraphTangentInput
  prior : GraphPrior.NZSmoothLocalPriorInput C

/-- The last sentence of Theorem 1.2, for both actual minimum-copy models.
Only flat rank-r inputs are promised, and `2*r ≤ d` is the exact natural
number condition for `r ≤ d/2`.  Both constants are the same as in the
all-rank main theorem. -/
theorem theorem_1_2_flat {d r : ℕ} (hcard : Fintype.card ι = d)
    (hd : 2 ≤ d) (hr : 1 ≤ r) (hhalf : 2 * r ≤ d) {C ε : ℝ} (hC : 0 < C)
    (I : ClassicalInputs d r C) (RN : MainCopyLowerBounds.AllOperatorRN ι)
    (RF : SourceCopyComplexity.AllFixedOperatorRN ι)
    (hε : 0 < ε) (hsmall : ε ≤ accuracyThreshold C) :
    ENNReal.ofReal (sampleConstant C *
      (Real.sqrt (r : ℝ) * d * Real.sqrt (d : ℝ) / ε)) ≤
        NcollFlat (ι := ι) chiB r (ENNReal.ofReal ε) ∧
    ENNReal.ofReal (sampleConstant C *
      ((r : ℝ) * Real.sqrt (r : ℝ) * d * Real.sqrt (d : ℝ) / ε)) ≤
        NonecopyFlat RF chiB r (ENNReal.ofReal ε) ∧
    ENNReal.ofReal (sampleConstant C * ((d : ℝ) ^ 2 / ε ^ 2)) ≤
        NcollFlat (ι := ι) chiR r (ENNReal.ofReal ε) ∧
    ENNReal.ofReal (sampleConstant C * ((r : ℝ) * (d : ℝ) ^ 2 / ε ^ 2)) ≤
        NonecopyFlat RF chiR r (ENNReal.ofReal ε) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply le_minimumCopies
    rintro n ⟨Ω, mΩ, A, hA⟩
    letI := mΩ
    have h := bures_collective_operator_flat hcard hd hr hhalf I.volume I.analysis
      (I.symmetric n) A (RN n Ω mΩ) I.graph hC I.prior hε hsmall hA
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal h
  · apply le_minimumCopies
    rintro n ⟨Seed, Ω, mSeed, mΩ, A, hA⟩
    letI := mSeed
    letI := mΩ
    have h := bures_adaptive_operator_flat hcard hd hr hhalf I.volume I.analysis
      (I.symmetric n) A (RF Ω mΩ)
      (fun k => RF (AdaptiveModel.History Seed Ω k.val × Ω) inferInstance)
      I.graph hC I.prior hε hsmall hA
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal h
  · apply le_minimumCopies
    rintro n ⟨Ω, mΩ, A, hA⟩
    letI := mΩ
    have h := right_collective_operator_flat hcard hd hr hhalf I.volume I.analysis
      (I.symmetric n) A (RN n Ω mΩ) I.graph hC I.prior hε hsmall hA
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal h
  · apply le_minimumCopies
    rintro n ⟨Seed, Ω, mSeed, mΩ, A, hA⟩
    letI := mSeed
    letI := mΩ
    have h := right_adaptive_operator_flat hcard hd hr hhalf I.volume I.analysis
      (I.symmetric n) A (RF Ω mΩ)
      (fun k => RF (AdaptiveModel.History Seed Ω k.val × Ω) inferInstance)
      I.graph hC I.prior hε hsmall hA
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal h

end Paper26.FlatCopyComplexity
