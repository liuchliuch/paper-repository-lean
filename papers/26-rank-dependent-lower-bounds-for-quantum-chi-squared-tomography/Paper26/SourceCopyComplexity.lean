import Paper26.MainCopyLowerBounds
import Paper26.AdaptiveOperatorModelTransport
import Paper26.FlatLowerBounds

/-! Definition 1.1 and Theorem 1.2 for raw operator-valued adaptive
protocols, with arbitrary measurable histories and outcomes. Ordinary fixed
operator RN witnesses merely construct the intrinsic Born measures; their
choice does not change a learning promise or the minimum copy count. The
native protocol transport, rather than a family RN assumption, proves the
adaptive lower bounds. -/
noncomputable section
open scoped ENNReal
open MeasureTheory

namespace Paper26.SourceCopyComplexity
open QuantumModel CollectiveModel CollectiveMainLowerBounds CopyComplexity
open MainCopyLowerBounds
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The same generic fixed-space operator RN theorem, quantified over all
spaces needed for a raw step or a single fixed joint history/outcome space. -/
def AllFixedOperatorRN (ι : Type) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω),
    letI := mΩ
    OperatorRadonNikodymInput ι Ω

/-- A raw protocol uses exactly n fresh copies. The RN witness only names
its Born law, which is proved independent of the witness below. -/
def adaptiveAchievable (RN : AllFixedOperatorRN ι)
    (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε : ℝ≥0∞) (n : ℕ) : Prop :=
  ∃ (Seed Ω : Type) (mSeed : MeasurableSpace Seed) (mΩ : MeasurableSpace Ω),
    letI := mSeed
    letI := mΩ
    ∃ A : AdaptiveOperatorModelTransport.OperatorLearner ι Seed Ω n,
      A.LearnsRank (RN Ω mΩ) loss r ε ((2 : ℝ≥0∞) / 3)

/-- The source's one-copy minimum over the original operator model. -/
def Nonecopy (RN : AllFixedOperatorRN ι)
    (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε : ℝ≥0∞) : ℝ≥0∞ :=
  minimumCopies (adaptiveAchievable RN loss r ε)

theorem learnsRank_choice_independent {Seed Ω : Type}
    [MeasurableSpace Seed] [MeasurableSpace Ω] {n : ℕ}
    (A : AdaptiveOperatorModelTransport.OperatorLearner ι Seed Ω n)
    (R R' : OperatorRadonNikodymInput ι Ω)
    (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε q : ℝ≥0∞) :
    A.LearnsRank R loss r ε q ↔ A.LearnsRank R' loss r ε q := by
  exact Iff.rfl

theorem adaptiveAchievable_choice_independent (RN RN' : AllFixedOperatorRN ι)
    (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε : ℝ≥0∞) (n : ℕ) :
    adaptiveAchievable RN loss r ε n ↔ adaptiveAchievable RN' loss r ε n := by
  constructor <;> rintro ⟨Seed, Ω, mSeed, mΩ, A, hA⟩
  · exact ⟨Seed, Ω, mSeed, mΩ, A,
      (learnsRank_choice_independent A (RN Ω mΩ) (RN' Ω mΩ) loss r ε _).mp hA⟩
  · exact ⟨Seed, Ω, mSeed, mΩ, A,
      (learnsRank_choice_independent A (RN' Ω mΩ) (RN Ω mΩ) loss r ε _).mp hA⟩

theorem Nonecopy_choice_independent (RN RN' : AllFixedOperatorRN ι)
    (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε : ℝ≥0∞) :
    Nonecopy RN loss r ε = Nonecopy RN' loss r ε := by
  rfl

/-- Equation (6), including its measurable-event requirement, for the raw
operator protocol rather than its derived dominated representation. -/
theorem learnsRank_iff_inf {Seed Ω : Type}
    [MeasurableSpace Seed] [MeasurableSpace Ω] {n : ℕ}
    (A : AdaptiveOperatorModelTransport.OperatorLearner ι Seed Ω n)
    (R : OperatorRadonNikodymInput ι Ω)
    (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε q : ℝ≥0∞) :
    A.LearnsRank R loss r ε q ↔
      (∀ ρ : Density ι, ρ.matrix.rank ≤ r → MeasurableSet (A.successSet loss ρ ε)) ∧
      q ≤ ⨅ ρ : {ρ : Density ι // ρ.matrix.rank ≤ r},
        A.successProbability R loss ρ.1 ε := by
  constructor
  · intro h
    exact ⟨fun ρ hr => (h ρ hr).1, le_iInf fun ρ => (h ρ.1 ρ.2).2⟩
  · rintro ⟨hm, hp⟩ ρ hr
    exact ⟨hm ρ hr, hp.trans (iInf_le (fun η : {ρ : Density ι // ρ.matrix.rank ≤ r} =>
      A.successProbability R loss η.1 ε) ⟨ρ, hr⟩)⟩

/-- All four source minimum-copy lower bounds. Both adaptive minima now
range over the original raw operator protocols. The collective minimum
already ranges over arbitrary actual operator POVMs. -/
theorem theorem_1_2 {d r : ℕ} (hcard : Fintype.card ι = d)
    (hd : 2 ≤ d) (hr : 1 ≤ r) (hrd : r ≤ d) {C ε : ℝ} (hC : 0 < C)
    (I : ClassicalInputs d r C) (RN : AllOperatorRN ι) (RF : AllFixedOperatorRN ι)
    (hε : 0 < ε) (hsmall : ε ≤ accuracyThreshold C) :
    ENNReal.ofReal (sampleConstant C *
      (Real.sqrt (r : ℝ) * d * Real.sqrt (d : ℝ) / ε)) ≤
        Ncoll (ι := ι) chiB r (ENNReal.ofReal ε) ∧
    ENNReal.ofReal (sampleConstant C *
      ((r : ℝ) * Real.sqrt (r : ℝ) * d * Real.sqrt (d : ℝ) / ε)) ≤
        Nonecopy RF chiB r (ENNReal.ofReal ε) ∧
    ENNReal.ofReal (sampleConstant C * ((d : ℝ) ^ 2 / ε ^ 2)) ≤
        Ncoll (ι := ι) chiR r (ENNReal.ofReal ε) ∧
    ENNReal.ofReal (sampleConstant C * ((r : ℝ) * (d : ℝ) ^ 2 / ε ^ 2)) ≤
        Nonecopy RF chiR r (ENNReal.ofReal ε) := by
  have hbase := MainCopyLowerBounds.theorem_1_2 hcard hd hr hrd hC I RN hε hsmall
  have hnι : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  letI := hnι
  refine ⟨hbase.1, ?_, hbase.2.2.1, ?_⟩
  · apply le_minimumCopies
    rintro n ⟨Seed, Ω, mSeed, mΩ, A, hA⟩
    letI := mSeed
    letI := mΩ
    have h := A.bures_adaptive (RF Ω mΩ)
      (fun k => RF (AdaptiveModel.History Seed Ω k.val × Ω) inferInstance)
      hcard hd hr hrd I.volume I.analysis (I.symmetric n) I.graph hC I.prior hε hsmall hA
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal h
  · apply le_minimumCopies
    rintro n ⟨Seed, Ω, mSeed, mΩ, A, hA⟩
    letI := mSeed
    letI := mΩ
    have h := A.right_adaptive (RF Ω mΩ)
      (fun k => RF (AdaptiveModel.History Seed Ω k.val × Ω) inferInstance)
      hcard hd hr hrd I.volume I.analysis (I.symmetric n) I.graph hC I.prior hε hsmall hA
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal h

end Paper26.SourceCopyComplexity
