import Paper26.SourceCopyComplexity
import Paper26.JordanLossMeasurability

/-! The source's chiG lower-bound consequence of chiB <= chiG. Actual
successful events and the original operator-model minima are used. -/
noncomputable section
open scoped ENNReal
open MeasureTheory
namespace Paper26.IntermediateLossLowerBounds
open QuantumModel CollectiveModel CopyComplexity SourceCopyComplexity
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem collective_promise {Ω : Type} [MeasurableSpace Ω] {n r : ℕ}
    (A : OperatorPOVMTransport.OperatorLearner ι Ω n)
    (R : OperatorRadonNikodymInput (Fin n → ι) Ω) {ε q : ℝ≥0∞}
    (h : A.LearnsRank chiG r ε q) : A.LearnsRank chiB r ε q := by
  intro ρ hr
  have hm : MeasurableSet (A.successSet chiB ρ ε) := by
    exact measurableSet_le
      (JordanLossMeasurability.measurable_chiB_comp (fun _ : Ω => ρ)
        A.estimator.estimate measurable_const A.estimator.measurable_estimate) measurable_const
  refine ⟨hm, ?_⟩
  have hp := (h ρ hr).2
  rw [A.successProbability_eq_outcomeMeasure R chiG ρ ε (h ρ hr).1] at hp
  rw [A.successProbability_eq_outcomeMeasure R chiB ρ ε hm]
  apply hp.trans
  apply measure_mono
  intro y hy
  exact (loss_comparison ρ (A.estimator.estimate y)).1.trans hy

theorem adaptive_promise {Seed Ω : Type} [MeasurableSpace Seed] [MeasurableSpace Ω]
    {n r : ℕ} (A : AdaptiveOperatorModelTransport.OperatorLearner ι Seed Ω n)
    (R : OperatorRadonNikodymInput ι Ω) {ε q : ℝ≥0∞}
    (h : A.LearnsRank R chiG r ε q) : A.LearnsRank R chiB r ε q := by
  intro ρ hr
  refine ⟨?_, (h ρ hr).2.trans (measure_mono ?_)⟩
  · exact measurableSet_le
      (JordanLossMeasurability.measurable_chiB_comp (fun _ => ρ)
        A.estimator.estimate measurable_const A.estimator.measurable_estimate) measurable_const
  · intro y hy
    exact (loss_comparison ρ (A.estimator.estimate y)).1.trans hy

theorem collective_minimum_mono (RN : MainCopyLowerBounds.AllOperatorRN ι)
    (r : ℕ) (ε : ℝ≥0∞) :
    Ncoll (ι := ι) chiB r ε ≤ Ncoll (ι := ι) chiG r ε := by
  apply le_minimumCopies
  rintro n ⟨Ω, mΩ, A, hA⟩
  letI := mΩ
  exact minimumCopies_le (show collectiveAchievable chiB r ε n from
    ⟨Ω, mΩ, A, collective_promise A (RN n Ω mΩ) hA⟩)

theorem adaptive_minimum_mono (RF : AllFixedOperatorRN ι) (r : ℕ) (ε : ℝ≥0∞) :
    SourceCopyComplexity.Nonecopy RF chiB r ε ≤ SourceCopyComplexity.Nonecopy RF chiG r ε := by
  apply le_minimumCopies
  rintro n ⟨Seed, Ω, mSeed, mΩ, A, hA⟩
  letI := mSeed
  letI := mΩ
  exact minimumCopies_le (show SourceCopyComplexity.adaptiveAchievable RF chiB r ε n from
    ⟨Seed, Ω, mSeed, mΩ, A, adaptive_promise A (RF Ω mΩ) hA⟩)

/-- Both Bures main lower rates apply to the intermediate geometric loss,
with the same constants, parameter ranges and original measurement models. -/
theorem chiG_lower_bounds {d r : ℕ} (hcard : Fintype.card ι = d)
    (hd : 2 ≤ d) (hr : 1 ≤ r) (hrd : r ≤ d) {C ε : ℝ} (hC : 0 < C)
    (I : MainCopyLowerBounds.ClassicalInputs d r C)
    (RN : MainCopyLowerBounds.AllOperatorRN ι) (RF : AllFixedOperatorRN ι)
    (hε : 0 < ε) (hsmall : ε ≤ CollectiveMainLowerBounds.accuracyThreshold C) :
    ENNReal.ofReal (CollectiveMainLowerBounds.sampleConstant C *
      (Real.sqrt (r : ℝ)*d*Real.sqrt (d : ℝ)/ε)) ≤
        Ncoll (ι := ι) chiG r (ENNReal.ofReal ε) ∧
    ENNReal.ofReal (CollectiveMainLowerBounds.sampleConstant C *
      ((r : ℝ)*Real.sqrt (r : ℝ)*d*Real.sqrt (d : ℝ)/ε)) ≤
        SourceCopyComplexity.Nonecopy RF chiG r (ENNReal.ofReal ε) := by
  have h := SourceCopyComplexity.theorem_1_2 hcard hd hr hrd hC I RN RF hε hsmall
  exact ⟨h.1.trans (collective_minimum_mono RN r _),
    h.2.1.trans (adaptive_minimum_mono RF r _)⟩

end Paper26.IntermediateLossLowerBounds
