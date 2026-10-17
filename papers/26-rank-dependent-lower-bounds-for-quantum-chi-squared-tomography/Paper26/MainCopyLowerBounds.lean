import Paper26.CopyComplexity
import Paper26.MainLowerBounds

/-! The four actual-learner inequalities expressed as the minimum copy
counts from Definition 1.1. Every classical hypothesis remains raw: matrix
geometry/volume, Sobolev and weak analysis, symmetric tensors, the universal
prior, and fixed operator-measure RN representation. No sample bound is an input.
The one-copy minimum presently uses the joint dominated adaptive model. -/
noncomputable section
open scoped ENNReal
open MeasureTheory

namespace Paper26.MainCopyLowerBounds
open QuantumModel CollectiveModel CollectiveMainLowerBounds CopyComplexity
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The already disclosed standard facts needed at fixed d,r. The symmetric
projector tower covers all possible copy counts in the minimum. -/
structure ClassicalInputs (d r : ℕ) (C : ℝ) where
  volume : RawVolumeInputs (RankReduction.reducedRank d r) (d - RankReduction.reducedRank d r)
  analysis : 2 ≤ RankReduction.reducedRank d r * (d - RankReduction.reducedRank d r) →
    AnalysisInputs (2 * RankReduction.reducedRank d r * (d - RankReduction.reducedRank d r))
  symmetric : ∀ n : ℕ, SymmetricSupport.SymmetricProjectorInput (AmbientIndex d r) n
  graph : GraphFisherBudget.GraphTangentInput
  prior : GraphPrior.NZSmoothLocalPriorInput C

/-- The generic fixed-POVM RN theorem is retained uniformly over the actual
outcome spaces occurring in the collective minimum; it is not a family-RN
assumption for adaptive measurement kernels. -/
def AllOperatorRN (ι : Type) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ (n : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω),
    letI := mΩ
    OperatorRadonNikodymInput (Fin n → ι) Ω

/-- Equation (7)--(8), with actual extended minimum copy counts, common
positive constants and all dimension/rank endpoints. -/
theorem theorem_1_2 {d r : ℕ} (hcard : Fintype.card ι = d)
    (hd : 2 ≤ d) (hr : 1 ≤ r) (hrd : r ≤ d) {C ε : ℝ} (hC : 0 < C)
    (I : ClassicalInputs d r C) (RN : AllOperatorRN ι)
    (hε : 0 < ε) (hsmall : ε ≤ accuracyThreshold C) :
    ENNReal.ofReal (sampleConstant C *
      (Real.sqrt (r : ℝ) * d * Real.sqrt (d : ℝ) / ε)) ≤ Ncoll (ι := ι) chiB r (ENNReal.ofReal ε) ∧
    ENNReal.ofReal (sampleConstant C *
      ((r : ℝ) * Real.sqrt (r : ℝ) * d * Real.sqrt (d : ℝ) / ε)) ≤
        Nonecopy (ι := ι) chiB r (ENNReal.ofReal ε) ∧
    ENNReal.ofReal (sampleConstant C * ((d : ℝ) ^ 2 / ε ^ 2)) ≤ Ncoll (ι := ι) chiR r (ENNReal.ofReal ε) ∧
    ENNReal.ofReal (sampleConstant C * ((r : ℝ) * (d : ℝ) ^ 2 / ε ^ 2)) ≤
        Nonecopy (ι := ι) chiR r (ENNReal.ofReal ε) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply collective_lower_of_all_learners (ι := ι)
    intro n Ω mΩ A hA
    letI := mΩ
    have h := MainLowerBounds.bures_collective hcard hd hr hrd I.volume I.analysis
      (I.symmetric n) (RN n Ω mΩ) A I.graph hC I.prior hε hsmall hA
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal h
  · apply adaptive_lower_of_all_learners (ι := ι)
    intro n Seed Ω mSeed mΩ A hA
    letI := mSeed
    letI := mΩ
    have h := AdaptiveCoordinateTransport.bures_adaptive hcard hd hr hrd I.volume I.analysis
      (I.symmetric n) A I.graph hC I.prior hε hsmall hA
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal h
  · apply collective_lower_of_all_learners (ι := ι)
    intro n Ω mΩ A hA
    letI := mΩ
    have h := MainLowerBounds.right_collective hcard hd hr hrd I.volume I.analysis
      (I.symmetric n) (RN n Ω mΩ) A I.graph hC I.prior hε hsmall hA
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal h
  · apply adaptive_lower_of_all_learners (ι := ι)
    intro n Seed Ω mSeed mΩ A hA
    letI := mSeed
    letI := mΩ
    have h := AdaptiveCoordinateTransport.right_adaptive hcard hd hr hrd I.volume I.analysis
      (I.symmetric n) A I.graph hC I.prior hε hsmall hA
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal h

end Paper26.MainCopyLowerBounds
