import Paper26.CoordinateTransport
import Paper26.OperatorPOVMTransport

/-!
# Collective Theorem 1.2 for arbitrary actual operator POVMs

These conclusions apply to every actual finite ambient index, arbitrary
measurable outcome space, unrestricted measurable estimator, and collective
operator POVM on the actual tensor-copy space. The actual rank-learning
promise is intrinsic to the operator POVM. Its transfer to a dominated
experiment, and subsequent coordinate transport, preserve that promise.

The classical finite-dimensional operator RN theorem is retained as its
exact existing generic input for the one collective measurement. All other
parameters are the original raw inputs of the proved chart and pure-state
arguments. No Fisher bound, successful-volume bound, success-rate bound or
sample lower bound is an external field. A common positive constant and
accuracy threshold work for all dimensions and ranks once the universal
smooth-prior constant `C` is fixed.

This module does not assert a jointly measurable RN representation of an
arbitrary adaptive family of conditional operator POVMs.
-/

noncomputable section
open MeasureTheory

namespace Paper26.MainLowerBounds

open CollectiveModel CollectiveMainLowerBounds OperatorPOVMTransport SymmetricSupport

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]

theorem constants_positive {C : ℝ} (hC : 0 < C) :
    0 < sampleConstant C ∧ 0 < accuracyThreshold C :=
  ⟨sampleConstant_pos hC, accuracyThreshold_pos hC⟩

/-- The collective Bures chi-squared rate for every actual operator learner,
including all pure/qubit and large-rank endpoints. -/
theorem bures_collective {d r n : ℕ} (hcard : Fintype.card ι = d)
    (hd : 2 ≤ d) (hr : 1 ≤ r) (hrd : r ≤ d)
    (V : RawVolumeInputs (RankReduction.reducedRank d r) (d - RankReduction.reducedRank d r))
    (An : 2 ≤ RankReduction.reducedRank d r * (d - RankReduction.reducedRank d r) →
      AnalysisInputs (2 * RankReduction.reducedRank d r * (d - RankReduction.reducedRank d r)))
    (P : SymmetricProjectorInput (AmbientIndex d r) n)
    (R : OperatorRadonNikodymInput (Fin n → ι) Ω)
    (A : OperatorLearner ι Ω n) (G : GraphFisherBudget.GraphTangentInput)
    {C ε : ℝ} (hC : 0 < C) (N : GraphPrior.NZSmoothLocalPriorInput C)
    (hε : 0 < ε) (hsmall : ε ≤ accuracyThreshold C)
    (hA : A.BuresSuccess r (ENNReal.ofReal ε)) :
    sampleConstant C * (Real.sqrt (r : ℝ) * d * Real.sqrt (d : ℝ) / ε) ≤ (n : ℝ) := by
  exact CoordinateTransport.bures_collective hcard hd hr hrd V An P (A.toDominated R)
    G hC N hε hsmall ((A.toDominated_buresSuccess_iff R r _).mpr hA)

/-- The collective right-inverse chi-squared rate, with the same positive
universal coefficient and small-accuracy threshold as the Bures rate. -/
theorem right_collective {d r n : ℕ} (hcard : Fintype.card ι = d)
    (hd : 2 ≤ d) (hr : 1 ≤ r) (hrd : r ≤ d)
    (V : RawVolumeInputs (RankReduction.reducedRank d r) (d - RankReduction.reducedRank d r))
    (An : 2 ≤ RankReduction.reducedRank d r * (d - RankReduction.reducedRank d r) →
      AnalysisInputs (2 * RankReduction.reducedRank d r * (d - RankReduction.reducedRank d r)))
    (P : SymmetricProjectorInput (AmbientIndex d r) n)
    (R : OperatorRadonNikodymInput (Fin n → ι) Ω)
    (A : OperatorLearner ι Ω n) (G : GraphFisherBudget.GraphTangentInput)
    {C ε : ℝ} (hC : 0 < C) (N : GraphPrior.NZSmoothLocalPriorInput C)
    (hε : 0 < ε) (hsmall : ε ≤ accuracyThreshold C)
    (hA : A.RightSuccess r (ENNReal.ofReal ε)) :
    sampleConstant C * ((d : ℝ) ^ 2 / ε ^ 2) ≤ (n : ℝ) := by
  exact CoordinateTransport.right_collective hcard hd hr hrd V An P (A.toDominated R)
    G hC N hε hsmall ((A.toDominated_rightSuccess_iff R r _).mpr hA)

end Paper26.MainLowerBounds
