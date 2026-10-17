import Paper26.CollectiveBuresUpper
import Paper26.OneCopyBuresUpper
import Paper26.RightUpperWitnesses
import Paper26.PureUpperWitnesses

/-!
# Theorem 1.3 in the original operator measurement models

Each upper witness retains an actual experiment and estimator, chosen before
all rank-at-most-r inputs, together with its natural consumed-copy count.
The four coefficients below are explicit positive universal constants.
The source stage schedule is exactly ceil(log₂(16d/ε)).

The input record merely collects already disclosed generic classical facts:
compact-fiber Borel selection, OW Frobenius experiments, raw Haar coordinate
moments, matrix Bernstein and Hermitian Weyl perturbation. No learning
promise, conditional risk, measurement law or execution certificate is an
input. Pure-state inputs are kept separate because that construction uses
only Haar tensor moments and symmetric projectors.
-/
noncomputable section
open scoped ENNReal
open MeasureTheory

namespace Paper26.MainUpperBounds
open QuantumModel UpperBoundWitnesses

variable {d : ℕ} [NeZero d]

/-- A packaging of existing generic inputs, with no P26 conclusion as a field. -/
structure ClassicalInputs (d : ℕ) [NeZero d] where
  selection : MeasurableSpectralSelection.CompactFiberSelectionInput.{0,0}
  collectiveFull : FrobeniusLearning.OWFrobeniusInput (Fin d)
  collectiveBlocks : ∀ S : Finset (Fin d), S.Nonempty →
    FrobeniusLearning.OWFrobeniusInput (CollectiveStageRoutine.Active S)
  haarBlocks : OneCopyStageRoutine.HaarFamily (Fin d)
  bernsteinFull : OneCopySubmatrix.MatrixBernsteinInput (Fin d)
  weylFull : OneCopySubmatrix.WeylEigenvalueInput (Fin d)
  bernsteinBlocks : ∀ (S : Finset (Fin d)) (hS : S.Nonempty),
    @OneCopySubmatrix.MatrixBernsteinInput (MultiscaleUpdate.BlockIndex S)
      inferInstance inferInstance (OneCopyStageRoutine.blockIndex_nonempty S hS)
  weylBlocks : ∀ S : Finset (Fin d),
    OneCopySubmatrix.WeylEigenvalueInput (MultiscaleUpdate.BlockIndex S)

def stages (d : ℕ) (ε : ℝ) : ℕ := DyadicSchedule.sourceStages d ε

def collectiveBuresBudget (d r : ℕ) (ε δ : ℝ) : ℝ :=
  CollectiveBuresUpper.universalConstant *
    (Real.sqrt (r : ℝ) * d * Real.sqrt (d : ℝ) * (stages d ε : ℝ)^2 / ε) *
      Real.log ((stages d ε : ℝ)/δ)

def onecopyBuresBudget (d r : ℕ) (ε δ : ℝ) : ℝ :=
  OneCopyBuresUpper.universalConstant *
    ((r : ℝ) * Real.sqrt (r : ℝ) * d * Real.sqrt (d : ℝ) *
      (stages d ε : ℝ)^2 / ε) * Real.log (2*(d : ℝ)*(stages d ε : ℝ)/δ)

def collectiveRightBudget (d : ℕ) (ε δ : ℝ) : ℝ :=
  CollectiveRightCopyBound.universalConstant * ((d : ℝ)^2/ε^2) * Real.log (1/δ)

def onecopyRightBudget (d r : ℕ) (ε δ : ℝ) : ℝ :=
  18432*(r : ℝ)*(d : ℝ)^2/ε^2 * Real.log (2*(d : ℝ)/δ)

theorem universal_constants_pos :
    0 < CollectiveBuresUpper.universalConstant ∧
    0 < OneCopyBuresUpper.universalConstant ∧
    0 < CollectiveRightCopyBound.universalConstant ∧ (0 : ℝ) < 18432 :=
  ⟨CollectiveBuresUpper.universalConstant_pos,
    OneCopyBuresUpper.universalConstant_pos,
    CollectiveRightCopyBound.universalConstant_pos, by norm_num⟩

/-- Equations (9)--(12): four uniform actual operator learners, with the
source confidence, exact logarithms, and proved integer-copy budgets. -/
theorem theorem_1_3 (I : ClassicalInputs d)
    (μ : Measure (OneCopyObservation.PureFrame (Fin d))) [IsProbabilityMeasure μ]
    (H : OneCopyObservation.HaarCoordinateMoments μ)
    (RF : SourceCopyComplexity.AllFixedOperatorRN (Fin d))
    {r : ℕ} {ε δ : ℝ} (hr : 1 ≤ r) (hrd : r ≤ d)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδhalf : δ < 1/2) :
    Collective (ι := Fin d) chiB r (ENNReal.ofReal ε) (1-ENNReal.ofReal δ)
      (collectiveBuresBudget d r ε δ) ∧
    Adaptive RF chiB r (ENNReal.ofReal ε) (1-ENNReal.ofReal δ)
      (onecopyBuresBudget d r ε δ) ∧
    Collective (ι := Fin d) chiR r (ENNReal.ofReal ε) (1-ENNReal.ofReal δ)
      (collectiveRightBudget d ε δ) ∧
    Adaptive RF chiR r (ENNReal.ofReal ε) (1-ENNReal.ofReal δ)
      (onecopyRightBudget d r ε δ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨n, Ω, mΩ, A, hA, hn⟩ := CollectiveBuresUpper.equation_9 I.selection
      I.collectiveBlocks hr (by simpa only [Fintype.card_fin] using hrd)
      hε hε1 hδ hδhalf
    letI := mΩ
    apply collective_of_learner A chiB r (ENNReal.ofReal ε) (1-ENNReal.ofReal δ) _ hA
    simpa only [collectiveBuresBudget, stages, Fintype.card_fin] using hn
  · obtain ⟨n, A, hA, hn⟩ := OneCopyBuresUpper.exists_learner I.haarBlocks I.selection
      I.bernsteinBlocks I.weylBlocks r ε δ hr
      (by simpa only [Fintype.card_fin] using hrd) hε hε1 hδ hδhalf
    apply adaptive_of_learner RF A chiB r (ENNReal.ofReal ε) (1-ENNReal.ofReal δ) _ hA
    simpa only [onecopyBuresBudget, stages, Fintype.card_fin,
      MultiscaleRefinement.commonLog] using hn
  · exact RightUpperWitnesses.equation_11 I.collectiveFull r hrd hε hε1 hδ hδhalf
  · exact RightUpperWitnesses.equation_12 I.bernsteinFull I.weylFull I.selection μ H RF r
      (by omega) hε hε1 hδ hδhalf

/-- All four original minimum copy counts at the source confidence 2/3.
Specializing the budgets at δ=1/3 gives respectively log(3L₀), log(6dL₀),
log 3 and log(6d). -/
theorem theorem_1_3_minima (I : ClassicalInputs d)
    (μ : Measure (OneCopyObservation.PureFrame (Fin d))) [IsProbabilityMeasure μ]
    (H : OneCopyObservation.HaarCoordinateMoments μ)
    (RF : SourceCopyComplexity.AllFixedOperatorRN (Fin d))
    {r : ℕ} {ε : ℝ} (hr : 1 ≤ r) (hrd : r ≤ d)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    CopyComplexity.Ncoll (ι := Fin d) chiB r (ENNReal.ofReal ε) ≤
      ENNReal.ofReal (collectiveBuresBudget d r ε (1/3)) ∧
    SourceCopyComplexity.Nonecopy RF chiB r (ENNReal.ofReal ε) ≤
      ENNReal.ofReal (onecopyBuresBudget d r ε (1/3)) ∧
    CopyComplexity.Ncoll (ι := Fin d) chiR r (ENNReal.ofReal ε) ≤
      ENNReal.ofReal (collectiveRightBudget d ε (1/3)) ∧
    SourceCopyComplexity.Nonecopy RF chiR r (ENNReal.ofReal ε) ≤
      ENNReal.ofReal (onecopyRightBudget d r ε (1/3)) := by
  have h := theorem_1_3 I μ H RF hr hrd hε hε1
    (by norm_num : (0 : ℝ) < 1/3) (by norm_num : (1/3 : ℝ) < 1/2)
  rw [RightUpperWitnesses.confidence_third] at h
  exact ⟨Ncoll_le h.1, Nonecopy_le h.2.1, Ncoll_le h.2.2.1, Nonecopy_le h.2.2.2⟩

/-- The pure-input clause of Theorem 1.3: actual collective experiments at
constant confidence, with no logarithmic factors and explicit coefficients. -/
theorem pure_collective (hd : 2 ≤ d)
    (μ : Measure (HaarFrames.Frame (Fin d) (Fin 1))) [IsProbabilityMeasure μ]
    (H : PureCovariant.HaarTensorMomentInput μ)
    (P : ∀ n, SymmetricSupport.SymmetricProjectorInput (Fin d) n)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Collective (ι := Fin d) chiB 1 (ENNReal.ofReal ε) ((2 : ℝ≥0∞)/3)
      (49*(d : ℝ)*Real.sqrt d/ε) ∧
    Collective (ι := Fin d) chiR 1 (ENNReal.ofReal ε) ((2 : ℝ≥0∞)/3)
      (25*(d : ℝ)^2/ε^2) :=
  ⟨PureUpperWitnesses.bures_collective hd μ H P hε hε1,
    PureUpperWitnesses.right_collective hd μ H P hε hε1⟩

theorem pure_minima (hd : 2 ≤ d)
    (μ : Measure (HaarFrames.Frame (Fin d) (Fin 1))) [IsProbabilityMeasure μ]
    (H : PureCovariant.HaarTensorMomentInput μ)
    (P : ∀ n, SymmetricSupport.SymmetricProjectorInput (Fin d) n)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    CopyComplexity.Ncoll (ι := Fin d) chiB 1 (ENNReal.ofReal ε) ≤
      ENNReal.ofReal (49*(d : ℝ)*Real.sqrt d/ε) ∧
    CopyComplexity.Ncoll (ι := Fin d) chiR 1 (ENNReal.ofReal ε) ≤
      ENNReal.ofReal (25*(d : ℝ)^2/ε^2) := by
  have h := pure_collective hd μ H P hε hε1
  exact ⟨Ncoll_le h.1, Ncoll_le h.2⟩

end Paper26.MainUpperBounds
