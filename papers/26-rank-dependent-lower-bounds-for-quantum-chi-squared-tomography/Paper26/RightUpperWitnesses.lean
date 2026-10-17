import Paper26.UpperBoundWitnesses
import Paper26.CollectiveRightCopyBound
import Paper26.OneCopyRightUpper

/-!
# Uniform actual operator witnesses for Equations (11) and (12)

The witnesses retain one actual experiment, chosen before every promised input.
Only the previously proved learners, integer costs, and source minimum interfaces
are transported here; no statistical upper bound is assumed.
-/
noncomputable section
open scoped ENNReal
open MeasureTheory
namespace Paper26.RightUpperWitnesses
open QuantumModel

variable {d : ℕ} [NeZero d]

lemma confidence_eq {δ : ℝ} (hδ : 0 ≤ δ) :
    ENNReal.ofReal (1-δ) = 1-ENNReal.ofReal δ := by
  rw [ENNReal.ofReal_sub 1 hδ, ENNReal.ofReal_one]

lemma confidence_third : 1-ENNReal.ofReal (1/3:ℝ) = (2:ℝ≥0∞)/3 := by
  rw [← confidence_eq (by norm_num : (0:ℝ)≤1/3)]
  rw [show (1-(1/3:ℝ)) = 2/3 by norm_num,
    ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<3)]
  norm_num

/-- Equation (11), uniformly over every rank promise r <= d, with one actual
raw collective operator learner and its proved consumed-copy bound. -/
theorem equation_11 (O : FrobeniusLearning.OWFrobeniusInput (Fin d))
    (r : ℕ) (hrd : r ≤ d) {ε δ : ℝ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hδ : 0 < δ) (hδhalf : δ < 1/2) :
    UpperBoundWitnesses.Collective (ι:=Fin d) chiR r (ENNReal.ofReal ε)
      (1-ENNReal.ofReal δ)
      (CollectiveRightCopyBound.universalConstant*((d:ℝ)^2/ε^2)*Real.log (1/δ)) := by
  obtain ⟨N,Ω,mΩ,hcost,hlearner⟩ :=
    CollectiveRightCopyBound.equation_11 O hε hε₁ hδ hδhalf
  letI := mΩ
  obtain ⟨A,hA⟩ := hlearner
  have hfull := UpperBoundWitnesses.collective_of_learner A chiR d
    (ENNReal.ofReal ε) (1-ENNReal.ofReal δ) hcost hA
  exact UpperBoundWitnesses.collective_weaken hfull hrd le_rfl le_rfl

/-- Equation (12) in the unified raw adaptive-operator witness interface.
The ordinary RN witness names the actual Born measures on fixed outcome spaces. -/
theorem equation_12
    (B : OneCopySubmatrix.MatrixBernsteinInput (Fin d))
    (Weyl : OneCopySubmatrix.WeylEigenvalueInput (Fin d))
    (S : MeasurableSpectralSelection.CompactFiberSelectionInput.{0,0})
    (μ : Measure (OneCopyObservation.PureFrame (Fin d))) [IsProbabilityMeasure μ]
    (H : OneCopyObservation.HaarCoordinateMoments μ)
    (RF : SourceCopyComplexity.AllFixedOperatorRN (Fin d))
    (r : ℕ) (hr : 0 < r) {ε δ : ℝ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hδ : 0 < δ) (hδhalf : δ < 1/2) :
    UpperBoundWitnesses.Adaptive RF chiR r (ENNReal.ofReal ε)
      (1-ENNReal.ofReal δ)
      (18432*(r:ℝ)*(d:ℝ)^2/ε^2*Real.log (2*(d:ℝ)/δ)) := by
  obtain ⟨N,A,hcost,hA⟩ := OneCopyRightUpper.eq_12_operator B Weyl S μ H
    (RF (OneCopyObservation.Outcome (Fin d)) inferInstance) r hr hε hε₁ hδ (by linarith)
  rw [confidence_eq hδ.le] at hA
  apply UpperBoundWitnesses.adaptive_of_operator RF A chiR r
    (ENNReal.ofReal ε) (1-ENNReal.ofReal δ) _ hA
  simpa only [Fintype.card_fin] using hcost.le

/-- A common collective experiment at the source confidence 2/3. -/
theorem collective_two_thirds (O : FrobeniusLearning.OWFrobeniusInput (Fin d))
    (r : ℕ) (hrd : r ≤ d) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    UpperBoundWitnesses.Collective (ι:=Fin d) chiR r (ENNReal.ofReal ε) ((2:ℝ≥0∞)/3)
      (CollectiveRightCopyBound.universalConstant*((d:ℝ)^2/ε^2)*Real.log 3) := by
  have h := equation_11 O r hrd hε hε₁
    (by norm_num : (0:ℝ)<1/3) (by norm_num : (1/3:ℝ)<1/2)
  simpa only [confidence_third, show (1/(1/3:ℝ)) = 3 by norm_num] using h

/-- A common actual adaptive operator protocol at source confidence 2/3. -/
theorem adaptive_two_thirds
    (B : OneCopySubmatrix.MatrixBernsteinInput (Fin d))
    (Weyl : OneCopySubmatrix.WeylEigenvalueInput (Fin d))
    (S : MeasurableSpectralSelection.CompactFiberSelectionInput.{0,0})
    (μ : Measure (OneCopyObservation.PureFrame (Fin d))) [IsProbabilityMeasure μ]
    (H : OneCopyObservation.HaarCoordinateMoments μ)
    (RF : SourceCopyComplexity.AllFixedOperatorRN (Fin d))
    (r : ℕ) (hr : 0 < r) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    UpperBoundWitnesses.Adaptive RF chiR r (ENNReal.ofReal ε) ((2:ℝ≥0∞)/3)
      (18432*(r:ℝ)*(d:ℝ)^2/ε^2*Real.log (6*(d:ℝ))) := by
  have h := equation_12 B Weyl S μ H RF r hr hε hε₁
    (by norm_num : (0:ℝ)<1/3) (by norm_num : (1/3:ℝ)<1/2)
  have he : 2*(d:ℝ)/(1/3:ℝ) = 6*(d:ℝ) := by ring
  simpa only [confidence_third, he] using h

/-- The raw collective minimum inherits Equation (11) with log 3. -/
theorem Ncoll_upper (O : FrobeniusLearning.OWFrobeniusInput (Fin d))
    (r : ℕ) (hrd : r ≤ d) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    CopyComplexity.Ncoll (ι:=Fin d) chiR r (ENNReal.ofReal ε) ≤
      ENNReal.ofReal (CollectiveRightCopyBound.universalConstant*((d:ℝ)^2/ε^2)*Real.log 3) :=
  UpperBoundWitnesses.Ncoll_le (collective_two_thirds O r hrd hε hε₁)

/-- The original raw one-copy minimum inherits Equation (12) with log(6d). -/
theorem Nonecopy_upper
    (B : OneCopySubmatrix.MatrixBernsteinInput (Fin d))
    (Weyl : OneCopySubmatrix.WeylEigenvalueInput (Fin d))
    (S : MeasurableSpectralSelection.CompactFiberSelectionInput.{0,0})
    (μ : Measure (OneCopyObservation.PureFrame (Fin d))) [IsProbabilityMeasure μ]
    (H : OneCopyObservation.HaarCoordinateMoments μ)
    (RF : SourceCopyComplexity.AllFixedOperatorRN (Fin d))
    (r : ℕ) (hr : 0 < r) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    SourceCopyComplexity.Nonecopy RF chiR r (ENNReal.ofReal ε) ≤
      ENNReal.ofReal (18432*(r:ℝ)*(d:ℝ)^2/ε^2*Real.log (6*(d:ℝ))) :=
  UpperBoundWitnesses.Nonecopy_le (adaptive_two_thirds B Weyl S μ H RF r hr hε hε₁)

end Paper26.RightUpperWitnesses
