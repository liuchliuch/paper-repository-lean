import Paper26.MultiscaleExecutionFacts
import Paper26.MultiscaleMatrixBridge
import Paper26.JordanLossMeasurability

/-!
# The actual multiscale density-matrix estimator

The estimator is a single Borel map of recorded PSD block estimates. It does
not depend on the unknown density matrix. Its execution certificate is derived
from the actual recursion; its loss guarantee is derived from ordinary errors
of the current compressed block estimates. No certificate-existence, final
error, success probability, or learner field is an input.
-/
noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal
open MeasureTheory

namespace Paper26.MultiscaleEstimator
open QuantumModel ContinuousPOVM Normalization ShellAccounting
open MultiscaleUpdate MultiscaleExecutionFacts MultiscaleMatrixBridge MultiscaleRefinement

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
local instance matrixMeasurableSpace (m n : Type*) : MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))

/-- The error of the actual current block estimate before its eigenbasis update. -/
def currentError (B : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (L : ℕ) (lower : Fin L → ℝ) (ρ : Density ι) (j : Fin L)
    (F : Fin L → EstimateFamily (ι := ι)) : ℝ :=
  stateError ρ (execute B L lower F j.val, F j)

theorem measurable_currentError (B : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (L : ℕ) (lower : Fin L → ℝ) (ρ : Density ι) (j : Fin L) :
    Measurable (currentError B L lower ρ j) :=
  (measurable_stateError ρ).comp ((measurable_execute B L lower j.val).prodMk (measurable_pi_apply j))

/-- The native execution certificate receives exactly the real block-routine
error, with no coordinate or support assumption left to the caller. -/
theorem stageData_localError (B : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (L : ℕ) [NeZero L] (lower : Fin L → ℝ) (ρ : Density ι)
    (F : Fin L → EstimateFamily (ι := ι)) (j : Fin L) :
    frobeniusSq ((stageData B L lower F).localError ρ j) = currentError B L lower ρ j F := by
  have hm : (stageData B L lower F).localError ρ j =
      mask (fun i => i ∈ activeAt B L lower F j.val)
        (coordinates ((basisAt B L lower F j.val *
          selectedUpdate B (activeAt B L lower F j.val) (F j (activeAt B L lower F j.val)) :
            Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) ρ.matrix -
          diagonalMatrix (stageValues B L lower F j)) := by
    ext i k
    simp only [StageData.localError, mask, stageData_active, stageData_basis, basis_next,
      stageData_spectrum]
  rw [hm, stageValues, localError_frobeniusSq]
  rfl

theorem trace_embedBlock (S : Finset ι) (C : Matrix (BlockIndex S) (BlockIndex S) ℂ) :
    Matrix.trace (embedBlock S C) = Matrix.trace C := by
  rw [embedBlock, CoordinateTransport.matrix_trace]
  simp [Matrix.trace, Fintype.sum_sum_type, Matrix.fromBlocks]

/-- The mass of the actual block measured by a routine is the mass in the
native execution certificate after its within-block eigenbasis update. -/
theorem compressedBlock_trace_stageData
    (B : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (L : ℕ) [NeZero L] (lower : Fin L → ℝ) (ρ : Density ι)
    (F : Fin L → EstimateFamily (ι := ι)) (j : Fin L) :
    Matrix.trace (compressedBlock (activeAt B L lower F j.val) (basisAt B L lower F j.val) ρ) =
      Matrix.trace ((stageData B L lower F).trueBlock ρ j) := by
  let S := activeAt B L lower F j.val
  let U := basisAt B L lower F j.val
  let C := F j S
  let V := selectedUpdate B S C
  have hc : coordinates (V : Matrix ι ι ℂ) (coordinates (U : Matrix ι ι ℂ) ρ.matrix) =
      coordinates ((U * V : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) ρ.matrix := by
    simp only [coordinates, Matrix.UnitaryGroup.mul_val, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have ht : mask (fun i => i ∈ S)
      (coordinates ((U * V : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) ρ.matrix) =
      (stageData B L lower F).trueBlock ρ j := by
    ext i k
    simp only [StageData.trueBlock, mask, stageData_active, stageData_basis, basis_next]
    rfl
  calc
    _ = Matrix.trace (embedBlock S (compressedBlock S U ρ)) := (trace_embedBlock S _).symm
    _ = Matrix.trace (mask (fun i => i ∈ S) (coordinates (U : Matrix ι ι ℂ) ρ.matrix)) := by
      rw [compressedBlock, embedBlock_mask]
    _ = Matrix.trace (coordinates (V : Matrix ι ι ℂ)
        (mask (fun i => i ∈ S) (coordinates (U : Matrix ι ι ℂ) ρ.matrix))) :=
      (MultiscaleRefinement.trace_coordinates V _).symm
    _ = _ := by
      rw [MultiscaleRefinement.coordinates_mask _ V _ (selectedUpdate_cross_zero B S C), hc, ht]

/-- Conditional mass bound: only earlier successful estimates are needed.
Future estimates in the recorded tuple remain completely arbitrary. -/
theorem current_mass_le_allowance
    (B : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (L : ℕ) [NeZero L] (ρ : Density ι) (F : Fin L → EstimateFamily (ι := ι))
    {r : ℕ} {e : ℝ} (hr : ρ.matrix.rank ≤ r) (j : Fin L)
    (haccuracy : ∀ k : Fin L, k.val < j.val →
      currentError B L (dyadicLower L) ρ k F ≤ stageAccuracy e L k) :
    (Matrix.trace (compressedBlock (activeAt B L (dyadicLower L) F j.val)
      (basisAt B L (dyadicLower L) F j.val) ρ)).re ≤ massAllowance r e L j := by
  rw [compressedBlock_trace_stageData]
  unfold massAllowance
  split_ifs with hj
  · have hb : (stageData B L (dyadicLower L) F).trueBlock ρ j =
        coordinates ((stageData B L (dyadicLower L) F).basis j : Matrix ι ι ℂ) ρ.matrix := by
      ext i k
      simp [StageData.trueBlock, mask, StageData.active, hj]
    rw [hb, MultiscaleRefinement.trace_coordinates, ρ.trace_one]
    norm_num
  · apply (stageData B L (dyadicLower L) F).trueBlock_mass_bound ρ j (previousStage j hj)
      (by change j.val = j.val - 1 + 1; omega) (dyadicLower_pos L _) hr
    rw [stageData_localError]
    exact haccuracy _ (by change j.val - 1 < j.val; omega)

section Nonempty
variable [Nonempty ι]

/-- The actual returned density is the normalized positive final matrix. -/
def estimate (B : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (L : ℕ) [NeZero L] (lower : Fin L → ℝ) (hlower : ∀ j, 0 < lower j)
    (F : Fin L → EstimateFamily (ι := ι)) : Density ι :=
  (stageData B L lower F).normalizedOutput hlower

theorem estimate_matrix (B : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (L : ℕ) [NeZero L] (lower : Fin L → ℝ) (hlower : ∀ j, 0 < lower j)
    (F : Fin L → EstimateFamily (ι := ι)) :
    (estimate B L lower hlower F).matrix =
      (((1 / (Matrix.trace (finalMatrix B L lower F)).re : ℝ) : ℂ)) • finalMatrix B L lower F := by
  change (((1 / (Matrix.trace (stageData B L lower F).outputMatrix).re : ℝ) : ℂ)) •
    (stageData B L lower F).outputMatrix = _
  rw [stageData_outputMatrix]

theorem estimate_posDef (B : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (L : ℕ) [NeZero L] (lower : Fin L → ℝ) (hlower : ∀ j, 0 < lower j)
    (F : Fin L → EstimateFamily (ι := ι)) : (estimate B L lower hlower F).matrix.PosDef :=
  (stageData B L lower F).normalizedOutput_posDef hlower

theorem measurable_estimate_matrix (B : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (L : ℕ) [NeZero L] (lower : Fin L → ℝ) (hlower : ∀ j, 0 < lower j) :
    Measurable (fun F : Fin L → EstimateFamily (ι := ι) => (estimate B L lower hlower F).matrix) := by
  have hm := measurable_finalMatrix (ι := ι) B L lower
  have ht : Measurable (fun F : Fin L → EstimateFamily (ι := ι) =>
      (Matrix.trace (finalMatrix B L lower F)).re) := by
    have hs : Measurable (fun F : Fin L → EstimateFamily (ι := ι) =>
        ∑ i, finalMatrix B L lower F i i) :=
      Finset.measurable_sum Finset.univ fun i _ =>
        (measurable_pi_apply i).comp ((measurable_pi_apply i).comp hm)
    exact hs.re
  have h1 : Measurable (fun _F : Fin L → EstimateFamily (ι := ι) => (1 : ℝ)) := measurable_const
  have hc := (h1.div ht).complex_ofReal
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro k
  simp only [estimate_matrix, Matrix.smul_apply, smul_eq_mul]
  exact hc.mul ((measurable_pi_apply k).comp ((measurable_pi_apply i).comp hm))

theorem measurable_estimate (B : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (L : ℕ) [NeZero L] (lower : Fin L → ℝ) (hlower : ∀ j, 0 < lower j) :
    Measurable (estimate (ι := ι) B L lower hlower) := by
  intro s hs
  rcases hs with ⟨t, ht, rfl⟩
  exact measurable_estimate_matrix B L lower hlower ht

def estimator (B : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (L : ℕ) [NeZero L] (lower : Fin L → ℝ) (hlower : ∀ j, 0 < lower j) :
    Estimator ι (Fin L → EstimateFamily (ι := ι)) where
  estimate := estimate B L lower hlower
  measurable_estimate := measurable_estimate B L lower hlower

/-- Full deterministic Section 5.3 for the actual Borel output of the actual
recursive algorithm. The sole accuracy premises concern actual block matrices. -/
theorem actual_chiB_epsilon (B : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (L : ℕ) [NeZero L] (ρ : Density ι) (F : Fin L → EstimateFamily (ι := ι))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hL : L = dyadicStages (Fintype.card ι) (ε / 16))
    (haccuracy : ∀ j, currentError B L (dyadicLower L) ρ j F ≤ stageAccuracy (ε / 16) L j) :
    chiB ρ (estimate B L (dyadicLower L) (dyadicLower_pos L) F) < ENNReal.ofReal ε := by
  exact scheduled_chiB_epsilon (stageData B L (dyadicLower L) F) ρ hε hε1 hL
    (fun j => (stageData_localError B L (dyadicLower L) ρ F j).trans_le (haccuracy j))

omit [Nonempty ι] in
/-- Every actual accuracy event is Borel. -/
theorem measurableSet_allAccurate (B : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (L : ℕ) (lower : Fin L → ℝ) (ρ : Density ι) (η : Fin L → ℝ) :
    MeasurableSet {F : Fin L → EstimateFamily (ι := ι) | ∀ j, currentError B L lower ρ j F ≤ η j} := by
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter fun j => measurableSet_le (measurable_currentError B L lower ρ j) measurable_const

end Nonempty
end Paper26.MultiscaleEstimator
