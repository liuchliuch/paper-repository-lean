import Paper26.MultiscaleEstimator
import Paper26.OneCopyStageRoutine
import Paper26.MultiscaleOneCopyCost

/-!
# Actual block-routine risk for the multiscale recursion

The one-copy routine measures the real active columns of the current ambient
unitary. Its matrix block is identified entry by entry with the compression
used by the execution, and its recorded estimates supply a single Borel map
into the algorithm's estimate data. Conditional success remains a theorem
about the actual product Born law, with no independent-data premise.
-/
noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal
open MeasureTheory

namespace Paper26.MultiscaleRoutineBridge
open QuantumModel ShellAccounting MultiscaleUpdate MultiscaleMatrixBridge

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

local instance matrixMeasurableSpace (m n : Type*) : MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))

/-- The physical projection measurement acts on exactly the same actual block. -/
theorem trueBlock_eq_compressedBlock (S : Finset ι) (U : Matrix.unitaryGroup ι ℂ) (ρ : Density ι) :
    OneCopySubmatrix.trueBlock (OneCopyStageRoutine.activeColumns U S) ρ = compressedBlock S U ρ := by
  ext i k
  simp only [OneCopySubmatrix.trueBlock, OneCopyStageRoutine.activeColumns, compressedBlock,
    Normalization.coordinates, Matrix.submatrix_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem frobeniusSq_sub_comm {m n : Type*} [Fintype m] [Fintype n]
    (A C : Matrix m n ℂ) : frobeniusSq (A - C) = frobeniusSq (C - A) := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  simp only [Matrix.sub_apply, norm_sub_rev]

/-- A full record is constructed from the actual sample tuple. Estimates of
unused subsets are available as harmless Borel coordinates. -/
def decodeStage (B : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u}) (N r : ℕ)
    (z : Fin N → OneCopyStageRoutine.Outcome ι) : EstimateFamily (ι := ι) :=
  fun S => OneCopyStageRoutine.positiveEstimate B S N r z

theorem measurable_decodeStage (B : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (N r : ℕ) : Measurable (decodeStage (ι := ι) B N r) := by
  apply measurable_pi_lambda
  intro S
  exact OneCopyStageRoutine.positiveEstimate_measurable B S N r

/-- The routine's reported Frobenius event is precisely the actual recursion's
block-accuracy event, including the sign reversal in the difference. -/
theorem decoded_stateError (B : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (N r : ℕ) (st : MultiscaleUpdate.State (ι := ι)) (ρ : Density ι)
    (z : Fin N → OneCopyStageRoutine.Outcome ι) :
    stateError ρ (st, decodeStage B N r z) = frobeniusSq
      (OneCopyStageRoutine.estimate B st.1 N r z -
        OneCopySubmatrix.trueBlock (OneCopyStageRoutine.activeColumns st.2.1 st.1) ρ) := by
  rw [stateError, stateErrorFiber, blockError, trueBlock_eq_compressedBlock, frobeniusSq_sub_comm]
  rfl

/-- Uniform conditional risk under the actual independent fresh-copy Born law;
all dependence on the current state is in the actual measurement control. -/
theorem decoded_success_of_global_budget [Nonempty ι]
    (H : OneCopyStageRoutine.HaarFamily ι)
    (B : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (Bernstein : ∀ (S : Finset ι) (hS : S.Nonempty),
      @OneCopySubmatrix.MatrixBernsteinInput (MultiscaleUpdate.BlockIndex S) inferInstance inferInstance
        (OneCopyStageRoutine.blockIndex_nonempty S hS))
    (Weyl : ∀ S : Finset ι, OneCopySubmatrix.WeylEigenvalueInput (MultiscaleUpdate.BlockIndex S))
    (st : MultiscaleUpdate.State (ι := ι)) (ρ : Density ι)
    (r N : ℕ) (hr : 0 < r) (hrank : ρ.matrix.rank ≤ r) (hN : 0 < N)
    (W η β : ℝ)
    (hW : (Matrix.trace (compressedBlock st.1 st.2.1 ρ)).re ≤ W)
    (hη : 0 < η) (hβ : 0 < β) (hβ₁ : β < 1/2)
    (hbudget : OneCopySubmatrix.copyBudget (ι := ι) r W η β ≤ (N : ℝ)) :
    ENNReal.ofReal (1 - β) ≤
      Measure.pi (fun _ : Fin N => (OneCopyStageRoutine.measurement H st.1 st.2.1).outcomeMeasure ρ)
        {z | stateError ρ (st, decodeStage B N r z) ≤ η} := by
  have he : {z : Fin N → OneCopyStageRoutine.Outcome ι | stateError ρ (st, decodeStage B N r z) ≤ η} =
      {z | frobeniusSq (OneCopyStageRoutine.estimate B st.1 N r z -
        OneCopySubmatrix.trueBlock (OneCopyStageRoutine.activeColumns st.2.1 st.1) ρ) ≤ η} := by
    ext z
    simp only [Set.mem_setOf_eq, decoded_stateError]
  rw [he]
  by_cases hS : st.1.Nonempty
  · exact OneCopyStageRoutine.estimate_success_of_global_budget H B st.1 hS (Bernstein _ hS) (Weyl _)
      st.2.1 ρ r N hr hrank hN W η β (by rwa [trueBlock_eq_compressedBlock]) hη hβ hβ₁ hbudget
  · exact OneCopyStageRoutine.estimate_success_empty H B st.1 hS st.2.1 ρ N r η β hη.le hβ.le

/-- The fully scheduled conditional stage guarantee has no free copy-budget,
mass, certificate or risk field. Only preceding actual accuracy is assumed. -/
theorem conditional_scheduled_success [Nonempty ι]
    (H : OneCopyStageRoutine.HaarFamily ι)
    (B : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (Bernstein : ∀ (S : Finset ι) (hS : S.Nonempty),
      @OneCopySubmatrix.MatrixBernsteinInput (MultiscaleUpdate.BlockIndex S) inferInstance inferInstance
        (OneCopyStageRoutine.blockIndex_nonempty S hS))
    (Weyl : ∀ S : Finset ι, OneCopySubmatrix.WeylEigenvalueInput (MultiscaleUpdate.BlockIndex S))
    (L : ℕ) [NeZero L] (ρ : Density ι) (F : Fin L → EstimateFamily (ι := ι))
    (r : ℕ) (e δ : ℝ) (hr : 1 ≤ r) (hrd : r ≤ Fintype.card ι)
    (hrank : ρ.matrix.rank ≤ r) (he : 0 < e) (he₁ : e ≤ 1)
    (hδ : 0 < δ) (hδ₁ : δ < 1/2)
    (hSchedule : L = MultiscaleRefinement.dyadicStages (Fintype.card ι) e) (j : Fin L)
    (haccuracy : ∀ k : Fin L, k.val < j.val →
      MultiscaleEstimator.currentError B L (MultiscaleRefinement.dyadicLower L) ρ k F ≤
        MultiscaleRefinement.stageAccuracy e L k) :
    let N := MultiscaleOneCopyCost.stageCopies r (Fintype.card ι) L e δ
    let st := execute B L (MultiscaleRefinement.dyadicLower L) F j.val
    ENNReal.ofReal (1 - δ / (L : ℝ)) ≤
      Measure.pi (fun _ : Fin N => (OneCopyStageRoutine.measurement H st.1 st.2.1).outcomeMeasure ρ)
        {z | stateError ρ (st, decodeStage B N r z) ≤ MultiscaleRefinement.stageAccuracy e L j} := by
  dsimp only
  have hparams := MultiscaleOneCopyCost.actual_stage_parameters (ι := ι) r L e δ hr hrd
    (NeZero.pos L) he he₁ hδ hδ₁ hSchedule j
  apply decoded_success_of_global_budget H B Bernstein Weyl _ ρ r _ (by omega) hrank hparams.1
    (MultiscaleRefinement.massAllowance r e L j) (MultiscaleRefinement.stageAccuracy e L j) (δ / (L : ℝ))
    (MultiscaleEstimator.current_mass_le_allowance B L ρ F hrank j haccuracy)
    hparams.2.1 hparams.2.2.1 hparams.2.2.2.1
  exact MultiscaleOneCopyCost.actual_stageBudget_le_stageCopies r L e δ hr hrd (NeZero.pos L)
    he hδ (by linarith) hSchedule j

end Paper26.MultiscaleRoutineBridge

