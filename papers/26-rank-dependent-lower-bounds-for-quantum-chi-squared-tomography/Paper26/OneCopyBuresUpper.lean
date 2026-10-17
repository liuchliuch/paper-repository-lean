import Paper26.MultiscaleRoutineBridge
import Paper26.MultiscalePolicy
import Paper26.AtomicBatchPolicy
import Paper26.DyadicSchedule

/-!
# Actual one-copy Bures upper bound

The learner below consumes precisely `L * N` individual fresh copies. Each
stage's measurement is frozen for its N outcomes, and its next active block
and basis are computed from those actual observations. The native batch
compiler proves the macro/atomic Born-law identity. Previous good stages
supply the current mass bound; the actual submatrix routine and a first-failure
bound supply the confidence guarantee. No execution certificate, conditional
risk, product-law, or final learning conclusion is an external input.

Classical inputs are exactly the existing generic Haar coordinate moments,
Hermitian Weyl perturbation theorem, matrix Bernstein theorem, compact-fiber
Borel selection theorem, and (only for the source minimum) fixed-space operator
Radon--Nikodym theorem. All are quantified in their original generic interfaces.
-/
noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal
open MeasureTheory ProbabilityTheory

namespace Paper26.OneCopyBuresUpper
open QuantumModel ContinuousPOVM AdaptiveModel
open MultiscaleUpdate MultiscaleMatrixBridge MultiscaleRefinement MultiscaleRoutineBridge

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
local instance matrixMeasurableSpace (m n : Type*) : MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))

abbrev AtomicOutcome := OneCopyStageRoutine.Outcome ι
abbrev BatchOutcome (N : ℕ) := Fin N → AtomicOutcome (ι := ι)

def decode (B : MeasurableSpectralSelection.CompactFiberSelectionInput.{0,0})
    (N r : ℕ) : ℕ → BatchOutcome (ι := ι) N → EstimateFamily (ι := ι) :=
  fun _ => decodeStage B N r

omit [Nonempty ι] in
theorem measurable_decode (B : MeasurableSpectralSelection.CompactFiberSelectionInput.{0,0})
    (N r k : ℕ) : Measurable (decode (ι := ι) B N r k) := measurable_decodeStage B N r

def control (B : MeasurableSpectralSelection.CompactFiberSelectionInput.{0,0})
    (r N L : ℕ) (j : Fin L) : History PUnit (BatchOutcome (ι := ι) N) j.val →
      OneCopyStageRoutine.State ι :=
  MultiscalePolicy.control B (dyadicLower L) (decode B N r) j.val

omit [Nonempty ι] in
theorem measurable_control (B : MeasurableSpectralSelection.CompactFiberSelectionInput.{0,0})
    (r N L : ℕ) (j : Fin L) : Measurable (control (ι := ι) B r N L j) :=
  MultiscalePolicy.measurable_control B (dyadicLower L) (decode B N r) (measurable_decode B N r) j.val

def outputEstimator (B : MeasurableSpectralSelection.CompactFiberSelectionInput.{0,0})
    (r N L : ℕ) [NeZero L] : Estimator ι (History PUnit (BatchOutcome (ι := ι) N) L) :=
  MultiscalePolicy.estimator B (dyadicLower L) (decode B N r) (measurable_decode B N r) (dyadicLower_pos L)

/-- The actual adaptive learner, one atomic quantum measurement per copy. -/
def learner (H : OneCopyStageRoutine.HaarFamily ι)
    (B : MeasurableSpectralSelection.CompactFiberSelectionInput.{0,0})
    (r N L : ℕ) [NeZero L] : AdaptiveModel.Learner ι PUnit (AtomicOutcome (ι := ι)) (L * N) :=
  AtomicBatchPolicy.learner (OneCopyStageRoutine.step H) (control B r N L)
    (measurable_control B r N L) (outputEstimator B r N L)

def policy (H : OneCopyStageRoutine.HaarFamily ι)
    (B : MeasurableSpectralSelection.CompactFiberSelectionInput.{0,0})
    (r N L : ℕ) (ρ : Density ι) : StagePolicy.Policy PUnit (BatchOutcome (ι := ι) N) L :=
  AtomicBatchPolicy.macroPolicy (OneCopyStageRoutine.step H) (control B r N L)
    (measurable_control B r N L) ρ

/-- Complement conversion is a probability theorem, not an extra conditional
failure premise for the learning routine. -/
theorem failure_le_of_success_ge {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (f : Ω → ℝ) (hf : Measurable f)
    (η β : ℝ) (_hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hs : ENNReal.ofReal (1 - β) ≤ ν {z | f z ≤ η}) :
    ν {z | ¬ f z ≤ η} ≤ ENNReal.ofReal β := by
  have hg : MeasurableSet {z | f z ≤ η} := measurableSet_le hf measurable_const
  have he : {z | ¬ f z ≤ η} = {z | f z ≤ η}ᶜ := rfl
  rw [he, measure_compl hg (measure_ne_top ν _), measure_univ]
  apply (tsub_le_tsub_left hs 1).trans_eq
  calc
    (1 : ℝ≥0∞) - ENNReal.ofReal (1 - β) = ENNReal.ofReal (1 - (1 - β)) := by
      rw [ENNReal.ofReal_sub 1 (sub_nonneg.mpr hβ1), ENNReal.ofReal_one]
    _ = ENNReal.ofReal β := by congr 1; ring

section StatisticalInputs
variable (H : OneCopyStageRoutine.HaarFamily ι)
    (B : MeasurableSpectralSelection.CompactFiberSelectionInput.{0,0})
    (Bernstein : ∀ (S : Finset ι) (hS : S.Nonempty),
      @OneCopySubmatrix.MatrixBernsteinInput (MultiscaleUpdate.BlockIndex S) inferInstance inferInstance
        (OneCopyStageRoutine.blockIndex_nonempty S hS))
    (Weyl : ∀ S : Finset ι, OneCopySubmatrix.WeylEigenvalueInput (MultiscaleUpdate.BlockIndex S))
include Bernstein Weyl

/-- Conditional failures of the real atomic policy satisfy the allocated
budget on exactly the previously successful histories. -/
theorem conditional_failure (r L : ℕ) [NeZero L] (ε δ : ℝ)
    (hr : 1 ≤ r) (hrd : r ≤ Fintype.card ι) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ < 1 / 2)
    (hSchedule : L = dyadicStages (Fintype.card ι) (ε / 16))
    (ρ : Density ι) (hrank : ρ.matrix.rank ≤ r) (k : ℕ) (hk : k < L)
    (h : History PUnit (BatchOutcome (ι := ι)
      (MultiscaleOneCopyCost.stageCopies r (Fintype.card ι) L (ε / 16) δ)) k)
    (hh : h ∈ StagePolicy.goodPrefix
      (MultiscalePolicy.good B (dyadicLower L)
        (decode B (MultiscaleOneCopyCost.stageCopies r (Fintype.card ι) L (ε / 16) δ) r)
        ρ (stageAccuracy (ε / 16) L)) k) :
    let N := MultiscaleOneCopyCost.stageCopies r (Fintype.card ι) L (ε / 16) δ
    (policy H B r N L ρ).transition ⟨k, hk⟩ h
      {y | (h, y) ∉ MultiscalePolicy.good B (dyadicLower L) (decode B N r) ρ (stageAccuracy (ε / 16) L) k} ≤
        ENNReal.ofReal (δ / (L : ℝ)) := by
  let N := MultiscaleOneCopyCost.stageCopies r (Fintype.card ι) L (ε / 16) δ
  let D := decode (ι := ι) B N r
  let F := MultiscalePolicy.records (L := L) D k h
  let st := execute B L (dyadicLower L) F k
  let f : BatchOutcome (ι := ι) N → ℝ := fun z => stateError ρ (st, decodeStage B N r z)
  have hs := conditional_scheduled_success H B Bernstein Weyl L ρ F r (ε / 16) δ hr hrd hrank
    (by positivity) (by linarith) hδ hδ1 hSchedule ⟨k, hk⟩
    (MultiscalePolicy.goodPrefix_accuracy B (dyadicLower L) D ρ (stageAccuracy (ε / 16) L) k h hh)
  have hf : Measurable f := by
    have hst : Measurable (fun _z : BatchOutcome (ι := ι) N => st) := measurable_const
    have hm := (measurable_stateError ρ).comp (hst.prodMk (measurable_decodeStage B N r))
    exact hm
  have hβ : 0 < δ / (L : ℝ) := MultiscaleOneCopyCost.stageFailure_pos hδ (NeZero.pos L)
  have hβ1 : δ / (L : ℝ) ≤ 1 :=
    (MultiscaleOneCopyCost.stageFailure_lt_half hδ hδ1 (NeZero.pos L)).le.trans (by norm_num)
  have hb := failure_le_of_success_ge
    (Measure.pi (fun _ : Fin N => (OneCopyStageRoutine.measurement H st.1 st.2.1).outcomeMeasure ρ))
    f hf (stageAccuracy (ε / 16) L ⟨k, hk⟩) (δ / (L : ℝ)) hβ.le hβ1 hs
  change (StagePolicy.quantumBlockKernel
    (StagePolicy.pullbackStep (OneCopyStageRoutine.step H) (control B r N L ⟨k, hk⟩)
      (measurable_control B r N L ⟨k, hk⟩)) ρ N) h _ ≤ _
  rw [StagePolicy.quantumBlockKernel_apply]
  simp only [StagePolicy.pullbackStep_bornKernel, Kernel.comap_apply]
  rw [OneCopyStageRoutine.step_bornKernel]
  simpa only [MultiscalePolicy.good, dif_pos hk, Set.mem_setOf_eq, control,
    MultiscalePolicy.control, MultiscalePolicy.state, decode, D, F, st, f] using hb

/-- The macro success event is proved for every actual rank-at-most-r state. -/
theorem policy_success (r L : ℕ) [NeZero L] (ε δ : ℝ)
    (hr : 1 ≤ r) (hrd : r ≤ Fintype.card ι) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ < 1 / 2)
    (hSchedule : L = dyadicStages (Fintype.card ι) (ε / 16))
    (ρ : Density ι) (hrank : ρ.matrix.rank ≤ r) :
    let N := MultiscaleOneCopyCost.stageCopies r (Fintype.card ι) L (ε / 16) δ
    1 - ENNReal.ofReal δ ≤ (policy H B r N L ρ).transcriptLaw
      {h | chiB ρ ((outputEstimator B r N L).estimate h) ≤ ENNReal.ofReal ε} := by
  apply MultiscalePolicy.policy_success B _ (measurable_decode B _ r) _ ρ hε hε1 hδ.le hSchedule
  intro k hk h hh
  exact conditional_failure H B Bernstein Weyl r L ε δ hr hrd hε hε1 hδ hδ1 hSchedule ρ hrank k hk h hh

/-- True uniform learning promise for the actual `L*N`-copy one-copy learner. -/
theorem learnsRank (r L : ℕ) [NeZero L] (ε δ : ℝ)
    (hr : 1 ≤ r) (hrd : r ≤ Fintype.card ι) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ < 1 / 2)
    (hSchedule : L = dyadicStages (Fintype.card ι) (ε / 16)) :
    let N := MultiscaleOneCopyCost.stageCopies r (Fintype.card ι) L (ε / 16) δ
    (learner H B r N L).LearnsRank chiB r (ENNReal.ofReal ε) (1 - ENNReal.ofReal δ) := by
  dsimp only
  unfold learner
  apply (AtomicBatchPolicy.learner_learnsRank_iff _ _ _ _ _ _ _ _).mpr
  intro ρ hrank
  have hLoss : Measurable (fun σ : Density ι => chiB ρ σ) :=
    JordanLossMeasurability.measurable_chiB_comp (fun _ : Density ι => ρ) id measurable_const measurable_id
  refine ⟨measurableSet_le (hLoss.comp (outputEstimator B r _ L).measurable_estimate) measurable_const, ?_⟩
  exact policy_success H B Bernstein Weyl r L ε δ hr hrd hε hε1 hδ hδ1 hSchedule ρ hrank

end StatisticalInputs

/-- An explicit universal constant, including stage rounding. -/
def universalConstant : ℝ := 16 * (2304 + 1 / Real.log 2)

theorem universalConstant_pos : 0 < universalConstant := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold universalConstant
  positivity

omit [DecidableEq ι] [Nonempty ι] in
/-- The fresh-copy count has the exact source exponents and logarithmic factor. -/
theorem copyBound (r L : ℕ) (ε δ : ℝ) (hr : 1 ≤ r) (hrd : r ≤ Fintype.card ι)
    (hL : 0 < L) (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ((L * MultiscaleOneCopyCost.stageCopies r (Fintype.card ι) L (ε / 16) δ : ℕ) : ℝ) ≤
      universalConstant * ((r : ℝ) * Real.sqrt r * (Fintype.card ι : ℝ) *
        Real.sqrt (Fintype.card ι) * (L : ℝ) ^ 2 / ε) * commonLog (Fintype.card ι) L δ := by
  have h := MultiscaleOneCopyCost.totalCopies_le r (Fintype.card ι) L (ε / 16) δ hr hrd hL
    (by positivity) (by linarith) hδ hδ1
  calc
    _ = (MultiscaleOneCopyCost.totalCopies r (Fintype.card ι) L (ε / 16) δ : ℝ) := by
      simp only [MultiscaleOneCopyCost.totalCopies, Nat.mul_comm]
    _ ≤ _ := h
    _ = _ := by unfold universalConstant; ring

section SourceSchedule
variable (H : OneCopyStageRoutine.HaarFamily ι)
    (B : MeasurableSpectralSelection.CompactFiberSelectionInput.{0,0})
    (Bernstein : ∀ (S : Finset ι) (hS : S.Nonempty),
      @OneCopySubmatrix.MatrixBernsteinInput (MultiscaleUpdate.BlockIndex S) inferInstance inferInstance
        (OneCopyStageRoutine.blockIndex_nonempty S hS))
    (Weyl : ∀ S : Finset ι, OneCopySubmatrix.WeylEigenvalueInput (MultiscaleUpdate.BlockIndex S))
include H B Bernstein Weyl

/-- An actual finite one-copy learner with a uniform rank promise, using
exactly the source's ceiling-logarithm stage schedule. -/
theorem exists_learner (r : ℕ) (ε δ : ℝ) (hr : 1 ≤ r) (hrd : r ≤ Fintype.card ι)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ < 1 / 2) :
    ∃ (n : ℕ) (A : AdaptiveModel.Learner ι PUnit (AtomicOutcome (ι := ι)) n),
      A.LearnsRank chiB r (ENNReal.ofReal ε) (1 - ENNReal.ofReal δ) ∧
      (n : ℝ) ≤ universalConstant *
        ((r : ℝ) * Real.sqrt r * (Fintype.card ι : ℝ) * Real.sqrt (Fintype.card ι) *
          (DyadicSchedule.sourceStages (Fintype.card ι) ε : ℝ) ^ 2 / ε) *
        commonLog (Fintype.card ι) (DyadicSchedule.sourceStages (Fintype.card ι) ε) δ := by
  let L := DyadicSchedule.sourceStages (Fintype.card ι) ε
  have hLpos : 0 < L := DyadicSchedule.sourceStages_pos _ hε hε1 Fintype.card_pos
  letI : NeZero L := ⟨Nat.ne_of_gt hLpos⟩
  have hSchedule : L = dyadicStages (Fintype.card ι) (ε / 16) :=
    (DyadicSchedule.sourceStages_eq _ hε Fintype.card_pos).symm
  let N := MultiscaleOneCopyCost.stageCopies r (Fintype.card ι) L (ε / 16) δ
  refine ⟨L * N, learner H B r N L, ?_, ?_⟩
  · exact learnsRank H B Bernstein Weyl r L ε δ hr hrd hε hε1 hδ hδ1 hSchedule
  · exact copyBound r L ε δ hr hrd hLpos hε hε1 hδ (by linarith)

/-- Equation 10 as a bound on the original raw-operator one-copy minimum.
The constant is explicit and independent of dimension, rank and accuracy. -/
theorem equation_10 (RN : SourceCopyComplexity.AllFixedOperatorRN ι)
    (r : ℕ) (ε : ℝ) (hr : 1 ≤ r) (hrd : r ≤ Fintype.card ι)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    SourceCopyComplexity.Nonecopy RN chiB r (ENNReal.ofReal ε) ≤ ENNReal.ofReal
      (universalConstant *
        ((r : ℝ) * Real.sqrt r * (Fintype.card ι : ℝ) * Real.sqrt (Fintype.card ι) *
          (DyadicSchedule.sourceStages (Fintype.card ι) ε : ℝ) ^ 2 / ε) *
        Real.log (6 * (Fintype.card ι : ℝ) * DyadicSchedule.sourceStages (Fintype.card ι) ε)) := by
  obtain ⟨n, A, hA, hn⟩ := exists_learner H B Bernstein Weyl r ε (1 / 3) hr hrd hε hε1
    (by norm_num) (by norm_num)
  have hconfidence : (1 : ℝ≥0∞) - ENNReal.ofReal (1 / 3 : ℝ) = (2 : ℝ≥0∞) / 3 := by
    calc
      _ = ENNReal.ofReal (1 - (1 / 3 : ℝ)) := by
        rw [ENNReal.ofReal_sub 1 (by norm_num : (0 : ℝ) ≤ 1 / 3), ENNReal.ofReal_one]
      _ = (2 : ℝ≥0∞) / 3 := by norm_num [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3)]
  rw [hconfidence] at hA
  have hlog : commonLog (Fintype.card ι) (DyadicSchedule.sourceStages (Fintype.card ι) ε) (1 / 3) =
      Real.log (6 * (Fintype.card ι : ℝ) * DyadicSchedule.sourceStages (Fintype.card ι) ε) := by
    unfold commonLog
    congr 1
    ring
  rw [hlog] at hn
  apply (StagePolicy.Nonecopy_le A RN chiB r (ENNReal.ofReal ε) hA).trans
  simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hn

end SourceSchedule
end Paper26.OneCopyBuresUpper

