import Paper26.CollectiveStageFamily
import Paper26.MultiscalePolicy
import Paper26.MultiscaleCollectiveCost
import Paper26.ProductOutcomeStep
import Paper26.DyadicSchedule
import Paper26.JordanLossMeasurability

/-!
# The complete actual collective Bures upper-bound learner

All stage experiments, the common macro-copy budget, product outcome space
and final estimator are fixed before the unknown input. Native conditional
Born bounds are used only on successful past histories. No law, risk, mass
allowance or execution-certificate hypothesis is an external model field.
-/
noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal
namespace Paper26.CollectiveBuresUpper
open MeasureTheory QuantumModel ContinuousPOVM AdaptiveModel MultiscaleRefinement
open MultiscaleUpdate CollectiveFiltering

local instance matrixMeasurableSpace (m n : Type*) : MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
local instance : MeasurableSpace (Finset ι) := ⊤

/-- Original numerical promises and the two already registered generic
supporting inputs. There is no statistical conclusion in these parameters. -/
structure Parameters (ι : Type) [Fintype ι] [DecidableEq ι] where
  r : ℕ
  ε : ℝ
  δ : ℝ
  hr : 1 ≤ r
  hrd : r ≤ Fintype.card ι
  hε : 0 < ε
  hε1 : ε ≤ 1
  hδ : 0 < δ
  hδhalf : δ < 1/2
  selection : MeasurableSpectralSelection.CompactFiberSelectionInput.{0,0}
  ow : ∀ A : Finset ι, A.Nonempty → FrobeniusLearning.OWFrobeniusInput (CollectiveStageRoutine.Active A)

namespace Parameters
variable (P : Parameters ι)

def stages : ℕ := DyadicSchedule.sourceStages (Fintype.card ι) P.ε

def copies : ℕ := MultiscaleCollectiveCost.globalN P.r (Fintype.card ι) P.stages (P.ε/16) P.δ

lemma stages_pos : 0 < P.stages :=
  DyadicSchedule.sourceStages_pos _ P.hε P.hε1 Fintype.card_pos
instance stages_neZero : NeZero P.stages := ⟨P.stages_pos.ne'⟩

lemma schedule : P.stages = dyadicStages (Fintype.card ι) (P.ε/16) :=
  (DyadicSchedule.sourceStages_eq _ P.hε Fintype.card_pos).symm

lemma smallError_pos : 0 < P.ε/16 := by have h := P.hε; positivity
lemma smallError_lt_dim : P.ε/16 < Fintype.card ι := by
  have hd : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos (α := ι)
  linarith [P.hε1]

lemma stageMass_nonneg (j : Fin P.stages) : 0 ≤ massAllowance P.r (P.ε/16) P.stages j :=
  massAllowance_nonneg _ _ _ _
lemma stageMass_le_one (j : Fin P.stages) : massAllowance P.r (P.ε/16) P.stages j ≤ 1 := by
  unfold massAllowance
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _
lemma stageAccuracy_pos (j : Fin P.stages) : 0 < stageAccuracy (P.ε/16) P.stages j := by
  unfold stageAccuracy
  have hε := P.hε
  have hL := P.stages_pos
  have hscale := dyadicLower_pos P.stages j
  positivity
lemma stageFailure_range :
    0 < MultiscaleCollectiveCost.stageFailure P.stages P.δ ∧
      MultiscaleCollectiveCost.stageFailure P.stages P.δ < 1/2 :=
  MultiscaleCollectiveCost.stageFailure_range P.stages_pos P.hδ P.hδhalf

lemma stageBudget (j : Fin P.stages) :
    CollectiveStageFamily.macroCopies (ι := ι)
      (W := massAllowance P.r (P.ε/16) P.stages j)
      (η := stageAccuracy (P.ε/16) P.stages j)
      (b := MultiscaleCollectiveCost.stageFailure P.stages P.δ) ≤ P.copies := by
  apply Nat.ceil_le.mpr
  exact MultiscaleCollectiveCost.stage_routine_cost_le_globalN P.hr P.hrd (Nat.le_refl _)
    P.smallError_pos P.smallError_lt_dim P.schedule P.hδ P.hδhalf j

/-- Every stage's entire active-subspace family is fixed before inputρ. -/
def branches (j : Fin P.stages) : ∀ A : Finset ι, CollectiveStageRoutine.Branch ι P.copies A :=
  CollectiveStageFamily.family P.ow (P.stageMass_nonneg j) (P.stageMass_le_one j)
    (P.stageAccuracy_pos j) P.stageFailure_range.1 P.stageFailure_range.2 P.copies (P.stageBudget j)

abbrev StageOutcome (j : Fin P.stages) := CollectiveStageRoutine.Outcome (P.branches j)
instance stageOutcomeMeasurable (j : Fin P.stages) : MeasurableSpace (P.StageOutcome j) :=
  inferInstanceAs (MeasurableSpace (∀ A, (P.branches j A).Outcome))
abbrev Outcome := ∀ j : Fin P.stages, P.StageOutcome j

def stageReference (j : Fin P.stages) : Measure (P.StageOutcome j) :=
  CollectiveStageRoutine.reference (P.branches j)
instance stageReference_probability (j : Fin P.stages) : IsProbabilityMeasure (P.stageReference j) :=
  CollectiveStageRoutine.reference_isProbabilityMeasure _

def stageStep (j : Fin P.stages) :
    OneCopyStep (Fin P.copies → ι) (CollectiveStageRoutine.Control (ι := ι)) (P.StageOutcome j) :=
  CollectiveStageRoutine.step (P.branches j)
lemma stageStep_reference (j : Fin P.stages) :
    (P.stageStep j).reference = ProbabilityTheory.Kernel.const _ (P.stageReference j) := rfl

def commonStep (j : Fin P.stages) :
    OneCopyStep (Fin P.copies → ι) (CollectiveStageRoutine.Control (ι := ι)) P.Outcome :=
  ProductOutcomeStep.lift P.stageReference P.stageStep P.stageStep_reference j

def decode (k : ℕ) (y : P.Outcome) : EstimateFamily (ι := ι) :=
  if hk : k<P.stages then CollectiveStageRoutine.estimateFamily (P.branches ⟨k,hk⟩) (y ⟨k,hk⟩)
    else MultiscalePolicy.zeroFamily
lemma measurable_decode (k : ℕ) : Measurable (P.decode k) := by
  by_cases hk : k<P.stages
  · have he : P.decode k = (fun y : P.Outcome =>
        CollectiveStageRoutine.estimateFamily (P.branches ⟨k,hk⟩) (y ⟨k,hk⟩)) := by
      funext y
      simp [decode,hk]
    rw [he]
    exact (CollectiveStageRoutine.measurable_estimateFamily (P.branches ⟨k,hk⟩)).comp
      (measurable_pi_apply (⟨k,hk⟩ : Fin P.stages))
  · have he : P.decode k = (fun _ : P.Outcome => MultiscalePolicy.zeroFamily) := by
      funext y
      simp [decode,hk]
    rw [he]
    exact measurable_const

/-- The actual sequential quantum macroprotocol. Its estimator on the
supercopy space is dummy data; the real output below is on the originalι. -/
def macroLearner : AdaptiveModel.Learner (Fin P.copies → ι) PUnit P.Outcome P.stages where
  seed := Measure.dirac PUnit.unit
  seed_probability := inferInstance
  step j := StagePolicy.pullbackStep (P.commonStep j)
    (MultiscalePolicy.control P.selection (dyadicLower P.stages) P.decode j.val)
    (MultiscalePolicy.measurable_control P.selection _ _ P.measurable_decode j.val)
  estimator := ⟨fun _ => AdaptiveCollectiveEmbedding.uniformState (Fin P.copies → ι),measurable_const⟩

def estimator : Estimator ι (History PUnit P.Outcome P.stages) :=
  MultiscalePolicy.estimator P.selection (dyadicLower P.stages) P.decode
    P.measurable_decode (dyadicLower_pos P.stages)

def learner : CollectiveModel.Learner ι (History PUnit P.Outcome P.stages) (P.copies*P.stages) :=
  CollectiveBlockProtocol.learner P.macroLearner P.estimator


lemma frobenius_sub_comm {κ : Type*} [Fintype κ] (A B : Matrix κ κ ℂ) :
    ShellAccounting.frobeniusSq (A-B) = ShellAccounting.frobeniusSq (B-A) := by
  simp only [ShellAccounting.frobeniusSq,Matrix.sub_apply,norm_sub_rev]

lemma failure_of_success {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (f : Ω → ℝ) (hf : Measurable f) (η b : ℝ) (hb1 : b ≤ 1)
    (hs : ENNReal.ofReal (1-b) ≤ ν {z | f z ≤ η}) :
    ν {z | ¬f z ≤ η} ≤ ENNReal.ofReal b := by
  have hE : MeasurableSet {z | f z ≤ η} := measurableSet_le hf measurable_const
  change ν {z | f z ≤ η}ᶜ ≤ _
  rw [measure_compl hE (measure_ne_top ν _),measure_univ]
  apply (tsub_le_tsub_left hs 1).trans_eq
  calc
    (1 : ℝ≥0∞)-ENNReal.ofReal (1-b) = ENNReal.ofReal (1-(1-b)) := by
      rw [ENNReal.ofReal_sub 1 (sub_nonneg.mpr hb1),ENNReal.ofReal_one]
    _ = _ := by congr 1; ring

/-- The next actual macro Born transition has the allocated failure budget
on good past histories; no future-stage success is used. -/
theorem conditional_failure (ρ : Density ι) (hrank : ρ.matrix.rank ≤ P.r)
    (k : ℕ) (hk : k<P.stages) (h : History PUnit P.Outcome k)
    (hh : h ∈ StagePolicy.goodPrefix
      (MultiscalePolicy.good P.selection (dyadicLower P.stages) P.decode ρ
        (stageAccuracy (P.ε/16) P.stages)) k) :
    ((P.macroLearner.step ⟨k,hk⟩).bornKernel (TensorCopies.density ρ P.copies)) h
      {y | (h,y) ∉ MultiscalePolicy.good P.selection (dyadicLower P.stages) P.decode ρ
        (stageAccuracy (P.ε/16) P.stages) k} ≤
      ENNReal.ofReal (P.δ/(P.stages : ℝ)) := by
  let j : Fin P.stages := ⟨k,hk⟩
  let st := MultiscalePolicy.state P.selection (dyadicLower P.stages) P.decode k h
  let q : CollectiveStageRoutine.Control (ι := ι) := (st.1,st.2.1)
  let η := stageAccuracy (P.ε/16) P.stages j
  let b := MultiscaleCollectiveCost.stageFailure P.stages P.δ
  let f : P.StageOutcome j → ℝ := fun z => MultiscaleMatrixBridge.stateError ρ
    (st,CollectiveStageRoutine.estimateFamily (P.branches j) z)
  have hf : Measurable f := (MultiscaleMatrixBridge.measurable_stateError ρ).comp
    (measurable_const.prodMk (CollectiveStageRoutine.measurable_estimateFamily (P.branches j)))
  have hmass : headMass (CollectiveStageRoutine.splitState q.1 q.2 ρ) ≤
      massAllowance P.r (P.ε/16) P.stages j := by
    change (Matrix.trace (headBlock (CollectiveStageRoutine.splitState q.1 q.2 ρ).matrix)).re ≤ _
    rw [CollectiveStageRoutine.splitState_headBlock]
    exact MultiscalePolicy.current_mass_le P.selection P.decode ρ hrank j h hh
  have hs := CollectiveStageFamily.conditional_success P.ow (P.stageMass_nonneg j)
    (P.stageMass_le_one j) (P.stageAccuracy_pos j) P.stageFailure_range.1 P.stageFailure_range.2
    P.copies (P.stageBudget j) q ρ hmass
  have hflip : ∀ z : P.StageOutcome j, f z = ShellAccounting.frobeniusSq
      ((CollectiveStageRoutine.estimateFamily (P.branches j) z q.1).val -
        CollectiveStageRoutine.compressedBlock q.1 q.2 ρ) := by
    intro z
    change ShellAccounting.frobeniusSq
      (MultiscaleMatrixBridge.compressedBlock st.1 st.2.1 ρ-
        (CollectiveStageRoutine.estimateFamily (P.branches j) z st.1).val) = _
    exact frobenius_sub_comm _ _
  have hsucc : ENNReal.ofReal (1-b) ≤
      (P.stageStep j).bornKernel (TensorCopies.density ρ P.copies) q {z | f z ≤ η} := by
    change ENNReal.ofReal (1-b) ≤ (P.stageStep j).bornKernel
      (TensorCopies.density ρ P.copies) q {z | ShellAccounting.frobeniusSq
        ((CollectiveStageRoutine.estimateFamily (P.branches j) z q.1).val -
          CollectiveStageRoutine.compressedBlock q.1 q.2 ρ) ≤ η} at hs
    simpa only [← hflip] using hs
  have hbad := failure_of_success
    ((P.stageStep j).bornKernel (TensorCopies.density ρ P.copies) q) f hf η b
      (P.stageFailure_range.2.le.trans (by norm_num)) hsucc
  have hE : MeasurableSet {z : P.StageOutcome j | ¬f z ≤ η} :=
    (measurableSet_le hf measurable_const).compl
  have he : {y : P.Outcome | (h,y) ∉ MultiscalePolicy.good P.selection
        (dyadicLower P.stages) P.decode ρ (stageAccuracy (P.ε/16) P.stages) k} =
      Function.eval j ⁻¹' {z | ¬f z ≤ η} := by
    ext y
    simp only [MultiscalePolicy.good,Set.mem_setOf_eq,Set.mem_preimage,
      decode,dif_pos hk,f,η,j,st]
    rfl
  change ((StagePolicy.pullbackStep (P.commonStep j)
    (MultiscalePolicy.control P.selection (dyadicLower P.stages) P.decode k)
    (MultiscalePolicy.measurable_control P.selection _ _ P.measurable_decode k)).bornKernel
      (TensorCopies.density ρ P.copies)) h _ ≤ _
  rw [StagePolicy.pullbackStep_bornKernel,ProbabilityTheory.Kernel.comap_apply,he]
  change (ProductOutcomeStep.lift P.stageReference P.stageStep P.stageStep_reference j).bornKernel
    (TensorCopies.density ρ P.copies) q (Function.eval j ⁻¹' {z | ¬f z ≤ η}) ≤ _
  rw [ProductOutcomeStep.event_lift _ _ _ _ _ _ _ hE]
  exact hbad

/-- The actual final density estimator succeeds for every rank-at-most-r
input, after all experiments and the entire learner have been fixed. -/
theorem success (ρ : Density ι) (hrank : ρ.matrix.rank ≤ P.r) :
    1-ENNReal.ofReal P.δ ≤ P.learner.successProbability chiB ρ (ENNReal.ofReal P.ε) := by
  have hs := MultiscalePolicy.policy_success P.selection P.decode P.measurable_decode
    (StagePolicy.ofLearner P.macroLearner (TensorCopies.density ρ P.copies)) ρ
    P.hε P.hε1 P.hδ.le P.schedule (fun k hk h hh => P.conditional_failure ρ hrank k hk h hh)
  unfold learner
  rw [CollectiveBlockProtocol.learner_successProbability]
  simpa only [estimator,StagePolicy.Policy.transcriptLaw,StagePolicy.ofLearner_prefixLaw,
    AdaptiveModel.Learner.transcriptLaw] using hs

/-- This is the full actual-learner promise, including measurable loss events
and unrestricted normalized density outputs. -/
theorem learnsRank : P.learner.LearnsRank chiB P.r (ENNReal.ofReal P.ε) (1-ENNReal.ofReal P.δ) := by
  intro ρ hrank
  refine ⟨P.learner.successSet_measurable chiB ρ ?_ _,P.success ρ hrank⟩
  exact JordanLossMeasurability.measurable_chiB_comp (fun _ : Density ι => ρ) id measurable_const measurable_id

/-- Source Eq9's literal rank/dimension/logarithm exponents and sourceL0. -/
theorem copies_bound : ((P.copies*P.stages : ℕ) : ℝ) ≤
    (MultiscaleCollectiveCost.universalConstant*16) *
      (Real.sqrt (P.r : ℝ) * Fintype.card ι * Real.sqrt (Fintype.card ι : ℝ) *
        (P.stages : ℝ)^2 / P.ε) * Real.log ((P.stages : ℝ)/P.δ) := by
  have h := MultiscaleCollectiveCost.total_copies_le P.hr P.hrd P.smallError_pos
    P.smallError_lt_dim P.schedule P.hδ P.hδhalf
  apply h.trans_eq
  field_simp

end Parameters

/-- Universal coefficient of the actual Eq9 experiment. -/
def universalConstant : ℝ := MultiscaleCollectiveCost.universalConstant*16

theorem universalConstant_pos : 0 < universalConstant := by
  unfold universalConstant
  exact mul_pos MultiscaleCollectiveCost.universalConstant_pos (by norm_num)

/-- Complete Eq9: one physical learner is chosen before every unknown input
of rank≤r, on arbitrary measurable continuous outcomes. -/
theorem equation_9
    (B : MeasurableSpectralSelection.CompactFiberSelectionInput.{0,0})
    (O : ∀ A : Finset ι, A.Nonempty → FrobeniusLearning.OWFrobeniusInput (CollectiveStageRoutine.Active A))
    {r : ℕ} {ε δ : ℝ} (hr : 1 ≤ r) (hrd : r ≤ Fintype.card ι)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδhalf : δ < 1/2) :
    ∃ (n : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω),
      letI := mΩ
      ∃ A : CollectiveModel.Learner ι Ω n,
        A.LearnsRank chiB r (ENNReal.ofReal ε) (1-ENNReal.ofReal δ) ∧
        (n : ℝ) ≤ universalConstant *
          (Real.sqrt (r : ℝ) * Fintype.card ι * Real.sqrt (Fintype.card ι : ℝ) *
            (DyadicSchedule.sourceStages (Fintype.card ι) ε : ℝ)^2 / ε) *
              Real.log ((DyadicSchedule.sourceStages (Fintype.card ι) ε : ℝ)/δ) := by
  let P : Parameters ι := {
    r := r
    ε := ε
    δ := δ
    hr := hr
    hrd := hrd
    hε := hε
    hε1 := hε1
    hδ := hδ
    hδhalf := hδhalf
    selection := B
    ow := O }
  exact ⟨P.copies*P.stages,History PUnit P.Outcome P.stages,inferInstance,P.learner,
    P.learnsRank,P.copies_bound⟩

/-- The actual source minimum at its standard2/3 confidence, obtained by
choosing the same complete physical learner withδ=1/3. -/
theorem Ncoll_le
    (B : MeasurableSpectralSelection.CompactFiberSelectionInput.{0,0})
    (O : ∀ A : Finset ι, A.Nonempty → FrobeniusLearning.OWFrobeniusInput (CollectiveStageRoutine.Active A))
    {r : ℕ} {ε : ℝ} (hr : 1 ≤ r) (hrd : r ≤ Fintype.card ι)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    CopyComplexity.Ncoll (ι := ι) chiB r (ENNReal.ofReal ε) ≤ ENNReal.ofReal
      (universalConstant *
        (Real.sqrt (r : ℝ) * Fintype.card ι * Real.sqrt (Fintype.card ι : ℝ) *
          (DyadicSchedule.sourceStages (Fintype.card ι) ε : ℝ)^2 / ε) *
            Real.log (3*(DyadicSchedule.sourceStages (Fintype.card ι) ε : ℝ))) := by
  let P : Parameters ι := {
    r := r
    ε := ε
    δ := 1/3
    hr := hr
    hrd := hrd
    hε := hε
    hε1 := hε1
    hδ := by norm_num
    hδhalf := by norm_num
    selection := B
    ow := O }
  have hconf : 1-ENNReal.ofReal P.δ = (2 : ℝ≥0∞)/3 := by
    change 1-ENNReal.ofReal (1/3 : ℝ) = (2 : ℝ≥0∞)/3
    norm_num only [ENNReal.ofReal_div_of_pos, ENNReal.ofReal_one,
      ENNReal.ofReal_ofNat, Nat.cast_ofNat, one_div]
    exact ENNReal.sub_eq_of_eq_add' (by norm_num)
      (by rw [← one_div, ENNReal.div_add_div_same]; norm_num [ENNReal.div_self])
  have hlearn : P.learner.LearnsRank chiB r (ENNReal.ofReal ε) ((2 : ℝ≥0∞)/3) := by
    rw [← hconf]
    exact P.learnsRank
  have hn := CollectiveBlockProtocol.Ncoll_le P.macroLearner P.estimator chiB r
    (ENNReal.ofReal ε) hlearn
  apply hn.trans
  rw [← ENNReal.ofReal_natCast]
  apply ENNReal.ofReal_le_ofReal
  have hc := P.copies_bound
  have he : (P.stages : ℝ)/P.δ = 3*(DyadicSchedule.sourceStages (Fintype.card ι) ε : ℝ) := by
    change (DyadicSchedule.sourceStages (Fintype.card ι) ε : ℝ)/(1/3) = _
    ring
  rw [he] at hc
  exact hc

end Paper26.CollectiveBuresUpper
