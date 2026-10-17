import Paper26.CollectiveModel
import Paper26.LossMeasurability
import Paper26.JordanLossMeasurability

/-!
# Arbitrary operator POVMs and actual dominated collective experiments

The only representation input is the existing generic operator RN interface.
Every measurable-event Born probability is proved equal to its intrinsic
operator trace, for any representing dominated POVM. Actual learner success
is defined directly by the operator POVM and is independent of RN choices.
No kernel RN or arbitrary adaptive-family representation is asserted.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal
open MeasureTheory Paper26.QuantumModel Paper26.ContinuousPOVM Paper26.CollectiveModel

namespace Paper26.OperatorPOVMTransport

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]

/-- Exact representation of measurable-event matrix effects. -/
def Represents (P : OperatorPOVM ι Ω) (M : DominatedPOVM ι Ω) : Prop :=
  ∀ S, MeasurableSet S → ∀ i j,
    P.operator S i j = ∫ y in S, M.effect y i j ∂M.reference

/-- Integrating the actual finite complex Born trace recovers the actual
operator-valued event. All restricted integrability obligations are explicit. -/
theorem integral_complexBorn_event (P : OperatorPOVM ι Ω) (M : DominatedPOVM ι Ω)
    (hM : Represents P M) (ρ : Density ι) (S : Set Ω) (hS : MeasurableSet S) :
    ∫ y in S, M.complexBorn ρ y ∂M.reference = Matrix.trace (ρ.matrix * P.operator S) := by
  simp_rw [M.complexBorn_eq_sum ρ]
  rw [integral_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum Finset.univ (fun j _ =>
      ((M.entry_integrable j i).restrict (s := S)).const_mul (ρ.matrix i j)))]
  simp_rw [integral_finset_sum Finset.univ (fun j _ =>
    ((M.entry_integrable j _).restrict (s := S)).const_mul (ρ.matrix _ j)), integral_const_mul]
  simp_rw [← hM S hS]
  rfl

theorem integral_born_event (P : OperatorPOVM ι Ω) (M : DominatedPOVM ι Ω)
    (hM : Represents P M) (ρ : Density ι) (S : Set Ω) (hS : MeasurableSet S) :
    ∫ y in S, M.born ρ y ∂M.reference = (Matrix.trace (ρ.matrix * P.operator S)).re := by
  have hi := integral_re ((M.complexBorn_integrable ρ).restrict (s := S))
  simp only [RCLike.re_eq_complex_re] at hi
  exact hi.trans (congrArg Complex.re (integral_complexBorn_event P M hM ρ S hS))

/-- Measurable-event Born probabilities are intrinsic, independent of any
particular RN density or scalar reference representation. -/
theorem outcomeMeasure_event_trace (P : OperatorPOVM ι Ω) (M : DominatedPOVM ι Ω)
    (hM : Represents P M) (ρ : Density ι) (S : Set Ω) (hS : MeasurableSet S) :
    M.outcomeMeasure ρ S = ENNReal.ofReal (Matrix.trace (ρ.matrix * P.operator S)).re := by
  rw [M.outcomeMeasure_apply ρ hS,
    ← ofReal_integral_eq_lintegral_ofReal ((M.born_integrable ρ).restrict (s := S))
      (ae_restrict_of_ae (M.born_nonneg_ae ρ)), integral_born_event P M hM ρ S hS]

theorem event_trace_nonneg (P : OperatorPOVM ι Ω) (ρ : Density ι)
    (S : Set Ω) (hS : MeasurableSet S) : 0 ≤ (Matrix.trace (ρ.matrix * P.operator S)).re :=
  QuantumModel.trace_mul_effect_nonneg ρ (P.positive S hS)

/-- One simultaneous representing POVM, independent of the unknown state. -/
def chosenPOVM (R : OperatorRadonNikodymInput ι Ω) (P : OperatorPOVM ι Ω) : DominatedPOVM ι Ω :=
  Classical.choose (R.representation P)

theorem chosenPOVM_represents (R : OperatorRadonNikodymInput ι Ω) (P : OperatorPOVM ι Ω) :
    Represents P (chosenPOVM R P) := (Classical.choose_spec (R.representation P)).1

theorem chosenPOVM_reference (R : OperatorRadonNikodymInput ι Ω) (P : OperatorPOVM ι Ω)
    (S : Set Ω) (hS : MeasurableSet S) :
    (chosenPOVM R P).reference S = ENNReal.ofReal (Matrix.trace (P.operator S)).re :=
  (Classical.choose_spec (R.representation P)).2 S hS

/-- The actual Born probability measure of an arbitrary operator POVM. -/
def operatorOutcomeMeasure (R : OperatorRadonNikodymInput ι Ω) (P : OperatorPOVM ι Ω)
    (ρ : Density ι) : Measure Ω := (chosenPOVM R P).outcomeMeasure ρ

instance operatorOutcomeMeasure_probability (R : OperatorRadonNikodymInput ι Ω)
    (P : OperatorPOVM ι Ω) (ρ : Density ι) : IsProbabilityMeasure (operatorOutcomeMeasure R P ρ) :=
  inferInstanceAs (IsProbabilityMeasure ((chosenPOVM R P).outcomeMeasure ρ))

theorem operatorOutcomeMeasure_apply (R : OperatorRadonNikodymInput ι Ω)
    (P : OperatorPOVM ι Ω) (ρ : Density ι) (S : Set Ω) (hS : MeasurableSet S) :
    operatorOutcomeMeasure R P ρ S = ENNReal.ofReal (Matrix.trace (ρ.matrix * P.operator S)).re :=
  outcomeMeasure_event_trace P (chosenPOVM R P) (chosenPOVM_represents R P) ρ S hS

/-- Every RN witness, not merely the selected one, has the same Born law. -/
theorem outcomeMeasure_eq_of_representation (R : OperatorRadonNikodymInput ι Ω)
    (P : OperatorPOVM ι Ω) (M : DominatedPOVM ι Ω) (hM : Represents P M) (ρ : Density ι) :
    M.outcomeMeasure ρ = operatorOutcomeMeasure R P ρ := by
  apply Measure.ext
  intro S hS
  rw [outcomeMeasure_event_trace P M hM ρ S hS, operatorOutcomeMeasure_apply R P ρ S hS]

theorem operatorOutcomeMeasure_choice_independent (R R' : OperatorRadonNikodymInput ι Ω)
    (P : OperatorPOVM ι Ω) (ρ : Density ι) :
    operatorOutcomeMeasure R P ρ = operatorOutcomeMeasure R' P ρ := by
  apply Measure.ext
  intro S hS
  rw [operatorOutcomeMeasure_apply R P ρ S hS]

/-- A Definition-1.1 collective learner whose measurement is an arbitrary
actual operator POVM; the estimator output is an unrestricted density matrix. -/
structure OperatorLearner (ι Ω : Type*) [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (n : ℕ) where
  measurement : OperatorPOVM (Fin n → ι) Ω
  estimator : Estimator ι Ω

namespace OperatorLearner
variable {n : ℕ} (A : OperatorLearner ι Ω n)

/-- The actual event trace on `n` independent copies. -/
def eventBorn (ρ : Density ι) (S : Set Ω) : ℝ :=
  (Matrix.trace ((TensorCopies.density ρ n).matrix * A.measurement.operator S)).re

theorem eventBorn_nonneg (ρ : Density ι) (S : Set Ω) (hS : MeasurableSet S) :
    0 ≤ A.eventBorn ρ S := event_trace_nonneg A.measurement (TensorCopies.density ρ n) S hS

/-- A collective experiment from any candidate representing matrix density. -/
def representedLearner (M : DominatedPOVM (Fin n → ι) Ω) : CollectiveModel.Learner ι Ω n where
  measurement := M
  estimator := A.estimator

def toDominated (R : OperatorRadonNikodymInput (Fin n → ι) Ω) : CollectiveModel.Learner ι Ω n where
  measurement := chosenPOVM R A.measurement
  estimator := A.estimator

def outcomeMeasure (R : OperatorRadonNikodymInput (Fin n → ι) Ω) (ρ : Density ι) : Measure Ω :=
  operatorOutcomeMeasure R A.measurement (TensorCopies.density ρ n)

instance outcomeMeasure_probability (R : OperatorRadonNikodymInput (Fin n → ι) Ω)
    (ρ : Density ι) : IsProbabilityMeasure (A.outcomeMeasure R ρ) :=
  operatorOutcomeMeasure_probability R A.measurement _

theorem outcomeMeasure_apply (R : OperatorRadonNikodymInput (Fin n → ι) Ω)
    (ρ : Density ι) (S : Set Ω) (hS : MeasurableSet S) :
    A.outcomeMeasure R ρ S = ENNReal.ofReal (A.eventBorn ρ S) :=
  operatorOutcomeMeasure_apply R A.measurement _ S hS

def outputMeasure (R : OperatorRadonNikodymInput (Fin n → ι) Ω) (ρ : Density ι) :
    Measure (Density ι) := (A.outcomeMeasure R ρ).map A.estimator.estimate

instance outputMeasure_probability (R : OperatorRadonNikodymInput (Fin n → ι) Ω)
    (ρ : Density ι) : IsProbabilityMeasure (A.outputMeasure R ρ) :=
  Measure.isProbabilityMeasure_map A.estimator.measurable_estimate.aemeasurable

theorem outputMeasure_apply (R : OperatorRadonNikodymInput (Fin n → ι) Ω)
    (ρ : Density ι) (S : Set (Density ι)) (hS : MeasurableSet S) :
    A.outputMeasure R ρ S = ENNReal.ofReal (A.eventBorn ρ (A.estimator.estimate ⁻¹' S)) := by
  rw [outputMeasure, Measure.map_apply A.estimator.measurable_estimate hS,
    A.outcomeMeasure_apply R ρ _ (A.estimator.measurable_estimate hS)]

def successSet (loss : Density ι → Density ι → ℝ≥0∞) (ρ : Density ι) (ε : ℝ≥0∞) : Set Ω :=
  {y | loss ρ (A.estimator.estimate y) ≤ ε}

/-- This definition is intrinsic to the operator POVM. It is a probability
on every measurable success event, as proved below, with no RN choice in it. -/
def successProbability (loss : Density ι → Density ι → ℝ≥0∞) (ρ : Density ι)
    (ε : ℝ≥0∞) : ℝ≥0∞ := ENNReal.ofReal (A.eventBorn ρ (A.successSet loss ρ ε))

def LearnsRank (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε q : ℝ≥0∞) : Prop :=
  ∀ ρ : Density ι, ρ.matrix.rank ≤ r →
    MeasurableSet (A.successSet loss ρ ε) ∧ q ≤ A.successProbability loss ρ ε

def BuresSuccess (r : ℕ) (ε : ℝ≥0∞) : Prop := A.LearnsRank chiB r ε ((2 : ℝ≥0∞) / 3)
def RightSuccess (r : ℕ) (ε : ℝ≥0∞) : Prop := A.LearnsRank chiR r ε ((2 : ℝ≥0∞) / 3)

theorem successProbability_eq_outcomeMeasure (R : OperatorRadonNikodymInput (Fin n → ι) Ω)
    (loss : Density ι → Density ι → ℝ≥0∞) (ρ : Density ι) (ε : ℝ≥0∞)
    (hS : MeasurableSet (A.successSet loss ρ ε)) :
    A.successProbability loss ρ ε = A.outcomeMeasure R ρ (A.successSet loss ρ ε) :=
  (A.outcomeMeasure_apply R ρ _ hS).symm

theorem successProbability_eq_outputMeasure (R : OperatorRadonNikodymInput (Fin n → ι) Ω)
    (loss : Density ι → Density ι → ℝ≥0∞) (ρ : Density ι) (ε : ℝ≥0∞)
    (hLoss : Measurable (loss ρ)) :
    A.successProbability loss ρ ε = A.outputMeasure R ρ {σ | loss ρ σ ≤ ε} := by
  rw [A.outputMeasure_apply R ρ _ (measurableSet_le hLoss measurable_const)]
  rfl

theorem successProbability_le_one (R : OperatorRadonNikodymInput (Fin n → ι) Ω)
    (loss : Density ι → Density ι → ℝ≥0∞) (ρ : Density ι) (ε : ℝ≥0∞)
    (hS : MeasurableSet (A.successSet loss ρ ε)) : A.successProbability loss ρ ε ≤ 1 := by
  rw [A.successProbability_eq_outcomeMeasure R loss ρ ε hS]
  exact (measure_mono (Set.subset_univ _)).trans_eq (measure_univ : A.outcomeMeasure R ρ Set.univ = 1)

/-- Intrinsic learner success agrees with every representing dominated
POVM, for the actual measurable successful event. -/
theorem representedLearner_successProbability (M : DominatedPOVM (Fin n → ι) Ω)
    (hM : Represents A.measurement M)
    (loss : Density ι → Density ι → ℝ≥0∞) (ρ : Density ι) (ε : ℝ≥0∞)
    (hS : MeasurableSet (A.successSet loss ρ ε)) :
    (A.representedLearner M).successProbability loss ρ ε = A.successProbability loss ρ ε :=
  outcomeMeasure_event_trace A.measurement M hM (TensorCopies.density ρ n) _ hS

/-- The rank-learning promise is representation-independent even before
choosing a particular RN witness. -/
theorem representedLearner_learnsRank_iff (M : DominatedPOVM (Fin n → ι) Ω)
    (hM : Represents A.measurement M)
    (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε q : ℝ≥0∞) :
    (A.representedLearner M).LearnsRank loss r ε q ↔ A.LearnsRank loss r ε q := by
  constructor
  · intro h ρ hr
    obtain ⟨hS, hp⟩ := h ρ hr
    change MeasurableSet (A.successSet loss ρ ε) at hS
    refine ⟨hS, ?_⟩
    rw [A.representedLearner_successProbability M hM loss ρ ε hS] at hp
    exact hp
  · intro h ρ hr
    obtain ⟨hS, hp⟩ := h ρ hr
    refine ⟨hS, ?_⟩
    rw [A.representedLearner_successProbability M hM loss ρ ε hS]
    exact hp

theorem toDominated_outcomeMeasure (R : OperatorRadonNikodymInput (Fin n → ι) Ω)
    (ρ : Density ι) : (A.toDominated R).outcomeMeasure ρ = A.outcomeMeasure R ρ := rfl

theorem toDominated_outputMeasure (R : OperatorRadonNikodymInput (Fin n → ι) Ω)
    (ρ : Density ι) : (A.toDominated R).outputMeasure ρ = A.outputMeasure R ρ := rfl

@[simp] theorem toDominated_successSet (R : OperatorRadonNikodymInput (Fin n → ι) Ω)
    (loss : Density ι → Density ι → ℝ≥0∞) (ρ : Density ι) (ε : ℝ≥0∞) :
    (A.toDominated R).successSet loss ρ ε = A.successSet loss ρ ε := rfl

theorem toDominated_successProbability (R : OperatorRadonNikodymInput (Fin n → ι) Ω)
    (loss : Density ι → Density ι → ℝ≥0∞) (ρ : Density ι) (ε : ℝ≥0∞)
    (hS : MeasurableSet (A.successSet loss ρ ε)) :
    (A.toDominated R).successProbability loss ρ ε = A.successProbability loss ρ ε := by
  change A.outcomeMeasure R ρ (A.successSet loss ρ ε) = _
  exact (A.successProbability_eq_outcomeMeasure R loss ρ ε hS).symm

/-- Exact equivalence of the original rank/accuracy/confidence promise;
no new rank restriction, loss convention, or successful-event premise. -/
theorem toDominated_learnsRank_iff (R : OperatorRadonNikodymInput (Fin n → ι) Ω)
    (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε q : ℝ≥0∞) :
    (A.toDominated R).LearnsRank loss r ε q ↔ A.LearnsRank loss r ε q := by
  constructor
  · intro h ρ hr
    obtain ⟨hS, hp⟩ := h ρ hr
    change MeasurableSet (A.successSet loss ρ ε) at hS
    exact ⟨hS, by rw [A.toDominated_successProbability R loss ρ ε hS] at hp; exact hp⟩
  · intro h ρ hr
    obtain ⟨hS, hp⟩ := h ρ hr
    refine ⟨hS, ?_⟩
    rw [A.toDominated_successProbability R loss ρ ε hS]
    exact hp

theorem toDominated_buresSuccess_iff (R : OperatorRadonNikodymInput (Fin n → ι) Ω)
    (r : ℕ) (ε : ℝ≥0∞) :
    (A.toDominated R).BuresSuccess r ε ↔ A.BuresSuccess r ε :=
  A.toDominated_learnsRank_iff R chiB r ε _

theorem toDominated_rightSuccess_iff (R : OperatorRadonNikodymInput (Fin n → ι) Ω)
    (r : ℕ) (ε : ℝ≥0∞) :
    (A.toDominated R).RightSuccess r ε ↔ A.RightSuccess r ε :=
  A.toDominated_learnsRank_iff R chiR r ε _

theorem bures_successSet_measurable (ρ : Density ι) (ε : ℝ≥0∞) :
    MeasurableSet (A.successSet chiB ρ ε) :=
  measurableSet_le (JordanLossMeasurability.measurable_chiB_comp _ _ measurable_const
    A.estimator.measurable_estimate) measurable_const

theorem right_successSet_measurable (ρ : Density ι) (ε : ℝ≥0∞) :
    MeasurableSet (A.successSet chiR ρ ε) :=
  measurableSet_le (LossMeasurability.measurable_chiR_comp _ _ measurable_const
    A.estimator.measurable_estimate) measurable_const

end OperatorLearner
end Paper26.OperatorPOVMTransport
