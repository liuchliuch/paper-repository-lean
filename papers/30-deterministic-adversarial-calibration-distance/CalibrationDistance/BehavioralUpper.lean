import CalibrationDistance.DeterministicProtocol
import CalibrationDistance.GridStrategy
import CalibrationDistance.ProtocolOne

/-! The actual randomized simultaneous minimax value (2.4), with boundedness
proved from the trajectory loss. The upper strategy is the concrete grid
forecaster, injected into the public-history behavioral-kernel class. -/

open MeasureTheory ProbabilityTheory

namespace CalibrationDistance

open Protocol

noncomputable section

/-- The supremum is over precisely the deterministic past-adaptive adversaries
of §2.2, with expectation under the genuine simultaneous trajectory law. -/
def randAdaptiveWorst (K : BehavioralForecaster) (T : ℕ) : ℝ :=
  sSup (Set.range (fun A : Adversary => expectedCalDist K A T))

/-- Equation (2.4), preserving the order `inf_K sup_A expectation`. -/
def randAdaptiveMinimax (T : ℕ) : ℝ :=
  sInf (Set.range (fun K : BehavioralForecaster => randAdaptiveWorst K T))

theorem adaptiveExpected_range_nonempty (K : BehavioralForecaster) (T : ℕ) :
    (Set.range (fun A : Adversary => expectedCalDist K A T)).Nonempty :=
  ⟨_, constantAdversary false, rfl⟩

theorem adaptiveExpected_range_bddAbove (K : BehavioralForecaster) (T : ℕ) :
    BddAbove (Set.range (fun A : Adversary => expectedCalDist K A T)) := by
  refine ⟨(T : ℝ), ?_⟩
  rintro _ ⟨A, rfl⟩
  exact expectedCalDist_le_horizon K A T

theorem expectedCalDist_le_randAdaptiveWorst (K : BehavioralForecaster) (A : Adversary) (T : ℕ) :
    expectedCalDist K A T ≤ randAdaptiveWorst K T :=
  le_csSup (adaptiveExpected_range_bddAbove K T) (Set.mem_range_self A)

theorem randAdaptiveWorst_nonneg (K : BehavioralForecaster) (T : ℕ) :
    0 ≤ randAdaptiveWorst K T :=
  (expectedCalDist_nonneg K (constantAdversary false) T).trans
    (expectedCalDist_le_randAdaptiveWorst K (constantAdversary false) T)

theorem randAdaptiveWorst_le_horizon (K : BehavioralForecaster) (T : ℕ) :
    randAdaptiveWorst K T ≤ T := by
  apply csSup_le (adaptiveExpected_range_nonempty K T)
  rintro _ ⟨A, rfl⟩
  exact expectedCalDist_le_horizon K A T

theorem adaptiveWorst_range_nonempty (T : ℕ) :
    (Set.range (fun K : BehavioralForecaster => randAdaptiveWorst K T)).Nonempty :=
  ⟨_, halfBehavioralForecaster, rfl⟩

theorem adaptiveWorst_range_bddBelow (T : ℕ) :
    BddBelow (Set.range (fun K : BehavioralForecaster => randAdaptiveWorst K T)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨K, rfl⟩
  exact randAdaptiveWorst_nonneg K T

theorem randAdaptiveMinimax_le_worst (K : BehavioralForecaster) (T : ℕ) :
    randAdaptiveMinimax T ≤ randAdaptiveWorst K T :=
  csInf_le (adaptiveWorst_range_bddBelow T) (Set.mem_range_self K)

theorem randAdaptiveMinimax_nonneg (T : ℕ) : 0 ≤ randAdaptiveMinimax T := by
  apply le_csInf (adaptiveWorst_range_nonempty T)
  rintro _ ⟨K, rfl⟩
  exact randAdaptiveWorst_nonneg K T

theorem randAdaptiveMinimax_le_horizon (T : ℕ) : randAdaptiveMinimax T ≤ T :=
  (randAdaptiveMinimax_le_worst halfBehavioralForecaster T).trans
    (randAdaptiveWorst_le_horizon halfBehavioralForecaster T)

/-- Uniform expected guarantees bound the true supremum over adaptive adversaries. -/
theorem randAdaptiveWorst_le_of_uniform_bound (K : BehavioralForecaster) (T : ℕ) {C : ℝ}
    (hC : ∀ A, expectedCalDist K A T ≤ C) : randAdaptiveWorst K T ≤ C := by
  apply csSup_le (adaptiveExpected_range_nonempty K T)
  rintro _ ⟨A, rfl⟩
  exact hC A

/-- An explicit legal strategy supplies the upper minimax transfer. -/
theorem randAdaptiveMinimax_le_of_uniform_bound (K : BehavioralForecaster) (T : ℕ) {C : ℝ}
    (hC : ∀ A, expectedCalDist K A T ≤ C) : randAdaptiveMinimax T ≤ C :=
  (randAdaptiveMinimax_le_worst K T).trans (randAdaptiveWorst_le_of_uniform_bound K T hC)

/-- The lower transfer preserves the adaptive quantifiers: the chosen deterministic
adversary may depend on the whole forecaster but never on the current private draw. -/
theorem le_randAdaptiveMinimax_of_forall_exists (T : ℕ) {C : ℝ}
    (hC : ∀ K : BehavioralForecaster, ∃ A : Adversary, C ≤ expectedCalDist K A T) :
    C ≤ randAdaptiveMinimax T := by
  apply le_csInf (adaptiveWorst_range_nonempty T)
  rintro _ ⟨K, rfl⟩
  obtain ⟨A, hA⟩ := hC K
  exact hA.trans (expectedCalDist_le_randAdaptiveWorst K A T)

/-- The optimized grid is one concrete behavioral strategy for every adversary. -/
def optimizedGridBehavioral (T : ℕ) (hT : 1 ≤ T) : BehavioralForecaster :=
  deterministicBehavioral (optimizedGridForecaster T hT)

theorem optimizedGridBehavioral_expected_bound (T : ℕ) (hT : 1 ≤ T) (A : Adversary) :
    expectedCalDist (optimizedGridBehavioral T hT) A T ≤ optimalValue T :=
  expectedCalDist_deterministic_le (optimizedGridForecaster T hT) A
    (optimizedGridForecaster_loss_bound T hT)

/-- The pathwise algorithm also allows arbitrary randomized simultaneous opponents. -/
theorem optimizedGridBehavioral_randomized_bound (T : ℕ) (hT : 1 ≤ T)
    (B : RandomizedAdversary) :
    (∫ h, pathLoss T h ∂law (optimizedGridBehavioral T hT) B T) ≤ optimalValue T :=
  integral_calDist_deterministic_le (optimizedGridForecaster T hT) B
    (optimizedGridForecaster_loss_bound T hT)

theorem exists_optimized_behavioral_strategy (T : ℕ) (hT : 1 ≤ T) :
    ∃ K : BehavioralForecaster, ∀ A : Adversary, expectedCalDist K A T ≤ optimalValue T :=
  ⟨optimizedGridBehavioral T hT, optimizedGridBehavioral_expected_bound T hT⟩

/-- The randomized simultaneous upper inequality of Theorem 2.1. -/
theorem randAdaptiveMinimax_le_optimalValue (T : ℕ) (hT : 1 ≤ T) :
    randAdaptiveMinimax T ≤ optimalValue T :=
  randAdaptiveMinimax_le_of_uniform_bound (optimizedGridBehavioral T hT) T
    (optimizedGridBehavioral_expected_bound T hT)

theorem randAdaptiveMinimax_lt_sqrt (T : ℕ) (hT : 1 ≤ T) :
    randAdaptiveMinimax T < Real.sqrt (T : ℝ) :=
  lt_of_le_of_lt (randAdaptiveMinimax_le_optimalValue T hT) (optimalValue_lt_sqrt T hT)

/-- The deterministic strategies are included in the behavioral class with their
actual pathwise losses, so the randomized adaptive value is no larger. -/
theorem randAdaptiveMinimax_le_deterministicMinimax (T : ℕ) :
    randAdaptiveMinimax T ≤ deterministicMinimax T := by
  apply le_csInf (show (Set.range (@deterministicWorst T)).Nonempty from
    ⟨_, halfForecaster T, rfl⟩)
  rintro _ ⟨F, rfl⟩
  exact randAdaptiveMinimax_le_of_uniform_bound (deterministicBehavioral F) T
    (fun A => expectedCalDist_deterministic_le F A (fun y => deterministicLoss_le_worst F y))

/-- The exact boundary case in the last paragraph of Theorem 2.1. -/
theorem randAdaptiveMinimax_one : randAdaptiveMinimax 1 = (1 / 2 : ℝ) := by
  apply le_antisymm
  · exact randAdaptiveMinimax_le_of_uniform_bound halfBehavioralForecaster 1
      (fun A => le_of_eq (halfBehavioralForecaster_one A))
  · exact le_randAdaptiveMinimax_of_forall_exists 1 randomized_one_round_lower

theorem randAdaptiveMinimax_zero : randAdaptiveMinimax 0 = 0 := by
  apply le_antisymm
  · simpa using randAdaptiveMinimax_le_horizon 0
  · exact randAdaptiveMinimax_nonneg 0

end
end CalibrationDistance
