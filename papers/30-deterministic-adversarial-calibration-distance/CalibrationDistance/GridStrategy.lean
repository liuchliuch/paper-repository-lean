import CalibrationDistance.Grid
import CalibrationDistance.Deterministic
import CalibrationDistance.Optimization

/-! The grid algorithm as a genuine finite nonanticipating strategy. The finite
prefix supplied to a prediction is extended by zeros only to call `gridRun`;
nonanticipation proves that the extension does not affect the prediction. -/

namespace CalibrationDistance

noncomputable section

def extendBits {T : ℕ} (y : Fin T → Bool) (s : ℕ) : Bool :=
  if h : s < T then y ⟨s, h⟩ else false

@[simp] theorem extendBits_coe {T : ℕ} (y : Fin T → Bool) (t : Fin T) :
    extendBits y t.val = y t := by simp [extendBits, t.isLt]

/-- The input at time `t` contains exactly the `t` past outcomes. -/
def fixedGridForecaster {m : ℕ} (hm : 0 < m) (T : ℕ) : DeterministicForecaster T :=
  fun t pastBits => ⟨gridForecast hm (gridRun hm (extendBits pastBits) t.val), gridForecast_mem hm _⟩

theorem fixedGridForecaster_path {m : ℕ} (hm : 0 < m) (T : ℕ) (y : Fin T → Bool) :
    deterministicPath (fixedGridForecaster hm T) y = runForecast hm (extendBits y) T := by
  funext t
  unfold deterministicPath fixedGridForecaster runForecast
  apply gridForecast_nonanticipating
  intro s hs
  simp [extendBits, hs, lt_trans hs t.isLt]

theorem runOutcomes_extendBits (T : ℕ) (y : Fin T → Bool) :
    runOutcomes (extendBits y) T = realOutcomes y := by
  funext t
  simp [runOutcomes, extendBits, realOutcomes, binaryValue, t.isLt]

/-- Proposition 6.3 with the paper's actual finite-strategy quantifiers. -/
theorem fixedGridForecaster_loss_bound {m : ℕ} (hm : 0 < m) (T : ℕ) (y : Fin T → Bool) :
    deterministicLoss (fixedGridForecaster hm T) y ≤ gridObjective T m := by
  unfold deterministicLoss
  rw [fixedGridForecaster_path, ← runOutcomes_extendBits T y]
  exact fixed_grid_pathwise_bound hm (extendBits y) T

def optimizedGridForecaster (T : ℕ) (hT : 1 ≤ T) : DeterministicForecaster T :=
  fixedGridForecaster (show 0 < optimalGrid T from
    lt_of_lt_of_le Nat.zero_lt_one (optimalGrid_threshold T hT).1) T

/-- A single concrete strategy attains the optimized upper bound on every outcome path. -/
theorem optimizedGridForecaster_loss_bound (T : ℕ) (hT : 1 ≤ T) (y : Fin T → Bool) :
    deterministicLoss (optimizedGridForecaster T hT) y ≤ optimalValue T := by
  exact fixedGridForecaster_loss_bound _ T y

theorem exists_optimized_grid_strategy (T : ℕ) (hT : 1 ≤ T) :
    ∃ F : DeterministicForecaster T, ∀ y, deterministicLoss F y ≤ optimalValue T :=
  ⟨optimizedGridForecaster T hT, optimizedGridForecaster_loss_bound T hT⟩

/-- The deterministic minimax upper inequality of Theorem 2.1. -/
theorem deterministicMinimax_le_optimalValue (T : ℕ) (hT : 1 ≤ T) :
    deterministicMinimax T ≤ optimalValue T :=
  deterministicMinimax_le_of_uniform_bound (optimizedGridForecaster T hT)
    (optimizedGridForecaster_loss_bound T hT)

theorem deterministicMinimax_lt_sqrt (T : ℕ) (hT : 1 ≤ T) :
    deterministicMinimax T < Real.sqrt (T : ℝ) :=
  lt_of_le_of_lt (deterministicMinimax_le_optimalValue T hT) (optimalValue_lt_sqrt T hT)

end
end CalibrationDistance
