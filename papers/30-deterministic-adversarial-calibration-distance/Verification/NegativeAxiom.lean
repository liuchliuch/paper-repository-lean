import CalibrationDistance.Core
import CalibrationDistance.Grid
import CalibrationDistance.Optimization
import CalibrationDistance.Deterministic
import CalibrationDistance.Finite

open CalibrationDistance

/- Isolated deliberate illegal axiom: neither production nor the positive
solution imports this module. -/
axiom P30.ComparatorControls.unauthorized : False

namespace P30.Challenge

theorem deterministic_minimax_one : deterministicMinimax 1 = (1 / 2 : ℝ) := by
  exact False.elim P30.ComparatorControls.unauthorized

end P30.Challenge
