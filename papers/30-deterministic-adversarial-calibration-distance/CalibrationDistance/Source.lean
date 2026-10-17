import CalibrationDistance.Main
import CalibrationDistance.WitnessDomain
import CalibrationDistance.Runtime
import CalibrationDistance.Oblivious
import CalibrationDistance.OakesCalculation

/-! Literal source-object interfaces. In particular the common upper value is
defined as the minimum/infimum over positive grids, then proved equal to the
explicit optimizer value used by the implementation. -/

namespace CalibrationDistance
noncomputable section

/-- The positive-integer optimization domain in source (2.6). -/
def positiveGridValues (T : ℕ) : Set ℝ :=
  {v | ∃ m : ℕ, 1 ≤ m ∧ v = gridObjective T m}

/-- The source U_T, without building the optimizer into its definition. -/
def sourceUpperValue (T : ℕ) : ℝ := sInf (positiveGridValues T)

theorem sourceUpperValue_minimum (T : ℕ) (hT : 1 ≤ T) :
    IsLeast (positiveGridValues T) (optimalValue T) := by
  refine ⟨⟨optimalGrid T,(optimalGrid_threshold T hT).1,rfl⟩,?_⟩
  rintro v ⟨m,hm,rfl⟩
  exact optimalValue_le_gridObjective T m hT hm

theorem sourceUpperValue_eq (T : ℕ) (hT : 1 ≤ T) :
    sourceUpperValue T = optimalValue T := (sourceUpperValue_minimum T hT).csInf_eq

/-- Equations (2.7)--(2.8) using precisely the source optimization domain. -/
theorem source_minimax_rate (T : ℕ) (hT : 2 ≤ T) :
    (Real.sqrt (T : ℝ)/4320 ≤ randAdaptiveMinimax T ∧
      randAdaptiveMinimax T ≤ sourceUpperValue T ∧ sourceUpperValue T < Real.sqrt (T : ℝ)) ∧
    (Real.sqrt (T : ℝ)/1200 ≤ deterministicMinimax T ∧
      deterministicMinimax T ≤ sourceUpperValue T ∧ sourceUpperValue T < Real.sqrt (T : ℝ)) := by
  rw [sourceUpperValue_eq T (by omega)]
  have hh := square_root_minimax_rate T hT
  exact ⟨hh.1,hh.2.1⟩

end
end CalibrationDistance
