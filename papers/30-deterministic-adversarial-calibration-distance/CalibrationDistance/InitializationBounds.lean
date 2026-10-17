import CalibrationDistance.Initialization

/-! Sharp preparation work: the integer search actually stops at the optimal
grid, so the preparation cost is linear in the next grid size, as in B.2. -/

namespace CalibrationDistance

theorem gridParameterSearchVisits_to_optimum (T : ℕ) (hT : 1 ≤ T) (fuel : ℕ) :
    ∀ n, 1 ≤ n → n ≤ optimalGrid T → optimalGrid T ≤ n+fuel →
      gridParameterSearchVisits T fuel n ≤ optimalGrid T-n+1 := by
  induction fuel with
  | zero => intro n hn hlo hhi; simp [gridParameterSearchVisits]
  | succ fuel ih =>
    intro n hn hlo hhi
    simp only [gridParameterSearchVisits]
    split_ifs with hs
    · omega
    · have hnxt : n+1 ≤ optimalGrid T := by
        have hh : ¬ optimalGrid T ≤ n := by
          intro hh
          exact hs ((optimalGrid_le_iff T n hT).1 hh)
        omega
      have hh := ih (n+1) (by omega) hnxt (by omega)
      omega

/-- Exact preparation work is O(m_next), not merely O(L). -/
theorem nextEpochInitializationJob_work_linear (L : ℕ) (hL : 1 ≤ L) :
    (nextEpochInitializationJob L).work < 5*(optimalGrid (2*L)+1) := by
  have hm : optimalGrid (2*L) ≤ L :=
    (optimalGrid_le_iff (2*L) L (by omega)).2 (by nlinarith)
  have hs := gridParameterSearchVisits_to_optimum (2*L) (by omega) L 1 (by omega)
    (optimalGrid_threshold (2*L) (by omega)).1 (by omega)
  have hb := gridTree_nodes_lt (optimalGrid (2*L)) (gridTreeInitial (optimalGrid (2*L)))
  rw [nextEpochInitializationJob_work L hL]
  unfold nextInitializationWork nextTreeBuildRecords
  omega

end CalibrationDistance
