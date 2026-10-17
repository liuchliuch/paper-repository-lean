import CalibrationDistance.Implementation

/-! Exact cached-tree realization of the single horizon-free forecaster.

Record visits are the cost unit of the explicit word-RAM model in
Implementation. At an epoch boundary the prepared arena becomes current by
changing root handles; the old arena is retained, so no reclamation traversal
is charged to that round. All arenas, including retired ones, are counted.
-/

namespace CalibrationDistance
noncomputable section

open scoped BigOperators

def anytimeGridParameter (t : ℕ) : ℕ := optimalGrid (epochLength (epochIndex t))

theorem anytimeGridParameter_pos (t : ℕ) : 0 < anytimeGridParameter t := by
  have hh := (optimalGrid_threshold (epochLength (epochIndex t))
    (Nat.succ_le_of_lt (epochLength_pos _))).1
  exact Nat.lt_of_lt_of_le (by decide : 0 < 1) hh

def anytimeTreeState (y : ℕ → Bool) (t : ℕ) : GridSearchTree (anytimeGridParameter t) :=
  gridTreeRun (anytimeGridParameter t) (fun i => y (epochStart (epochIndex t)+i))
    (t-epochStart (epochIndex t))

def anytimeTreePrediction (y : ℕ → Bool) (t : ℕ) : ℚ :=
  gridTreeForecast (anytimeGridParameter t) (anytimeTreeState y t)

theorem anytimeTreePrediction_correct (y : ℕ → Bool) (t : ℕ) :
    (anytimeTreePrediction y t : ℝ) = anytimePrediction y t := by
  have hh := gridTreeForecast_correct (anytimeGridParameter_pos t)
    (fun i => y (epochStart (epochIndex t)+i)) (t-epochStart (epochIndex t))
  simpa only [anytimeTreePrediction, anytimeTreeState, anytimePrediction, restartStream,
    optimizedBudgetRule, dif_pos (epochLength_pos _), anytimeGridParameter] using hh

theorem anytimeTree_pathwise_bound (y : ℕ → Bool) (T : ℕ) (hT : 1 ≤ T) :
    calDist (fun t : Fin T => (anytimeTreePrediction y t.val : ℝ)) (runOutcomes y T) <
      (2+Real.sqrt 2)*Real.sqrt (T : ℝ) := by
  simp only [anytimeTreePrediction_correct]
  exact anytime_pathwise_bound y T hT

theorem anytimeTree_round_visits (y : ℕ → Bool) (t : ℕ) :
    gridTreeRoundVisits (anytimeGridParameter t) (anytimeTreeState y t) (y t) ≤
      4*(Nat.clog 2 (t+2)+1) := by
  apply epoch_tree_round_log_bound (epochLength (epochIndex t)) (t+1)
    (Nat.succ_le_of_lt (epochLength_pos _))
  exact Nat.pow_log_le_self 2 (by omega : t+1 ≠ 0)

theorem anytimeTree_word_width (t : ℕ) :
    gridWordWidth (anytimeGridParameter t) ≤ Nat.clog 2 (t+2)+4 := by
  have hL : 1 ≤ epochLength (epochIndex t) := Nat.succ_le_of_lt (epochLength_pos _)
  have hm := optimalGrid_le_budget (epochLength (epochIndex t)) hL
  have hLclock : epochLength (epochIndex t) ≤ t+1 := Nat.pow_log_le_self 2 (by omega)
  have hc := Nat.clog_mono_right 2
    (show anytimeGridParameter t+1 ≤ t+2 by dsimp [anytimeGridParameter]; omega)
  exact Nat.add_le_add_right hc 4

/-- Root handles model constant-time arena activation and retirement. No tree
is visited by this operation, and old epoch records are kept in the footprint. -/
structure ArenaHandles where
  current : ℕ
  prepared : ℕ
  retired : List ℕ

def ArenaHandles.activate (h : ArenaHandles) (nextPrepared : ℕ) : ArenaHandles :=
  ⟨h.prepared,nextPrepared,h.current::h.retired⟩

theorem arena_activation (h : ArenaHandles) (nextPrepared : ℕ) :
    (h.activate nextPrepared).current = h.prepared ∧
    (h.activate nextPrepared).retired.length = h.retired.length+1 :=
  ⟨rfl,rfl⟩

/-- Corollary 2.2's implementation bounds in exact cost-model quantities.
The first component is the every-prefix loss guarantee of this same run. -/
theorem horizon_free_exact_implementation (y : ℕ → Bool) (T : ℕ) (hT : 1 ≤ T) :
    calDist (fun t : Fin T => (anytimeTreePrediction y t.val : ℝ)) (runOutcomes y T) <
        (2+Real.sqrt 2)*Real.sqrt (T : ℝ) ∧
    (∀ t < T, gridTreeRoundVisits (anytimeGridParameter t) (anytimeTreeState y t) (y t) ≤
      4*(Nat.clog 2 (T+1)+1)) ∧
    (∑ k ∈ Finset.range (Nat.log 2 T+2),
      (GridTree.nodes (gridTreeInitial (optimalGrid (2^k))) : ℝ)) <
        96*Real.sqrt (T : ℝ) ∧
    (∀ L, 1 ≤ L → initializationProgress L L = nextInitializationWork L) := by
  refine ⟨anytimeTree_pathwise_bound y T hT, ?_, all_allocated_tree_records_lt T hT,
    initializationProgress_complete⟩
  intro t ht
  have hround := anytimeTree_round_visits y t
  have hclog := Nat.clog_mono_right 2 (show t+2 ≤ T+1 by omega)
  omega

end
end CalibrationDistance
