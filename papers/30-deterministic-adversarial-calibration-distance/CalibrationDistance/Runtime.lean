import CalibrationDistance.AnytimeImplementation
import CalibrationDistance.Initialization

/-! Final runtime interface in the source word-RAM abstraction. Record visits
and bounded initialization quanta are explicit operational costs, while every
stored numerator and every arena address fits logarithmically many bits. -/

namespace CalibrationDistance
noncomputable section
open scoped BigOperators

def anytimeRecordPool (T : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (Nat.log 2 T+2), GridTree.nodes (gridTreeInitial (optimalGrid (2^k)))

theorem anytime_arena_address_width (T : ℕ) (hT : 1 ≤ T) :
    anytimeRecordPool T < 2^(Nat.clog 2 (T+1)+8) := by
  have hmem : (anytimeRecordPool T : ℝ) < 96*Real.sqrt (T : ℝ) := by
    simpa [anytimeRecordPool] using all_allocated_tree_records_lt T hT
  have ht1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have ht0 : (0 : ℝ) ≤ T := by positivity
  have ht2 : (T : ℝ) ≤ (T : ℝ)^2 := by
    nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1)]
  have hs : Real.sqrt (T : ℝ) ≤ (T : ℝ) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) ht0).mp
    simpa only [Real.sq_sqrt ht0] using ht2
  have hnat : anytimeRecordPool T < 96*T := by
    exact_mod_cast (hmem.trans_le (mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ)≤96)))
  have hp := Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) (T+1)
  rw [pow_add]
  norm_num
  omega

/-- Corollary 2.2: one infinite rule, implemented by exact cached-tree forecasts,
with all-prefix loss, logarithmic round work/word widths, square-root total
arena space, and an actual completed prepared tree at every epoch boundary.
Standard unit-cost word arithmetic and constant-size record access are the
word-RAM model assumptions of the source, not additional theorem assumptions. -/
theorem horizon_free_runtime_guarantee :
    ∃ F : (t : ℕ) → (Fin t → Bool) → Set.Icc (0 : ℝ) 1,
    (∀ (y : ℕ → Bool) (t : ℕ),
      (F t (fun i => y i.val)).val = (anytimeTreePrediction y t : ℝ)) ∧
    (∀ (y : ℕ → Bool) (T : ℕ), 1 ≤ T →
      calDist (fun t : Fin T => (F t.val (fun i => y i.val)).val) (runOutcomes y T) <
        (2+Real.sqrt 2)*Real.sqrt (T : ℝ) ∧
      (∀ t < T, gridTreeRoundVisits (anytimeGridParameter t) (anytimeTreeState y t) (y t) ≤
        4*(Nat.clog 2 (T+1)+1)) ∧
      (anytimeRecordPool T : ℝ) < 96*Real.sqrt (T : ℝ) ∧
      anytimeRecordPool T < 2^(Nat.clog 2 (T+1)+8)) ∧
    (∀ L, 1 ≤ L → runInitializationRounds L L =
      .done ⟨optimalGrid (2*L),gridTreeInitial (optimalGrid (2*L))⟩) := by
  refine ⟨anytimeForecaster, ?_, ?_, next_epoch_ready⟩
  · intro y t
    rw [anytimeForecaster_path,anytimeTreePrediction_correct]
  · intro y T hT
    have hh := horizon_free_exact_implementation y T hT
    refine ⟨?_,hh.2.1,?_,anytime_arena_address_width T hT⟩
    · simp only [anytimeForecaster_path]
      exact anytime_pathwise_bound y T hT
    · simpa [anytimeRecordPool] using hh.2.2.1

end
end CalibrationDistance
