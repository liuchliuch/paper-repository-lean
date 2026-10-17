import CalibrationDistance.BehavioralUpper

/-! The remaining quantifier order in Remark 2.3. Outcomes in this protocol
are fixed before play; no unproved square-root lower bound is asserted. -/

namespace CalibrationDistance
open Protocol
noncomputable section

def fixedStringAdversary {T : ℕ} (y : Fin T → Bool) : Adversary where
  action n _ := if hn : n < T then y ⟨n,hn⟩ else false
  measurable_action _ := measurable_const

def randObliviousWorst (K : BehavioralForecaster) (T : ℕ) : ℝ :=
  sSup (Set.range (fun y : Fin T → Bool => expectedCalDist K (fixedStringAdversary y) T))

def randObliviousMinimax (T : ℕ) : ℝ :=
  sInf (Set.range (fun K : BehavioralForecaster => randObliviousWorst K T))

theorem randObliviousWorst_nonneg (K : BehavioralForecaster) (T : ℕ) :
    0 ≤ randObliviousWorst K T := by
  have hh : expectedCalDist K (fixedStringAdversary (fun _ : Fin T => false)) T ≤
      randObliviousWorst K T := le_csSup (Set.finite_range _).bddAbove (Set.mem_range_self _)
  exact (expectedCalDist_nonneg K _ T).trans hh

theorem randObliviousWorst_le_adaptive (K : BehavioralForecaster) (T : ℕ) :
    randObliviousWorst K T ≤ randAdaptiveWorst K T := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨y,rfl⟩
  exact expectedCalDist_le_randAdaptiveWorst K (fixedStringAdversary y) T

theorem obliviousWorst_range_bddBelow (T : ℕ) :
    BddBelow (Set.range (fun K : BehavioralForecaster => randObliviousWorst K T)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨K,rfl⟩
  exact randObliviousWorst_nonneg K T

theorem randObliviousMinimax_nonneg (T : ℕ) : 0 ≤ randObliviousMinimax T := by
  unfold randObliviousMinimax
  apply le_csInf (show (Set.range (fun K : BehavioralForecaster => randObliviousWorst K T)).Nonempty from
    ⟨_, halfBehavioralForecaster,rfl⟩)
  rintro _ ⟨K,rfl⟩
  exact randObliviousWorst_nonneg K T

theorem randObliviousMinimax_le_adaptive (T : ℕ) :
    randObliviousMinimax T ≤ randAdaptiveMinimax T := by
  apply le_csInf (adaptiveWorst_range_nonempty T)
  rintro _ ⟨K,rfl⟩
  exact (csInf_le (obliviousWorst_range_bddBelow T) (Set.mem_range_self K)).trans
    (randObliviousWorst_le_adaptive K T)

theorem randObliviousMinimax_le_optimalValue (T : ℕ) (hT : 1 ≤ T) :
    randObliviousMinimax T ≤ optimalValue T :=
  (randObliviousMinimax_le_adaptive T).trans (randAdaptiveMinimax_le_optimalValue T hT)

end
end CalibrationDistance
