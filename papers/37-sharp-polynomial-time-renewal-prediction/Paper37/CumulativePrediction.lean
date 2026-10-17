import Paper37.CumulativeLower
import Paper37.CycleGoodEvent

/-! Source G.1--G.3 on the actual endpoint-safe prediction risk. The only
external theorem parameter is the generic classical finite equilibrium-cycle
representation; all hard-prior probabilities and statistical inequalities
are independently proved in the imported modules. -/
namespace Paper37.CumulativePrediction
open Paper37.Renewal Paper37.Prediction Paper37.LowerBound
open Paper37.BayesLowerBound Paper37.CumulativeLower
open Paper37.EquilibriumCycle
open scoped ENNReal

/-- One common finite-support prior works at every late time in the horizon.
Its choice depends on the horizon, as allowed by the cumulative minimax
problem; it does not change from one summand to another. -/
lemma common_prior_goodMass (cycle : EquilibriumCyclePrinciple)
    (N : ℕ) (hN : 2500 ≤ N) :
    ∀ t ∈ Finset.Ico (24*ceilingRoot N) N,
      1/8 ≤ goodPredictiveMass t (ceilingRoot N) := by
  intro t ht
  have hb := (ceilingRoot_scale_bounds (show 600 ≤ N by omega)).1
  have hr := ceilingRoot_square_ge N
  have htN : t < N := (Finset.mem_Ico.mp ht).2
  exact Paper37.CycleGoodEvent.goodPredictiveMass_lower cycle hb
    (Finset.mem_Ico.mp ht).1 (by omega)

/-- The original cumulative minimax lower bound G.3, against every private
randomized predictor, with the actual source renewal laws in the supremum. -/
theorem cumulative_sqrt_lower (cycle : EquilibriumCyclePrinciple)
    (N : ℕ) (hN : 2500 ≤ N) (q : RandomizedPredictor) :
    ENNReal.ofReal (cumulativeConstant * Real.sqrt N) ≤
      ⨆ μ : Law, cumulativeRisk N q μ :=
  cumulative_sqrt_lower_of_goodMass N hN (common_prior_goodMass cycle N hN) q

/-- Taking the infimum includes predictors chosen with knowledge of `N`. -/
theorem minimax_cumulative_sqrt_lower (cycle : EquilibriumCyclePrinciple)
    (N : ℕ) (hN : 2500 ≤ N) :
    ENNReal.ofReal (cumulativeConstant * Real.sqrt N) ≤ minimaxCumulativeRisk N :=
  minimax_cumulative_sqrt_lower_of_goodMass N hN (common_prior_goodMass cycle N hN)

/-- A single horizon-free predictor attains the upper rate simultaneously at
every horizon, while the lower bound permits arbitrary horizon-aware private
kernels. Both constants are explicit and strictly positive. -/
theorem source_cumulative_rate (cycle : EquilibriumCyclePrinciple)
    (N : ℕ) (hN : 2500 ≤ N) :
    0 < cumulativeConstant ∧ 0 < cumulativeUpperConstant ∧
    ENNReal.ofReal (cumulativeConstant * Real.sqrt N) ≤ minimaxCumulativeRisk N ∧
    minimaxCumulativeRisk N ≤
      (⨆ μ : Law, AnytimePrediction.cumulativeRisk μ N) ∧
    (⨆ μ : Law, AnytimePrediction.cumulativeRisk μ N) ≤
      ENNReal.ofReal (cumulativeUpperConstant * Real.sqrt N) := by
  refine ⟨cumulativeConstant_pos, cumulativeUpperConstant_pos,
    minimax_cumulative_sqrt_lower cycle N hN, ?_, ?_⟩
  · exact iInf_le _ AnytimePrediction.predictor
  · exact iSup_le fun μ => anytime_cumulative_sqrt_upper μ N (by omega)

/-- Quantified asymptotic form of G.3 with explicit eventual threshold. -/
theorem cumulative_minimax_rate (cycle : EquilibriumCyclePrinciple) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ N : ℕ, 2500 ≤ N →
      ENNReal.ofReal (c * Real.sqrt N) ≤ minimaxCumulativeRisk N ∧
      minimaxCumulativeRisk N ≤ ENNReal.ofReal (C * Real.sqrt N) := by
  refine ⟨cumulativeConstant, cumulativeUpperConstant, cumulativeConstant_pos,
    cumulativeUpperConstant_pos, ?_⟩
  intro N hN
  exact ⟨minimax_cumulative_sqrt_lower cycle N hN,
    minimax_cumulative_sqrt_upper N (by omega)⟩

end Paper37.CumulativePrediction
