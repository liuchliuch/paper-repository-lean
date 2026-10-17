import Paper37.RateUpper
import Paper37.CycleGoodEvent
import Paper37.PeriodMinimax
import Paper37.TailAdaptation
import Paper37.ZeroHistory
import Paper37.CumulativePrediction
import Paper37.IntegerPredictor

/-! The source's statistical main conclusions, on the original actual renewal
laws and arbitrary privately randomized prediction kernels. Computational
program certificates are kept separate until their uniform syntax is joined. -/
namespace Paper37.MainResults
open Paper37.Renewal Paper37.Prediction Paper37.AnalyticBounds
open Paper37.EquilibriumCycle Paper37.CompressionPrediction
open scoped ENNReal

/-- Equations 2.8--2.10, preserving both distinct minimax criteria, the same
source upper-bound predictor, explicit constants and original cutoffs. The
sole explicit classical input is the generic equilibrium-cycle projection. -/
theorem main_statistical_chain (cycle : EquilibriumCyclePrinciple) (n : ℕ) (hn : 1≤n) :
    substitutedMinimaxRisk n = ENNReal.ofReal (Real.log 2) ∧
    minimaxRisk n ≤ (⨆ μ : Law,risk n (sourcePredictor n (by omega)) μ) ∧
    (⨆ μ : Law,risk n (sourcePredictor n (by omega)) μ) ≤
      ENNReal.ofReal ((redundancyBound (n+1)+Real.log (n+2))/n) ∧
    ENNReal.ofReal ((redundancyBound (n+1)+Real.log (n+2))/n) ≤
      ENNReal.ofReal ((2*Real.pi/Real.sqrt 3+3*Real.sqrt 2)/Real.sqrt n) ∧
    (600≤n → ENNReal.ofReal (11*(Real.log 2-1/2)/(40600*Real.sqrt n))≤minimaxRisk n) := by
  obtain ⟨h1,h2,h3⟩ := Paper37.RateUpper.fixed_time_upper_chain n hn
  exact ⟨substitutedMinimaxRisk_eq_log_two n,h1,h2,h3,
    fun h => Paper37.CycleGoodEvent.minimax_lower_bound cycle h⟩

/-- The information-theoretic fixed-time rate as explicit uniform positive
constants, with no mean bound, no tail bound, and randomized minimax infimum. -/
theorem fixed_time_minimax_rate (cycle : EquilibriumCyclePrinciple) :
    ∃ c C : ℝ,0<c ∧ 0<C ∧ ∀ n : ℕ,600≤n →
      ENNReal.ofReal (c/Real.sqrt n)≤minimaxRisk n ∧
      minimaxRisk n≤ENNReal.ofReal (C/Real.sqrt n) := by
  refine ⟨11*(Real.log 2-1/2)/40600,
    2*Real.pi/Real.sqrt 3+3*Real.sqrt 2,?_,?_,?_⟩
  · exact div_pos (mul_pos (by norm_num) Paper37.LowerBound.radius_coefficient_pos) (by norm_num)
  · positivity
  · intro n hn
    have hl := Paper37.CycleGoodEvent.minimax_lower_bound cycle hn
    have hu := Paper37.RateUpper.fixed_time_upper_chain n (by omega)
    constructor
    · simpa only [div_div,mul_assoc] using hl
    · exact hu.1.trans (hu.2.1.trans hu.2.2)

/-- The exact rational compression predictor admits an integer-only output
algorithm. This is a semantic implementation identity, separate from its
finite-program/time certificate. -/
theorem integer_predictor_implements_source (n : ℕ) (x : List Bool) (hx : x.length=n) :
    ((Paper37.IntegerPredictor.predictorPair n x).1:ℚ)/
      (Paper37.IntegerPredictor.predictorPair n x).2 = predict n x :=
  Paper37.IntegerPredictor.predictorPair_exact n x hx

end Paper37.MainResults
