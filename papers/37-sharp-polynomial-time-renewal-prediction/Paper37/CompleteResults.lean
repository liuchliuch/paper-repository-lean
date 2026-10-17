import Paper37.MainResults
import Paper37.UniformPredictionMachine
import Paper37.UniformAdaptivePredictionMachine
import Paper37.AnytimeMachine

/-! The statistical rate and the concrete polynomial-time implementation refer
to the same source prediction rule. Classical input parameters are kept visible
at this final connection; no source-specific risk or complexity premise occurs. -/
namespace Paper37.CompleteResults
noncomputable section
open Paper37.Renewal Paper37.Prediction Paper37.CompressionPrediction
open Paper37.EquilibriumCycle Paper37.BoundedLoopMachine
open Paper37.BoundedLoop Paper37.BoundedLoopEncoding Paper37.UniformPredictionMachine
open scoped ENNReal

/-- Fixed-time polynomial-time attainment, with the source's original lower
cutoff and explicit constants, actual stationary-history ENNReal risk and the
privately randomized minimax infimum. The same one finite binary TM handles
every history length and emits the exact rate-attaining source prediction. -/
theorem fixed_time_rate_attainment (cycle : EquilibriumCyclePrinciple)
    (simulation : BoundedLoopSimulationPrinciple) :
    ∃ M : Turing.TM2ComputableInPolyTime sourceEncoding valueEncoding sourceRun,
      (∀ k : M.tm.K, Finite (M.tm.Γ k)) ∧
      (∀ x : List Bool, 0<x.length →
        0<((sourceRun x).arrayVal[1]?.getD (Value.nat 0)).natVal) ∧
      (∀ x : List Bool, (((sourceRun x).arrayVal[0]?.getD (Value.nat 0)).natVal:ℚ) /
        ((sourceRun x).arrayVal[1]?.getD (Value.nat 0)).natVal=predict x.length x) ∧
      (∀ (n : ℕ) (hn : 600≤n),
        ENNReal.ofReal (11*(Real.log 2-1/2)/(40600*Real.sqrt n))≤minimaxRisk n ∧
        minimaxRisk n≤(⨆ μ : Law,risk n (sourcePredictor n (by omega)) μ) ∧
        (⨆ μ : Law,risk n (sourcePredictor n (by omega)) μ)≤
          ENNReal.ofReal ((2*Real.pi/Real.sqrt 3+3*Real.sqrt 2)/Real.sqrt n)) := by
  obtain ⟨M,hfinite,hden,hexact⟩:=actualPredictor_polytime simulation
  refine ⟨M,hfinite,hden,hexact,?_⟩
  intro n hn
  have h:=Paper37.MainResults.main_statistical_chain cycle n (by omega)
  exact ⟨h.2.2.2.2 hn,h.2.1,h.2.2.1.trans h.2.2.2.1⟩

/-- The adaptive oracle uses precisely the parameter computed by the one
uniform adaptive machine, and receives no support-size or tail parameter. -/
theorem adaptive_rate_attainment (simulation : BoundedLoopSimulationPrinciple) :
    ∃ M : Turing.TM2ComputableInPolyTime sourceEncoding valueEncoding
        Paper37.UniformAdaptivePredictionMachine.sourceRun,
      (∀ k : M.tm.K, Finite (M.tm.Γ k)) ∧
      (∀ x : List Bool,
        ((((Paper37.UniformAdaptivePredictionMachine.sourceRun x).arrayVal[0]?.getD
          (Value.nat 0)).natVal:ℚ) /
          ((Paper37.UniformAdaptivePredictionMachine.sourceRun x).arrayVal[1]?.getD
            (Value.nat 0)).natVal)=Paper37.Adaptive.adaptivePredict x.length x) ∧
      (∀ (μ : Law) (n : ℕ) (hn : 0<n),
        risk n (Paper37.AdaptivePrediction.sourcePredictor n hn) μ≤ENNReal.ofReal
          ((Real.log 2+min (Paper37.AnalyticBounds.redundancyBound (n+1))
            ((2*Paper37.AnalyticBounds.occupiedComplexity (n+1) (fun d => μ.mass (d-1))
              (mean μ)+6)*Real.log (n+2:ℝ))+Real.log (n+2:ℝ))/n)) := by
  obtain ⟨M,hfinite⟩:=Paper37.UniformAdaptivePredictionMachine.sourceTM_exists simulation
  exact ⟨M,hfinite,Paper37.UniformAdaptivePredictionMachine.sourceRun_exact,
    Paper37.AdaptivePrediction.adaptive_risk_oracle⟩

/-- A single horizon-free finite machine implements the very dyadic restart
kernel in the cumulative minimax upper and lower rate theorem. -/
theorem anytime_rate_attainment (cycle : EquilibriumCyclePrinciple)
    (simulation : BoundedLoopSimulationPrinciple) :
    ∃ M : Turing.TM2ComputableInPolyTime sourceEncoding valueEncoding
        Paper37.AnytimeMachine.sourceRun,
      (∀ k : M.tm.K, Finite (M.tm.Γ k)) ∧
      (∀ x : List Bool,
        (((Paper37.AnytimeMachine.sourceRun x).arrayVal[0]?.getD (Value.nat 0)).natVal:ℝ)/
          ((Paper37.AnytimeMachine.sourceRun x).arrayVal[1]?.getD (Value.nat 0)).natVal=
            Paper37.AnytimePrediction.onlineKernel x true) ∧
      (∀ (N : ℕ) (hN : 2500≤N),
        ENNReal.ofReal (Paper37.CumulativeLower.cumulativeConstant*Real.sqrt N)≤
          Paper37.CumulativeLower.minimaxCumulativeRisk N ∧
        Paper37.CumulativeLower.minimaxCumulativeRisk N≤(⨆ μ : Law,Paper37.AnytimePrediction.cumulativeRisk μ N) ∧
        (⨆ μ : Law,Paper37.AnytimePrediction.cumulativeRisk μ N)≤
          ENNReal.ofReal (Paper37.CumulativeLower.cumulativeUpperConstant*Real.sqrt N)) := by
  obtain ⟨M,hfinite,hden,hexact⟩:=Paper37.AnytimeMachine.sourceTM_exists simulation
  refine ⟨M,hfinite,hexact,?_⟩
  intro N hN
  have h:=Paper37.CumulativePrediction.source_cumulative_rate cycle N hN
  exact h.2.2

end
end Paper37.CompleteResults
