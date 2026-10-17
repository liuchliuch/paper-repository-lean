import Paper36.SourceTheorems
import Paper36.StageExactCalls

/-! Original source-process H=1 endpoints, including approximate guarantees
only at realized calls and exact zero reward shortfall. -/
namespace Paper36.SourceEndpointTheorems
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested
  Paper36.Statistical Paper36.SourceReplay
open scoped BigOperators
noncomputable section
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  {M Code : Type*} [MeasurableSpace M] [StandardBorelSpace M] [Nonempty M]
  [MeasurableSpace Code] (s₀ : S)
  (ν : Measure M) [IsProbabilityMeasure ν]
  (rows : M → S × A → CVaR.Law S)
  (hrows : ∀ r t, Measurable (fun m => (rows m r).mass t))
  (π : Code → Simulation.Policy S A)
  (hπ : ∀ h s a, Measurable (fun c => (π c h s).mass a))
  (planner : ProbabilityTheory.Kernel (History (M × Code) S A 1) (M × Code))
  [IsMarkovKernel planner] (dummy : Draw (M × Code) A 1)
  (hBayes : SourceSystem.BayesLaw 1 s₀ ν rows hrows π hπ planner dummy)


/-- H=1 approximate realized-call endpoint on the original experiment. -/
theorem corollary_B_1_horizon_one
    (α τ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (ε ζ : ℕ → ℝ) :
    let P := SourceSystem.toPosteriorSystem 1 s₀ ν rows hrows π hπ planner dummy hBayes
    ∀ (O : BorelAlgorithm.BorelOracles α c r 1 s₀ τ (Main.support P))
      (hcert : ∀ᵐ ω ∂SourceSystem.μ 1 s₀ ν rows hrows π hπ planner dummy, Main.RealizedCertificates P α τ c r ε ζ ω) (K : ℕ),
    (∫ ω, Assembly.total (fun n ω => Main.trueRisk P α c n ω - τ) K ω ∂SourceSystem.μ 1 s₀ ν rows hrows π hπ planner dummy) ≤ ∑ n ∈ Finset.range K, ε n ∧
    (∫ ω, Assembly.total (fun n ω => Main.optimum P α τ c r ω - Main.trueReward P r n ω) K ω ∂SourceSystem.μ 1 s₀ ν rows hrows π hπ planner dummy) ≤ ∑ n ∈ Finset.range K, ζ n := by
  dsimp only
  intro O hcert K
  exact Main.corollary_B_1_horizon_one_realized_calls
    (SourceSystem.toPosteriorSystem 1 s₀ ν rows hrows π hπ planner dummy hBayes) α τ hα hα1 c r hc hr O ε ζ hcert K

/-- H=1 exact endpoint on the original experiment. -/
theorem theorem_4_2_horizon_one
    (α τ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) :
    let P := SourceSystem.toPosteriorSystem 1 s₀ ν rows hrows π hπ planner dummy hBayes
    ∀ (O : BorelAlgorithm.BorelOracles α c r 1 s₀ τ (Main.support P))
      (hcert : ∀ᵐ ω ∂SourceSystem.μ 1 s₀ ν rows hrows π hπ planner dummy, Main.RealizedCertificates P α τ c r (fun _ => 0) (fun _ => 0) ω) (K : ℕ),
    (∫ ω, Assembly.total (fun n ω => Main.trueRisk P α c n ω - τ) K ω ∂SourceSystem.μ 1 s₀ ν rows hrows π hπ planner dummy) ≤ 0 ∧
    (∫ ω, Assembly.total (fun n ω => Main.optimum P α τ c r ω - Main.trueReward P r n ω) K ω ∂SourceSystem.μ 1 s₀ ν rows hrows π hπ planner dummy) = 0 ∧
    (∀ ω, Bank.bank (Main.target (S:=S) (A:=A) (H:=0) α)
      (fun j => Main.deposit P α τ c j ω) K = 0 ∧
      Bank.count (Main.target (S:=S) (A:=A) (H:=0) α)
        (fun j => Main.deposit P α τ c j ω) K = 0) := by
  dsimp only
  intro O hcert K
  exact Main.theorem_4_2_horizon_one_realized_calls
    (SourceSystem.toPosteriorSystem 1 s₀ ν rows hrows π hπ planner dummy hBayes) α τ hα hα1 c r hc hr O hcert K

/-- H=1 approximate realized-call endpoint on the original experiment. -/
theorem stage_corollary_B_1_horizon_one
    (β : ℕ → ℝ) (τ : ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (ε ζ : ℕ → ℝ) :
    let P := SourceSystem.toPosteriorSystem 1 s₀ ν rows hrows π hπ planner dummy hBayes
    ∀ (O : StageAlgorithm.BorelOracles β c r 1 s₀ τ (StageMain.support P))
      (hcert : ∀ᵐ ω ∂SourceSystem.μ 1 s₀ ν rows hrows π hπ planner dummy, ∀ n,
      ¬Bank.calibrates (StageMain.target (S:=S) (A:=A) (H:=0) β)
        (fun j => StageMain.deposit P β τ c j ω) n →
      StageMain.sampledRisk P β c n ω ≤ τ + ε n ∧
        StageMain.sampledOptimum P β τ c r n ω - StageMain.sampledReward P r n ω ≤ ζ n) (K : ℕ),
    (∫ ω, Assembly.total (fun n ω => StageMain.trueRisk P β c n ω - τ) K ω ∂SourceSystem.μ 1 s₀ ν rows hrows π hπ planner dummy) ≤ ∑ n ∈ Finset.range K, ε n ∧
    (∫ ω, Assembly.total (fun n ω => StageMain.optimum P β τ c r ω - StageMain.trueReward P r n ω) K ω ∂SourceSystem.μ 1 s₀ ν rows hrows π hπ planner dummy) ≤ ∑ n ∈ Finset.range K, ζ n := by
  dsimp only
  intro O hcert K
  exact StageMain.corollary_B_1_horizon_one_realized_calls
    (SourceSystem.toPosteriorSystem 1 s₀ ν rows hrows π hπ planner dummy hBayes) β τ hβ c r hc hr O ε ζ hcert K

/-- H=1 exact endpoint on the original experiment. -/
theorem stage_theorem_4_2_horizon_one
    (β : ℕ → ℝ) (τ : ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) :
    let P := SourceSystem.toPosteriorSystem 1 s₀ ν rows hrows π hπ planner dummy hBayes
    ∀ (O : StageAlgorithm.BorelOracles β c r 1 s₀ τ (StageMain.support P))
      (hcert : ∀ᵐ ω ∂SourceSystem.μ 1 s₀ ν rows hrows π hπ planner dummy, ∀ n,
      ¬Bank.calibrates (StageMain.target (S:=S) (A:=A) (H:=0) β)
        (fun j => StageMain.deposit P β τ c j ω) n →
      StageMain.sampledRisk P β c n ω ≤ τ + 0 ∧
        StageMain.sampledOptimum P β τ c r n ω - StageMain.sampledReward P r n ω ≤ 0) (K : ℕ),
    (∫ ω, Assembly.total (fun n ω => StageMain.trueRisk P β c n ω - τ) K ω ∂SourceSystem.μ 1 s₀ ν rows hrows π hπ planner dummy) ≤ 0 ∧
    (∫ ω, Assembly.total (fun n ω => StageMain.optimum P β τ c r ω - StageMain.trueReward P r n ω) K ω ∂SourceSystem.μ 1 s₀ ν rows hrows π hπ planner dummy) = 0 ∧
    (∀ ω, Bank.bank (StageMain.target (S:=S) (A:=A) (H:=0) β)
      (fun j => StageMain.deposit P β τ c j ω) K = 0 ∧
      Bank.count (StageMain.target (S:=S) (A:=A) (H:=0) β)
        (fun j => StageMain.deposit P β τ c j ω) K = 0) := by
  dsimp only
  intro O hcert K
  exact StageMain.theorem_4_2_horizon_one_realized_calls
    (SourceSystem.toPosteriorSystem 1 s₀ ν rows hrows π hπ planner dummy hBayes) β τ hβ c r hc hr O hcert K

end
end Paper36.SourceEndpointTheorems
