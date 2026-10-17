import Paper36.SourceSystem
import Paper36.SourceFiltration
import Paper36.MainRealized
import Paper36.StageRealized

/-! Final source-level statements. The experiment is constructed from an
arbitrary prior and the native posterior/planner kernel; there is no abstract
PosteriorSystem, physical-law or fresh-unused-tape premise. Exact posterior
sampling and the original oracle execution specifications remain explicit.
The source's natural filtration and trajectory adaptation are derived. -/
namespace Paper36.SourceTheorems
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested
  Paper36.Statistical Paper36.SourceReplay
open scoped BigOperators
noncomputable section
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  {M Code : Type*} [MeasurableSpace M] [StandardBorelSpace M] [Nonempty M]
  [MeasurableSpace Code] {H : ℕ} (s₀ : S)
  (ν : Measure M) [IsProbabilityMeasure ν]
  (rows : M → S × A → CVaR.Law S)
  (hrows : ∀ r t, Measurable (fun m => (rows m r).mass t))
  (π : Code → Simulation.Policy S A)
  (hπ : ∀ h s a, Measurable (fun c => (π c h s).mass a))
  (planner : ProbabilityTheory.Kernel (History (M × Code) S A (H+1)) (M × Code))
  [IsMarkovKernel planner] (dummy : Draw (M × Code) A (H+1))
  (hBayes : SourceSystem.BayesLaw (H+1) s₀ ν rows hrows π hπ planner dummy)

/-- Theorem 4.2 on the constructed original source experiment. -/
theorem theorem_4_2
    (external : RowTapes.ExternalCategoricalConcentration (S:=S))
    (α τ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hτ : 0 ≤ τ)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) :
    let P := SourceSystem.toPosteriorSystem (H+1) s₀ ν rows hrows π hπ planner dummy hBayes
    ∀ (hstrict : ∀ q ∈ Main.support P, minimumRisk α c (H+1) 0 s₀ q < τ)
      (O : BorelAlgorithm.BorelOracles α c r (H+1) s₀ τ (Main.support P))
      (hrun : ∀ n ω, Main.policy P n ω = Algorithm.selected O.toOracles
        (Main.target (S:=S) (A:=A) (H:=H) α) (Main.samples P) n ω),
    ∀ K, 1 ≤ K →
    ((∫ ω, Assembly.total (fun n ω => Main.trueRisk P α c n ω - τ) K ω ∂SourceSystem.μ (H+1) s₀ ν rows hrows π hπ planner dummy) ≤
      SourceBank.riskEnvelope (S:=S) (A:=A) α (Main.delta P α τ c) (H+1)) ∧
    ((∫ ω, Assembly.total (fun n ω => Main.optimum P α τ c r ω - Main.trueReward P r n ω) K ω ∂SourceSystem.μ (H+1) s₀ ν rows hrows π hπ planner dummy) ≤
      Main.rewardAllowance (S:=S) (A:=A) (H:=H) K + (H+1 : ℝ) * ((Main.target (S:=S) (A:=A) (H:=H) α K + τ) / Main.delta P α τ c)) ∧
    ((∫ ω, Assembly.countRV (Main.target (S:=S) (A:=A) (H:=H) α) (Main.deposit P α τ c) K ω ∂SourceSystem.μ (H+1) s₀ ν rows hrows π hπ planner dummy) ≤
      min (K:ℝ) ((Main.target (S:=S) (A:=A) (H:=H) α K + τ) / Main.delta P α τ c)) := by
  dsimp only
  intro hstrict O hrun
  exact Main.theorem_4_2 (SourceSystem.toPosteriorSystem (H+1) s₀ ν rows hrows π hπ planner dummy hBayes) external α τ hα hα1 hτ c r hc hr hstrict O hrun

/-- The original fixed-pair risk-bank certificate, with its filtration and
complete-trajectory adaptation proved by construction. -/
theorem risk_bank_certificate
    (external : RowTapes.ExternalCategoricalConcentration (S:=S))
    (α τ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    {K : ℕ} (hK : 1 ≤ K) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    let P := SourceSystem.toPosteriorSystem (H+1) s₀ ν rows hrows π hπ planner dummy hBayes
    ∀ (O : BorelAlgorithm.BorelOracles α c r (H+1) s₀ τ (Main.support P))
      (hrun : ∀ n ω, Main.policy P n ω = Algorithm.selected O.toOracles
        (Main.target (S:=S) (A:=A) (H:=H) α) (Main.samples P) n ω),
    (SourceSystem.μ (H+1) s₀ ν rows hrows π hπ planner dummy).real {ω | Bounds.certificate (Fintype.card S) (Fintype.card A) (H+1) (Weights.W α (H+1)) (Weights.w α (H+1)) δ K -
      Bank.bank (Main.target (S:=S) (A:=A) (H:=H) α) (fun j => Main.deposit P α τ c j ω) K <
      Assembly.total (fun n ω => Main.trueRisk P α c n ω - τ) K ω} ≤ δ := by
  dsimp only
  intro O hrun
  exact Main.risk_bank_certificate (SourceSystem.toPosteriorSystem (H+1) s₀ ν rows hrows π hπ planner dummy hBayes) external α τ hα hα1 c r hc O hrun
    (SourceFiltration.naturalFiltration s₀ dummy) (SourceFiltration.info_comap s₀ dummy)
    (SourceFiltration.path_measurable s₀ dummy) hK hδ hδ1

/-- Theorem 4.2 under stage-dependent masses (B.3) on the constructed original source experiment. -/
theorem stage_theorem_4_2
    (external : RowTapes.ExternalCategoricalConcentration (S:=S))
    (β : ℕ → ℝ) (τ : ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1) (hτ : 0 ≤ τ)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) :
    let P := SourceSystem.toPosteriorSystem (H+1) s₀ ν rows hrows π hπ planner dummy hBayes
    ∀ (hstrict : ∀ q ∈ StageMain.support P, ∃ ρ : Simulation.Policy S A,
      StageRisk.risk β c ρ (RiskBridge.ofKernel q) (H+1) 0 s₀ < τ)
      (O : StageAlgorithm.BorelOracles β c r (H+1) s₀ τ (StageMain.support P))
      (hrun : ∀ n ω, StageMain.policy P n ω = StageAlgorithm.selected O.toOracles
        (StageMain.target (S:=S) (A:=A) (H:=H) β) (StageMain.samples P) n ω),
    ∀ K, 1 ≤ K →
    ((∫ ω, Assembly.total (fun n ω => StageMain.trueRisk P β c n ω - τ) K ω ∂SourceSystem.μ (H+1) s₀ ν rows hrows π hπ planner dummy) ≤
      StageMain.riskEnvelope (S:=S) (A:=A) (H:=H) β (StageMain.delta P β τ c)) ∧
    ((∫ ω, Assembly.total (fun n ω => StageMain.optimum P β τ c r ω - StageMain.trueReward P r n ω) K ω ∂SourceSystem.μ (H+1) s₀ ν rows hrows π hπ planner dummy) ≤
      StageMain.rewardAllowance (S:=S) (A:=A) (H:=H) K + (H+1 : ℝ) * ((StageMain.target (S:=S) (A:=A) (H:=H) β K + τ) / StageMain.delta P β τ c)) ∧
    ((∫ ω, Assembly.countRV (StageMain.target (S:=S) (A:=A) (H:=H) β) (StageMain.deposit P β τ c) K ω ∂SourceSystem.μ (H+1) s₀ ν rows hrows π hπ planner dummy) ≤
      min (K:ℝ) ((StageMain.target (S:=S) (A:=A) (H:=H) β K + τ) / StageMain.delta P β τ c)) := by
  dsimp only
  intro hstrict O hrun
  exact StageMain.theorem_4_2 (SourceSystem.toPosteriorSystem (H+1) s₀ ν rows hrows π hπ planner dummy hBayes) external β τ hβ hτ c r hc hr hstrict O hrun

/-- The original fixed-pair risk-bank certificate, with its filtration and
complete-trajectory adaptation proved by construction. -/
theorem stage_risk_bank_certificate
    (external : RowTapes.ExternalCategoricalConcentration (S:=S))
    (β : ℕ → ℝ) (τ : ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    {K : ℕ} (hK : 1 ≤ K) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    let P := SourceSystem.toPosteriorSystem (H+1) s₀ ν rows hrows π hπ planner dummy hBayes
    ∀ (O : StageAlgorithm.BorelOracles β c r (H+1) s₀ τ (StageMain.support P))
      (hrun : ∀ n ω, StageMain.policy P n ω = StageAlgorithm.selected O.toOracles
        (StageMain.target (S:=S) (A:=A) (H:=H) β) (StageMain.samples P) n ω),
    (SourceSystem.μ (H+1) s₀ ν rows hrows π hπ planner dummy).real {ω | Bounds.certificate (Fintype.card S) (Fintype.card A) (H+1) (Real.sqrt (Weights.stageWsq β (H+1))) (Weights.stagew β (H+1)) δ K -
      Bank.bank (StageMain.target (S:=S) (A:=A) (H:=H) β) (fun j => StageMain.deposit P β τ c j ω) K <
      Assembly.total (fun n ω => StageMain.trueRisk P β c n ω - τ) K ω} ≤ δ := by
  dsimp only
  intro O hrun
  exact StageMain.risk_bank_certificate (SourceSystem.toPosteriorSystem (H+1) s₀ ν rows hrows π hπ planner dummy hBayes) external β τ hβ c r hc O hrun
    (SourceFiltration.naturalFiltration s₀ dummy) (SourceFiltration.info_comap s₀ dummy)
    (SourceFiltration.path_measurable s₀ dummy) hK hδ hδ1

/-- Corollary B.1, with errors certified only at actual calls of
the constructed original source process. -/
theorem corollary_B_1
    (external : RowTapes.ExternalCategoricalConcentration (S:=S))
    (α τ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hτ : 0 ≤ τ)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (ε ζ : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hζ : ∀ n, 0 ≤ ζ n) :
    let P := SourceSystem.toPosteriorSystem (H+1) s₀ ν rows hrows π hπ planner dummy hBayes
    ∀ (hstrict : ∀ q ∈ Main.support P, minimumRisk α c (H+1) 0 s₀ q < τ)
      (O : BorelAlgorithm.BorelOracles α c r (H+1) s₀ τ (Main.support P))
      (hcert : ∀ᵐ ω ∂SourceSystem.μ (H+1) s₀ ν rows hrows π hπ planner dummy, Main.RealizedCertificates P α τ c r ε ζ ω),
    ∀ K, 1 ≤ K →
    ((∫ ω, Assembly.total (fun n ω => Main.trueRisk P α c n ω - τ) K ω ∂SourceSystem.μ (H+1) s₀ ν rows hrows π hπ planner dummy) ≤
      SourceBank.riskEnvelope (S:=S) (A:=A) α (Main.delta P α τ c) (H+1) + ∑ n ∈ Finset.range K, ε n) ∧
    ((∫ ω, Assembly.total (fun n ω => Main.optimum P α τ c r ω - Main.trueReward P r n ω) K ω ∂SourceSystem.μ (H+1) s₀ ν rows hrows π hπ planner dummy) ≤
      Main.rewardAllowance (S:=S) (A:=A) (H:=H) K + (H+1 : ℝ) * ((Main.target (S:=S) (A:=A) (H:=H) α K + τ) / Main.delta P α τ c) + ∑ n ∈ Finset.range K, ζ n) ∧
    ((∫ ω, Assembly.countRV (Main.target (S:=S) (A:=A) (H:=H) α) (Main.deposit P α τ c) K ω ∂SourceSystem.μ (H+1) s₀ ν rows hrows π hπ planner dummy) ≤ min (K:ℝ) ((Main.target (S:=S) (A:=A) (H:=H) α K + τ) / Main.delta P α τ c)) := by
  dsimp only
  intro hstrict O hcert
  exact Main.corollary_B_1_realized_calls (SourceSystem.toPosteriorSystem (H+1) s₀ ν rows hrows π hπ planner dummy hBayes) external α τ hα hα1 hτ c r hc hr hstrict O
    ε ζ hε hζ hcert

/-- Corollary B.1 and B.3, with errors certified only at actual calls of
the constructed original source process. -/
theorem stage_corollary_B_1
    (external : RowTapes.ExternalCategoricalConcentration (S:=S))
    (β : ℕ → ℝ) (τ : ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1) (hτ : 0 ≤ τ)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (ε ζ : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hζ : ∀ n, 0 ≤ ζ n) :
    let P := SourceSystem.toPosteriorSystem (H+1) s₀ ν rows hrows π hπ planner dummy hBayes
    ∀ (hstrict : ∀ q ∈ StageMain.support P, ∃ ρ : Simulation.Policy S A,
      StageRisk.risk β c ρ (RiskBridge.ofKernel q) (H+1) 0 s₀ < τ)
      (O : StageAlgorithm.BorelOracles β c r (H+1) s₀ τ (StageMain.support P))
      (hcal : ∀ᵐ ω ∂SourceSystem.μ (H+1) s₀ ν rows hrows π hπ planner dummy, ∀ n,
      Bank.calibrates (StageMain.target (S:=S) (A:=A) (H:=H) β) (fun j => StageMain.deposit P β τ c j ω) n →
        StageMain.sampledRisk P β c n ω = StageAlgorithm.minimumRisk β c (H+1) s₀ (StageMain.samples P n ω))
    (hexploit : ∀ᵐ ω ∂SourceSystem.μ (H+1) s₀ ν rows hrows π hπ planner dummy, ∀ n,
      ¬ Bank.calibrates (StageMain.target (S:=S) (A:=A) (H:=H) β) (fun j => StageMain.deposit P β τ c j ω) n →
        StageMain.sampledRisk P β c n ω ≤ τ + ε n ∧
        StageMain.sampledOptimum P β τ c r n ω - StageMain.sampledReward P r n ω ≤ ζ n),
    ∀ K, 1 ≤ K →
    ((∫ ω, Assembly.total (fun n ω => StageMain.trueRisk P β c n ω - τ) K ω ∂SourceSystem.μ (H+1) s₀ ν rows hrows π hπ planner dummy) ≤
      StageMain.riskEnvelope (S:=S) (A:=A) (H:=H) β (StageMain.delta P β τ c) + ∑ n ∈ Finset.range K, ε n) ∧
    ((∫ ω, Assembly.total (fun n ω => StageMain.optimum P β τ c r ω - StageMain.trueReward P r n ω) K ω ∂SourceSystem.μ (H+1) s₀ ν rows hrows π hπ planner dummy) ≤
      StageMain.rewardAllowance (S:=S) (A:=A) (H:=H) K + (H+1 : ℝ) * ((StageMain.target (S:=S) (A:=A) (H:=H) β K + τ) / StageMain.delta P β τ c) + ∑ n ∈ Finset.range K, ζ n) ∧
    ((∫ ω, Assembly.countRV (StageMain.target (S:=S) (A:=A) (H:=H) β) (StageMain.deposit P β τ c) K ω ∂SourceSystem.μ (H+1) s₀ ν rows hrows π hπ planner dummy) ≤ min (K:ℝ) ((StageMain.target (S:=S) (A:=A) (H:=H) β K + τ) / StageMain.delta P β τ c)) := by
  dsimp only
  intro hstrict O hcal hexploit
  exact StageMain.corollary_B_1_realized_calls (SourceSystem.toPosteriorSystem (H+1) s₀ ν rows hrows π hπ planner dummy hBayes) external β τ hβ hτ c r hc hr hstrict O
    ε ζ hε hζ hcal hexploit

/-- One common probability-one event gives (4.12) for every K and sparse
calibration for this original infinite source process. -/
theorem pathwise_calibration
    (α τ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hτ : 0 ≤ τ)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1) :
    let P := SourceSystem.toPosteriorSystem (H+1) s₀ ν rows hrows π hπ planner dummy hBayes
    ∀ (hstrict : ∀ q ∈ Main.support P, minimumRisk α c (H+1) 0 s₀ q < τ),
    0 < Main.delta P α τ c ∧ ∀ᵐ ω ∂SourceSystem.μ (H+1) s₀ ν rows hrows π hπ planner dummy,
      (∀ K, (Bank.count (Main.target (S:=S) (A:=A) (H:=H) α) (fun j => Main.deposit P α τ c j ω) K : ℝ) ≤
        min (K:ℝ) ((Main.target (S:=S) (A:=A) (H:=H) α K + τ) / Main.delta P α τ c)) ∧
      Filter.Tendsto (fun K : ℕ => (Bank.count (Main.target (S:=S) (A:=A) (H:=H) α)
        (fun j => Main.deposit P α τ c j ω) K : ℝ) / (K:ℝ)) Filter.atTop (nhds 0) := by
  dsimp only
  intro hstrict
  exact Main.pathwise_calibration (SourceSystem.toPosteriorSystem (H+1) s₀ ν rows hrows π hπ planner dummy hBayes) α τ hα hα1 hτ c hc hstrict

/-- One common probability-one event gives (4.12) for every K and sparse
calibration for this original infinite source process. -/
theorem stage_pathwise_calibration
    (β : ℕ → ℝ) (τ : ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1) (hτ : 0 ≤ τ)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1) :
    let P := SourceSystem.toPosteriorSystem (H+1) s₀ ν rows hrows π hπ planner dummy hBayes
    ∀ (hstrict : ∀ q ∈ StageMain.support P, ∃ ρ : Simulation.Policy S A,
      StageRisk.risk β c ρ (RiskBridge.ofKernel q) (H+1) 0 s₀ < τ),
    0 < StageMain.delta P β τ c ∧ ∀ᵐ ω ∂SourceSystem.μ (H+1) s₀ ν rows hrows π hπ planner dummy,
      (∀ K, (Bank.count (StageMain.target (S:=S) (A:=A) (H:=H) β) (fun j => StageMain.deposit P β τ c j ω) K : ℝ) ≤
        min (K:ℝ) ((StageMain.target (S:=S) (A:=A) (H:=H) β K + τ) / StageMain.delta P β τ c)) ∧
      Filter.Tendsto (fun K : ℕ => (Bank.count (StageMain.target (S:=S) (A:=A) (H:=H) β)
        (fun j => StageMain.deposit P β τ c j ω) K : ℝ) / (K:ℝ)) Filter.atTop (nhds 0) := by
  dsimp only
  intro hstrict
  exact StageMain.pathwise_calibration (SourceSystem.toPosteriorSystem (H+1) s₀ ν rows hrows π hπ planner dummy hBayes) β τ hβ hτ c hc hstrict

/-- The actual kernel prior used by the final theorems is precisely the
pushforward of the original input prior. The planner cannot change it. -/
theorem actual_prior :
    let P := SourceSystem.toPosteriorSystem (H+1) s₀ ν rows hrows π hπ planner dummy hBayes
    PosteriorAlgorithm.prior (μ := SourceSystem.μ (H+1) s₀ ν rows hrows π hπ planner dummy) (Main.decode P) P.latent =
      ν.map (fun m => Measurability.regularKernel (fun s a => rows m (s,a))) := by
  let dec : M → Nested.Kernel S A := fun m => Measurability.regularKernel (fun s a => rows m (s,a))
  have hd : Measurable dec := Measurability.measurable_regularKernel _ (fun s a t => hrows (s,a) t)
  have hl : (SourceSystem.μ (H+1) s₀ ν rows hrows π hπ planner dummy).map
      (fun ω : SourceProtocol.Sample M (M × Code) S A (H+1) => ω.1.1) = ν :=
    SourceExperiment.source_latent_law ν rows hrows
      (SourceProtocol.protocolKernel (fun m : M × Code => π m.2)
        (fun h s a => (hπ h s a).comp measurable_snd) planner s₀) dummy
  change (SourceSystem.μ (H+1) s₀ ν rows hrows π hπ planner dummy).map (dec ∘ (fun ω => ω.1.1)) = ν.map dec
  rw [← Measure.map_map hd measurable_fst.fst, hl]

end
end Paper36.SourceTheorems
