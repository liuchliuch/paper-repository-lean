import Paper36.StageEndpoints

/-! Corollary B.1 for the literal realized-call contract. Exploitation may
depend on the full history and internal randomness. Only its actual calls are
certified; no approximate selector on all kernels is required. -/
namespace Paper36.StageMain
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested Paper36.StageAlgorithm
  Paper36.StatisticalCounts Paper36.Statistical
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 800000
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {Ω Info Model Hist : Type*} [MeasurableSpace Ω] [MeasurableSpace Info]
  [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model] [MeasurableSpace Hist]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℕ} {s₀ : S}
  {E : EpisodeSystem μ Info S A (H+1) s₀}
  (P : PosteriorSystem (Model := Model) (Hist := Hist) E)

/-- The original B.1 contract: each actual calibration call attains the minimum
risk DP value, and each actual exploitation call has its own two certificates. -/
theorem corollary_B_1_realized_calls
    (external : RowTapes.ExternalCategoricalConcentration (S := S))
    (β : ℕ → ℝ) (τ : ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1) (hτ : 0 ≤ τ)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (hstrict : ∀ q ∈ support P, ∃ π : Simulation.Policy S A,
      StageRisk.risk β c π (RiskBridge.ofKernel q) (H+1) 0 s₀ < τ)
    (O : StageAlgorithm.BorelOracles β c r (H+1) s₀ τ (support P))
    (ε ζ : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hζ : ∀ n, 0 ≤ ζ n)
    (hcal : ∀ᵐ ω ∂μ, ∀ n,
      Bank.calibrates (target (S := S) (A := A) (H := H) β)
        (fun j => deposit P β τ c j ω) n →
      sampledRisk P β c n ω = StageAlgorithm.minimumRisk β c (H+1) s₀ (samples P n ω))
    (hexploit : ∀ᵐ ω ∂μ, ∀ n,
      ¬Bank.calibrates (target (S := S) (A := A) (H := H) β)
        (fun j => deposit P β τ c j ω) n →
      sampledRisk P β c n ω ≤ τ + ε n ∧
        sampledOptimum P β τ c r n ω - sampledReward P r n ω ≤ ζ n) :
    ∀ K, 1 ≤ K →
    ((∫ ω, Assembly.total (fun n ω => trueRisk P β c n ω - τ) K ω ∂μ) ≤
      riskEnvelope (S := S) (A := A) (H := H) β (delta P β τ c) + ∑ n ∈ Finset.range K, ε n) ∧
    ((∫ ω, Assembly.total (fun n ω => optimum P β τ c r ω - trueReward P r n ω) K ω ∂μ) ≤
      rewardAllowance (S := S) (A := A) (H := H) K + (H+1 : ℝ) *
        ((target (S := S) (A := A) (H := H) β K + τ) / delta P β τ c) + ∑ n ∈ Finset.range K, ζ n) ∧
    ((∫ ω, Assembly.countRV (target (S := S) (A := A) (H := H) β) (deposit P β τ c) K ω ∂μ) ≤
      min (K : ℝ) ((target (S := S) (A := A) (H := H) β K + τ) / delta P β τ c)) := by
  intro K hK
  apply certified_performance P external β τ hβ hτ c r hc hr hstrict O ε ζ hε hζ
  · filter_upwards [hcal, hexploit] with ω hca hex
    intro n
    constructor
    · intro hn
      rw [hca n hn]
      simp only [deposit, StageAlgorithm.deposits]
      ring
    · exact fun hn => (hex n hn).1
  · filter_upwards [support_ae P, hexploit] with ω hω hex
    intro n
    constructor
    · intro _
      have hopt := Algorithm.reward_bounds r hr (O.exploitation (samples P n ω))
        (samples P n ω) (H+1) 0 s₀
      have hrew := Algorithm.reward_bounds r hr (policy P n ω) (samples P n ω) (H+1) 0 s₀
      change constrainedValue β c r (H+1) s₀ τ (samples P n ω) -
        Nested.reward r (policy P n ω) (samples P n ω) (H+1) 0 s₀ ≤ _
      rw [constrainedValue_eq O.toOracles (hω.2 n)]
      push_cast at hopt hrew
      linarith [hopt.2, hrew.1]
    · exact fun hn => (hex n hn).2
  · exact hK

section HorizonOne
variable {E₁ : EpisodeSystem μ Info S A 1 s₀}
  (P₁ : PosteriorSystem (Model := Model) (Hist := Hist) E₁)

/-- At H=1 the realized exploitation certificates give exactly the two
error sums, with no approximate oracle off the realized sample path. -/
theorem corollary_B_1_horizon_one_realized_calls
    (β : ℕ → ℝ) (τ : ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (O : StageAlgorithm.BorelOracles β c r 1 s₀ τ (support P₁))
    (ε ζ : ℕ → ℝ)
    (hexploit : ∀ᵐ ω ∂μ, ∀ n,
      ¬Bank.calibrates (target (S := S) (A := A) (H := 0) β)
        (fun j => deposit P₁ β τ c j ω) n →
      sampledRisk P₁ β c n ω ≤ τ + ε n ∧
        sampledOptimum P₁ β τ c r n ω - sampledReward P₁ r n ω ≤ ζ n) (K : ℕ) :
    ((∫ ω, Assembly.total (fun n ω => trueRisk P₁ β c n ω - τ) K ω ∂μ) ≤
      ∑ n ∈ Finset.range K, ε n) ∧
    ((∫ ω, Assembly.total (fun n ω => optimum P₁ β τ c r ω - trueReward P₁ r n ω) K ω ∂μ) ≤
      ∑ n ∈ Finset.range K, ζ n) := by
  have hnot (ω : Ω) (n : ℕ) :
      ¬Bank.calibrates (target (S := S) (A := A) (H := 0) β)
        (fun j => deposit P₁ β τ c j ω) n := by
    rw [target, StageEndpoints.horizon_one_target]
    unfold Bank.calibrates
    rw [(Bank.zero_target _ n).1]
    exact lt_irrefl _
  have hpaths : ∀ᵐ ω ∂μ,
      Assembly.total (fun n ω => trueRisk P₁ β c n ω - τ) K ω ≤ ∑ n ∈ Finset.range K, ε n ∧
      Assembly.total (fun n ω => optimum P₁ β τ c r ω - trueReward P₁ r n ω) K ω ≤ ∑ n ∈ Finset.range K, ζ n := by
    filter_upwards [support_ae P₁, hexploit] with ω hω hex
    have hh := StageEndpoints.one_stage_approximate_oracles β hβ τ c r hc (truth P₁ ω)
      (fun n => samples P₁ n ω) (fun n => policy P₁ n ω) (O.exploitation (truth P₁ ω)) 0 s₀ ε ζ
      (O.exp_feasible _ hω.1)
      (fun n => (hex n (hnot ω n)).1)
      (fun n π hf => by
        have hcert := (hex n (hnot ω n)).2
        have ho := O.exp_optimal _ (hω.2 n) π hf
        change constrainedValue β c r 1 s₀ τ (samples P₁ n ω) -
          Nested.reward r (policy P₁ n ω) (samples P₁ n ω) 1 0 s₀ ≤ ζ n at hcert
        rw [constrainedValue_eq O.toOracles (hω.2 n)] at hcert
        linarith) K
    simpa only [Assembly.total, trueRisk, trueReward, optimum, constrainedValue_eq O.toOracles hω.1] using hh
  constructor
  · have hi := Assembly.integrable_total (fun n ω => trueRisk P₁ β c n ω - τ)
      (fun n => (trueRisk_integrable P₁ β hβ c hc n).sub (integrable_const τ)) K
    have hh := integral_mono_ae hi (integrable_const (∑ n ∈ Finset.range K, ε n)) (hpaths.mono (fun _ h => h.1))
    simpa only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] using hh
  · have hi := Assembly.integrable_total (fun n ω => optimum P₁ β τ c r ω - trueReward P₁ r n ω)
      (fun n => (optimum_integrable P₁ O hr).sub (trueReward_integrable P₁ r hr n)) K
    have hh := integral_mono_ae hi (integrable_const (∑ n ∈ Finset.range K, ζ n)) (hpaths.mono (fun _ h => h.2))
    simpa only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] using hh

end HorizonOne
end
end Paper36.StageMain
