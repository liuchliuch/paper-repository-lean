import Paper36.StageRealized

/-! Exact H=1 performance for arbitrary realized exact-oracle choices, without
fixing a selector as a function only of the current sampled model. -/
namespace Paper36.StageMain
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested Paper36.StageAlgorithm
  Paper36.StatisticalCounts Paper36.Statistical
open scoped BigOperators
noncomputable section
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {Ω Info Model Hist : Type*} [MeasurableSpace Ω] [MeasurableSpace Info]
  [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model] [MeasurableSpace Hist]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {s₀ : S}
  {E : EpisodeSystem μ Info S A 1 s₀}
  (P : PosteriorSystem (Model := Model) (Hist := Hist) E)

theorem theorem_4_2_horizon_one_realized_calls
    (β : ℕ → ℝ) (τ : ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (O : StageAlgorithm.BorelOracles β c r 1 s₀ τ (support P))
    (hexploit : ∀ᵐ ω ∂μ, ∀ n,
      ¬Bank.calibrates (target (S := S) (A := A) (H := 0) β)
        (fun j => deposit P β τ c j ω) n →
      sampledRisk P β c n ω ≤ τ + 0 ∧
        sampledOptimum P β τ c r n ω - sampledReward P r n ω ≤ 0) (K : ℕ) :
    ((∫ ω, Assembly.total (fun n ω => trueRisk P β c n ω - τ) K ω ∂μ) ≤ 0) ∧
    ((∫ ω, Assembly.total (fun n ω => optimum P β τ c r ω - trueReward P r n ω) K ω ∂μ) = 0) ∧
    (∀ ω, Bank.bank (target (S := S) (A := A) (H := 0) β) (fun j => deposit P β τ c j ω) K = 0 ∧
      Bank.count (target (S := S) (A := A) (H := 0) β) (fun j => deposit P β τ c j ω) K = 0) := by
  have hb := corollary_B_1_horizon_one_realized_calls P β τ hβ c r hc hr O
    (fun _ => 0) (fun _ => 0) hexploit K
  simp only [Finset.sum_const_zero] at hb
  refine ⟨hb.1, le_antisymm hb.2 ?_, ?_⟩
  · apply integral_nonneg_of_ae
    filter_upwards [hexploit, support_ae P] with ω hex hs
    apply Finset.sum_nonneg
    intro n _
    have hnc : ¬ Bank.calibrates (target (S := S) (A := A) (H := 0) β)
        (fun j => deposit P β τ c j ω) n := by
      rw [target, StageEndpoints.horizon_one_target]
      unfold Bank.calibrates
      rw [(Bank.zero_target _ n).1]
      exact lt_irrefl _
    have hf := (hex n hnc).1
    have hm := (StageEndpoints.one_stage_model_independent β hβ c r hc
      (policy P n ω) (truth P ω) (samples P n ω) 0 s₀).1
    have hft : StageAlgorithm.risk β c (policy P n ω) (truth P ω) 1 0 s₀ ≤ τ := by
      change trueRisk P β c n ω = sampledRisk P β c n ω at hm
      simpa only [add_zero, ← hm] using hf
    have ho := O.exp_optimal (truth P ω) hs.1 (policy P n ω) hft
    rw [← StageAlgorithm.constrainedValue_eq O.toOracles hs.1] at ho
    exact sub_nonneg.mpr ho
  · intro ω
    rw [target, StageEndpoints.horizon_one_target]
    exact Bank.zero_target _ K

end
end Paper36.StageMain
