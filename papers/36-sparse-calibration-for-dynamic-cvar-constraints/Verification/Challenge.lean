import Paper36.Bank
import Paper36.Complexity
import Paper36.Tightening
import Paper36.CVaR
import Paper36.Regularity
import Paper36.Target
import Paper36.Nested
import Paper36.Calibration
import Paper36.Prior
import Paper36.LowerBound
import Paper36.Assembly
import Paper36.Posterior
import Paper36.CalibrationScan
import Paper36.Algorithm
import Paper36.Approximation
import Paper36.BorelAlgorithm
import Paper36.BankTarget
import Paper36.Bounds
import Paper36.Confidence
import Paper36.Counts
import Paper36.Divergence
import Paper36.Endpoints
import Paper36.FinitePolicies
import Paper36.HeterogeneousRareChain
import Paper36.HybridCharging
import Paper36.Measurability
import Paper36.PosteriorAlgorithm
import Paper36.RareChain
import Paper36.RiskBridge
import Paper36.RowTapes
import Paper36.Scaling
import Paper36.Simulation
import Paper36.SourceBank
import Paper36.SourceEndpoints
import Paper36.StageCalibration
import Paper36.StageCharging
import Paper36.StageRisk
import Paper36.Statistical
import Paper36.StatisticalCounts
import Paper36.Trajectories
import Paper36.Weights
import Paper36.AdaptiveTapes
import Paper36.InfiniteTapes
import Paper36.Main
import Paper36.MainExtensions
import Paper36.MainEndpoints
import Paper36.StageStatistical
import Paper36.StageAlgorithm
import Paper36.SourceScaling
import Paper36.Selection
import Paper36.FiniteStages
import Paper36.StageMain
import Paper36.AdaptiveKernel
import Paper36.AdaptiveKernelLaw
import Paper36.InfiniteExecution
import Paper36.Scope
import Paper36.StageSelection
import Paper36.StageEndpoints
import Paper36.MainRealized
import Paper36.ComplexityEncoding
import Paper36.GapBounds
import Paper36.PolylogScaling
import Paper36.MainParameters
import Paper36.StageRealized
import Paper36.StageParameters
import Paper36.FreshChoice
import Paper36.InfiniteProcess
import Paper36.InfiniteProcessLaw
import Paper36.MixedProcess
import Paper36.SourceBlocks
import Paper36.SourceReplay
import Paper36.SourceExperiment
import Paper36.SourceConditional
import Paper36.SourceProtocol
import Paper36.SourceMarginals
import Paper36.FiniteData
import Paper36.SourceHistory
import Paper36.StageExactCalls
import Paper36.SourceBlockKernel
import Paper36.SourceBlockReplay
import Paper36.SourceInduction
import Paper36.SourcePlanBlock
import Paper36.SourceSummary
import Paper36.SourceStepReplay
import Paper36.SourceFresh
import Paper36.SourceNativeConditional
import Paper36.SourceFiltration
import Paper36.SourceTheorems
import Paper36.SourceSystem
import Paper36.SourceEndpointTheorems

open scoped BigOperators Topology
open Set Filter Finset Paper36
set_option linter.unusedVariables false
attribute [local instance] Classical.propDecidable

/-! Fixed explicit statement contracts. Trusted holes are isolated from production. -/

namespace P36Contract.Bank

section

open Paper36.Bank

/-- Complete declaration of `Paper36.Bank.calibration_count_bound`; source support: S4.Thmtheorem2. -/
theorem calibration_count_bound : ∀ (T d : ℕ → ℝ) (Δ τ : ℝ)
    (hΔ : 0 < Δ) (hT : Monotone T) (hbase : 0 ≤ T 0 + τ)
    (hgap : ∀ n, calibrates T d n → Δ ≤ d (n + 1))
    (hcap : ∀ n, calibrates T d n → d (n + 1) ≤ τ) (K : ℕ),
    (count T d K : ℝ) ≤ min (K : ℝ) ((T K + τ) / Δ) := by
  sorry

end

section

open Paper36.Bank

/-- Complete declaration of `Paper36.Bank.deficit_le_residual`; source support: S4.Thmtheorem2. -/
theorem deficit_le_residual : ∀ (T d : ℕ → ℝ) (Δ R : ℝ) (hzero : T 0 = 0)
    (hgap : ∀ n, calibrates T d n → Δ ≤ d (n + 1))
    (hsub : ∀ j n, T (j + n) ≤ T j + T n)
    (henv : ∀ n, T n - (n : ℝ) * Δ ≤ R) (K : ℕ),
    T K - bank T d K ≤ R := by
  sorry

end

section

open Paper36.Bank

/-- Complete declaration of `Paper36.Bank.zero_target`; source support: S4.Thmtheorem2. -/
theorem zero_target : ∀ (d : ℕ → ℝ) (K : ℕ),
    bank (fun _ => 0) d K = 0 ∧ count (fun _ => 0) d K = 0 := by
  sorry

end

section

open Paper36.Bank

/-- Complete declaration of `Paper36.Bank.sampled_debt_cancellation`; source support: A2.Thmtheorem1. -/
theorem sampled_debt_cancellation : ∀ (T d debt ε : ℕ → ℝ)
    (hε : ∀ n, 0 ≤ ε n)
    (hcal : ∀ n, calibrates T d n → debt n = -d (n + 1))
    (hexp : ∀ n, ¬calibrates T d n → debt n ≤ ε n) (K : ℕ),
    (∑ n ∈ Finset.range K, debt n) ≤
      (∑ n ∈ Finset.range K, ε n) - bank T d K := by
  sorry

end

section

open Paper36.Bank

/-- Complete declaration of `Paper36.Bank.exact_sampled_debt_cancellation`; source support: S4.Thmtheorem2. -/
theorem exact_sampled_debt_cancellation : ∀ (T d debt : ℕ → ℝ)
    (hcal : ∀ n, calibrates T d n → debt n = -d (n + 1))
    (hexp : ∀ n, ¬calibrates T d n → debt n ≤ 0) (K : ℕ),
    (∑ n ∈ Finset.range K, debt n) ≤ -bank T d K := by
  sorry

end

section

open Paper36.Bank

/-- Complete declaration of `Paper36.Bank.sampled_reward_shortfall`; source support: A2.Thmtheorem1. -/
theorem sampled_reward_shortfall : ∀ (T d loss ζ : ℕ → ℝ) (H : ℝ)
    (hζ : ∀ n, 0 ≤ ζ n)
    (hcal : ∀ n, calibrates T d n → loss n ≤ H)
    (hexp : ∀ n, ¬calibrates T d n → loss n ≤ ζ n) (K : ℕ),
    (∑ n ∈ Finset.range K, loss n) ≤
      H * (count T d K : ℝ) + ∑ n ∈ Finset.range K, ζ n := by
  sorry

end

section

open Paper36.Bank

/-- Complete declaration of `Paper36.Bank.risk_decomposition_bound`; source support: S5.Thmtheorem6. -/
theorem risk_decomposition_bound : ∀ (T d risk sampled ε : ℕ → ℝ) (τ : ℝ)
    (hε : ∀ n, 0 ≤ ε n)
    (hcal : ∀ n, calibrates T d n → sampled n = τ - d (n + 1))
    (hexp : ∀ n, ¬calibrates T d n → sampled n ≤ τ + ε n) (K : ℕ),
    (∑ n ∈ Finset.range K, (risk n - τ)) ≤
      (∑ n ∈ Finset.range K, (risk n - sampled n)) +
      (∑ n ∈ Finset.range K, ε n) - bank T d K := by
  sorry

end

section

open Paper36.Bank

/-- Complete declaration of `Paper36.Bank.risk_bound_from_model_envelope`; source support: S4.Thmtheorem2, A2.Thmtheorem1. -/
theorem risk_bound_from_model_envelope : ∀ (T d risk sampled ε : ℕ → ℝ)
    (τ Δ D R : ℝ) (hzero : T 0 = 0)
    (hgap : ∀ n, calibrates T d n → Δ ≤ d (n + 1))
    (hsub : ∀ j n, T (j + n) ≤ T j + T n)
    (henv : ∀ n, T n - (n : ℝ) * Δ ≤ R)
    (hε : ∀ n, 0 ≤ ε n)
    (hcal : ∀ n, calibrates T d n → sampled n = τ - d (n + 1))
    (hexp : ∀ n, ¬calibrates T d n → sampled n ≤ τ + ε n) (K : ℕ)
    (hmodel : (∑ n ∈ Finset.range K, (risk n - sampled n)) ≤ T K + D),
    (∑ n ∈ Finset.range K, (risk n - τ)) ≤
      D + R + ∑ n ∈ Finset.range K, ε n := by
  sorry

end

section

open Paper36.Bank

/-- Complete declaration of `Paper36.Bank.reward_bound_from_count`; source support: S4.Thmtheorem2, A2.Thmtheorem1. -/
theorem reward_bound_from_count : ∀ (T d loss ζ : ℕ → ℝ) (H Δ τ : ℝ)
    (hH : 0 ≤ H) (hΔ : 0 < Δ) (hT : Monotone T) (hbase : 0 ≤ T 0 + τ)
    (hgap : ∀ n, calibrates T d n → Δ ≤ d (n + 1))
    (hcap : ∀ n, calibrates T d n → d (n + 1) ≤ τ)
    (hζ : ∀ n, 0 ≤ ζ n)
    (hcal : ∀ n, calibrates T d n → loss n ≤ H)
    (hexp : ∀ n, ¬calibrates T d n → loss n ≤ ζ n) (K : ℕ),
    (∑ n ∈ Finset.range K, loss n) ≤
      H * ((T K + τ) / Δ) + ∑ n ∈ Finset.range K, ζ n := by
  sorry

end

section

open Paper36.Bank

/-- Complete declaration of `Paper36.Bank.calibration_sparse_of_target_sublinear`; source support: S4.Thmtheorem2. -/
theorem calibration_sparse_of_target_sublinear : ∀ (T d : ℕ → ℝ) (Δ τ : ℝ)
    (hΔ : 0 < Δ) (hT : Monotone T) (hbase : 0 ≤ T 0 + τ)
    (hgap : ∀ n, calibrates T d n → Δ ≤ d (n + 1))
    (hcap : ∀ n, calibrates T d n → d (n + 1) ≤ τ)
    (hsmall : Filter.Tendsto (fun K : ℕ => T K / (K : ℝ))
      Filter.atTop (nhds 0)),
    Filter.Tendsto (fun K : ℕ => (count T d K : ℝ) / (K : ℝ))
      Filter.atTop (nhds 0) := by
  sorry

end

end P36Contract.Bank

namespace P36Contract.Complexity

section
open Set Paper36.Regularity Paper36.Nested
variable {H : ℕ} {S A : Type*} [Fintype S] [Fintype A]

open Paper36.Complexity

/-- Complete declaration of `Paper36.Complexity.bernoulliTail_eq_iff`; source support: S6.Thmtheorem2. -/
theorem bernoulliTail_eq_iff : ∀ {α x : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hx : 0 ≤ x) (hx1 : x ≤ 1),
    bernoulliTail α x = x ↔ x = 0 ∨ x = 1 := by
  sorry

end

section
open Set Paper36.Regularity Paper36.Nested
variable {H : ℕ} {S A : Type*} [Fintype S] [Fintype A]

open Paper36.Complexity

/-- Complete declaration of `Paper36.Complexity.reducedRisk_eq_reward_iff`; source support: S6.Thmtheorem2. -/
theorem reducedRisk_eq_reward_iff : ∀ {ι : Type*} [Fintype ι]
    {α : ℝ} {w x : ι → ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hw : ∀ i, 0 < w i) (hx : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i ≤ 1),
    reducedRisk α w x = linearReward w x ↔ ∀ i, x i = 0 ∨ x i = 1 := by
  sorry

end

section
open Set Paper36.Regularity Paper36.Nested
variable {H : ℕ} {S A : Type*} [Fintype S] [Fintype A]

open Paper36.Complexity

/-- Complete declaration of `Paper36.Complexity.exists_reduced_feasible_iff_subset`; source support: S6.Thmtheorem2. -/
theorem exists_reduced_feasible_iff_subset : ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α B : ℝ} {w : ι → ℝ} (hα : 0 < α) (hα1 : α < 1) (hw : ∀ i, 0 < w i),
    (∃ x : ι → ℝ, (∀ i, 0 ≤ x i) ∧ (∀ i, x i ≤ 1) ∧
      reducedRisk α w x ≤ B ∧ B ≤ linearReward w x) ↔
      ∃ s : Finset ι, ∑ i ∈ s, w i = B := by
  sorry

end

section
open Set Paper36.Regularity Paper36.Nested
variable {H : ℕ} {S A : Type*} [Fintype S] [Fintype A]

open Paper36.Complexity

/-- Complete declaration of `Paper36.Complexity.subset_sum_reduction`; source support: S6.Thmtheorem2. -/
theorem subset_sum_reduction : ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℕ) (B : ℕ) {α C : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hw : ∀ i, 0 < w i) (hC : 0 < C),
    (∃ x : ι → ℝ, (∀ i, 0 ≤ x i) ∧ (∀ i, x i ≤ 1) ∧
      reducedRisk α (fun i => (w i : ℝ) / C) x ≤ (B : ℝ) / C ∧
      (B : ℝ) / C ≤ linearReward (fun i => (w i : ℝ) / C) x) ↔
      ∃ s : Finset ι, ∑ i ∈ s, w i = B := by
  sorry

end

section
open Set Paper36.Regularity Paper36.Nested
variable {H : ℕ} {S A : Type*} [Fintype S] [Fintype A]

open Paper36.Complexity

/-- Complete declaration of `Paper36.Complexity.all_skip_strictly_feasible`; source support: S6.Thmtheorem2. -/
theorem all_skip_strictly_feasible : ∀ {ι : Type*} [Fintype ι]
    (w : ι → ℝ) {α B C : ℝ} (hB : 0 < B) (hC : 0 < C),
    reducedRisk α w (fun _ => 0) = 0 ∧ reducedRisk α w (fun _ => 0) < B / C := by
  sorry

end

section
open Set Paper36.Regularity Paper36.Nested
variable {H : ℕ} {S A : Type*} [Fintype S] [Fintype A]

open Paper36.Complexity

/-- Complete declaration of `Paper36.Complexity.dummy_subset_sum_iff`; source support: S6.Thmtheorem2. -/
theorem dummy_subset_sum_iff : ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℕ) (B : ℕ),
    (∃ s : Finset (Option ι), ∑ i ∈ s, dummyWeight w B i = B) ↔
      ∃ s : Finset ι, ∑ i ∈ s, w i = B := by
  sorry

end

section
open Set Paper36.Regularity Paper36.Nested
variable {H : ℕ} {S A : Type*} [Fintype S] [Fintype A]

open Paper36.Complexity

/-- Complete declaration of `Paper36.Complexity.normalized_weight_bounds`; source support: S6.Thmtheorem2. -/
theorem normalized_weight_bounds : ∀ {ι : Type*} [Fintype ι]
    (w : ι → ℕ) {C : ℝ} (hC : 0 < C) (htot : C = ∑ i, (w i : ℝ)) (i : ι),
    0 ≤ (w i : ℝ) / C ∧ (w i : ℝ) / C ≤ 1 := by
  sorry

end

section
open Set Paper36.Regularity Paper36.Nested
variable {H : ℕ} {S A : Type*} [Fintype S] [Fintype A]

open Paper36.Complexity

/-- Complete declaration of `Paper36.Complexity.planningPolynomial_degree`; source support: S6.Thmtheorem2. -/
theorem planningPolynomial_degree : ∀ (r c : Fin H → S → A → ℚ) (p : S → A → S → ℚ)
    (α τ target : ℚ) (s₀ : S) (k : PlanningConstraint H S A),
    (planningPolynomial r c p α τ target s₀ k).totalDegree ≤ 2 := by
  sorry

end

section
open Set Paper36.Regularity Paper36.Nested
variable {H : ℕ} {S A : Type*} [Fintype S] [Fintype A]

open Paper36.Complexity

/-- Complete declaration of `Paper36.Complexity.planning_variable_count`; source support: S6.Thmtheorem2. -/
theorem planning_variable_count : Fintype.card (PlanningVar H S A) =
    H * Fintype.card S * Fintype.card A +
      (H + 1) * Fintype.card S + (H + 1) * Fintype.card S +
      H * Fintype.card S + H * Fintype.card S * Fintype.card A * Fintype.card S := by
  sorry

end

section
open Set Paper36.Regularity Paper36.Nested
variable {H : ℕ} {S A : Type*} [Fintype S] [Fintype A]

open Paper36.Complexity

/-- Complete declaration of `Paper36.Complexity.planning_constraint_count`; source support: S6.Thmtheorem2. -/
theorem planning_constraint_count : Fintype.card (PlanningConstraint H S A) =
    H * Fintype.card S * Fintype.card A + H * Fintype.card S +
      Fintype.card S + Fintype.card S + H * Fintype.card S +
      H * Fintype.card S * Fintype.card A * Fintype.card S +
      H * Fintype.card S * Fintype.card A * Fintype.card S +
      H * Fintype.card S + 2 := by
  sorry

end

section
open Set Paper36.Regularity Paper36.Nested
variable {H : ℕ} {S A : Type*} [Fintype S] [Fintype A]

open Paper36.Complexity

/-- Complete declaration of `Paper36.Complexity.polynomialSatisfaction_iff`; source support: S6.Thmtheorem2. -/
theorem polynomialSatisfaction_iff : ∀ (r c : Fin H → S → A → ℚ) (p : S → A → S → ℚ)
    (α τ target : ℚ) (s₀ : S) (W : PlanningWitness H S A),
    polynomialSatisfaction r c p α τ target s₀ W.assignment ↔
      PlanningConditions r c p α τ target s₀ W := by
  sorry

end

section
open Set Paper36.Regularity Paper36.Nested
variable {H : ℕ} {S A : Type*} [Fintype S] [Fintype A]

open Paper36.Complexity

/-- Complete declaration of `Paper36.Complexity.one_state_piece_certificate`; source support: S6.Thmtheorem2. -/
theorem one_state_piece_certificate : ∀ {ι : Type*} [Fintype ι]
    (α : ℝ) (ha : 0 < α) (d₀ d₁ x : ι → ℝ) (τ : ℝ),
    (∑ i, twoActionRisk α (d₀ i) (d₁ i) (x i)) ≤ τ ↔
      ∃ b : ι → Bool,
        (∀ i, activePiece α (expensiveProbability (d₀ i) (d₁ i) (x i)) (b i)) ∧
        (∑ i, affineRiskPiece α (d₀ i) (d₁ i) (x i) (b i)) ≤ τ := by
  sorry

end

section
open Set Paper36.Regularity Paper36.Nested
variable {H : ℕ} {S A : Type*} [Fintype S] [Fintype A]

open Paper36.Complexity

/-- Complete declaration of `Paper36.Complexity.planning_epigraph_exact`; source support: S6.Thmtheorem2. -/
theorem planning_epigraph_exact : ∀ [Nonempty A]
    (r c : Fin H → S → A → ℚ) (p : S → A → S → ℚ)
    (α τ target : ℚ) (s₀ : S)
    (ha : 0 < (α : ℝ)) (ha1 : (α : ℝ) ≤ 1)
    (hc : ∀ h s a, (c h s a : ℝ) ∈ Icc 0 1)
    (q : Nested.Kernel S A) (hq : ∀ s a t, q s a t = (p s a t : ℝ)),
    (∃ W : PlanningWitness H S A, PlanningConditions r c p α τ target s₀ W) ↔
      ∃ π : Nested.Policy S A,
        Nested.risk (α : ℝ) (realStages c) π q H 0 s₀ ≤ (τ : ℝ) ∧
        (target : ℝ) ≤ Nested.reward (realStages r) π q H 0 s₀ := by
  sorry

end

section
open Set Paper36.Regularity Paper36.Nested
variable {H : ℕ} {S A : Type*} [Fintype S] [Fintype A]

open Paper36.Complexity

/-- Complete declaration of `Paper36.Complexity.planning_polynomial_exact`; source support: S6.Thmtheorem2. -/
theorem planning_polynomial_exact : ∀ [Nonempty A]
    (r c : Fin H → S → A → ℚ) (p : S → A → S → ℚ)
    (α τ target : ℚ) (s₀ : S)
    (ha : 0 < (α : ℝ)) (ha1 : (α : ℝ) ≤ 1)
    (hc : ∀ h s a, (c h s a : ℝ) ∈ Icc 0 1)
    (q : Nested.Kernel S A) (hq : ∀ s a t, q s a t = (p s a t : ℝ)),
    (∃ x : PlanningVar H S A → ℝ, polynomialSatisfaction r c p α τ target s₀ x) ↔
      ∃ π : Nested.Policy S A,
        Nested.risk (α : ℝ) (realStages c) π q H 0 s₀ ≤ (τ : ℝ) ∧
        (target : ℝ) ≤ Nested.reward (realStages r) π q H 0 s₀ := by
  sorry

end

section
open Set Paper36.Regularity Paper36.Nested
variable {H : ℕ} {S A : Type*} [Fintype S] [Fintype A]

open Paper36.Complexity

/-- Complete declaration of `Paper36.Complexity.rational_planning_encoding_exact`; source support: S6.Thmtheorem2. -/
theorem rational_planning_encoding_exact : ∀ [Nonempty A] (I : RationalPlanningInput S A),
    (∃ x : PlanningVar I.horizon S A → ℝ,
      polynomialSatisfaction I.reward I.cost I.transition I.tailMass I.budget I.target I.initial x) ↔
      I.Feasible := by
  sorry

end

section
open Set Paper36.Regularity Paper36.Nested
variable {H : ℕ} {S A : Type*} [Fintype S] [Fintype A]

open Paper36.Complexity

/-- Complete declaration of `Paper36.Complexity.actual_one_state_subset_sum_reduction`; source support: S6.Thmtheorem2. -/
theorem actual_one_state_subset_sum_reduction : ∀ (w : Fin H → ℕ) (B : ℕ) {α C : ℝ}
    (ha : 0 < α) (ha1 : α < 1) (hw : ∀ i, 0 < w i)
    (hC : 0 < C) (htot : C = ∑ i, (w i : ℝ)),
    (∃ π : Nested.Policy Unit Bool,
      Nested.risk α (takeSkipCost (normalizedStages w C)) π oneStateKernel H 0 () ≤ (B : ℝ)/C ∧
      (B : ℝ)/C ≤ Nested.reward (takeSkipCost (normalizedStages w C)) π oneStateKernel H 0 ()) ↔
      ∃ s : Finset (Fin H), ∑ i ∈ s, w i = B := by
  sorry

end

section
open Set Paper36.Regularity Paper36.Nested
variable {H : ℕ} {S A : Type*} [Fintype S] [Fintype A]

open Paper36.Complexity

/-- Complete declaration of `Paper36.Complexity.actual_all_skip_strictly_feasible`; source support: S6.Thmtheorem2. -/
theorem actual_all_skip_strictly_feasible : ∀ (w : Fin H → ℕ) (B : ℕ) {α C : ℝ}
    (ha : 0 < α) (ha1 : α ≤ 1) (hB : 0 < B)
    (hC : 0 < C) (htot : C = ∑ i, (w i : ℝ)),
    Nested.risk α (takeSkipCost (normalizedStages w C))
      (bernoulliPolicy (fun _ : Fin H => 0) (fun _ => le_rfl) (fun _ => zero_le_one))
      oneStateKernel H 0 () < (B : ℝ)/C := by
  sorry

end

section
open Set Paper36.Regularity Paper36.Nested
variable {H : ℕ} {S A : Type*} [Fintype S] [Fintype A]

open Paper36.Complexity

/-- Complete declaration of `Paper36.Complexity.one_state_two_action_reward_sum`; source support: S6.Thmtheorem2. -/
theorem one_state_two_action_reward_sum : ∀ (r₀ r₁ : ℕ → ℝ)
    (π : Nested.Policy Unit Bool) (n h : ℕ),
    Nested.reward (twoActionCost r₀ r₁) π oneStateKernel n h () =
      ∑ i ∈ Finset.range n, (r₀ (h+i)+(r₁ (h+i)-r₀ (h+i))*π (h+i) () true) := by
  sorry

end

section
open Set Paper36.Regularity Paper36.Nested
variable {H : ℕ} {S A : Type*} [Fintype S] [Fintype A]

open Paper36.Complexity

/-- Complete declaration of `Paper36.Complexity.one_state_piece_planning_exact`; source support: S6.Thmtheorem2. -/
theorem one_state_piece_planning_exact : ∀ (α τ target : ℚ) (c₀ c₁ r₀ r₁ : Fin H → ℚ)
    (ha : 0 < (α : ℝ)) (ha1 : (α : ℝ) ≤ 1)
    (hc₀ : ∀ h, (c₀ h : ℝ) ∈ Icc 0 1) (hc₁ : ∀ h, (c₁ h : ℝ) ∈ Icc 0 1),
    (∃ π : Nested.Policy Unit Bool,
      Nested.risk (α : ℝ) (twoActionCost (finiteScalar c₀) (finiteScalar c₁)) π oneStateKernel H 0 () ≤ (τ : ℝ) ∧
      (target : ℝ) ≤ Nested.reward (twoActionCost (finiteScalar r₀) (finiteScalar r₁)) π oneStateKernel H 0 ()) ↔
      ∃ x : Fin H → ℝ, ∃ b : Fin H → Bool, OneStatePieceConditions α τ target c₀ c₁ r₀ r₁ x b := by
  sorry

end

section
open Set Paper36.Regularity Paper36.Nested
variable {H : ℕ} {S A : Type*} [Fintype S] [Fintype A]

open Paper36.Complexity

/-- Complete declaration of `Paper36.Complexity.one_state_linear_system_iff`; source support: S6.Thmtheorem2. -/
theorem one_state_linear_system_iff : ∀ (α τ target : ℚ) (c₀ c₁ r₀ r₁ : Fin H → ℚ)
    (b : Fin H → Bool) (x : Fin H → ℝ),
    oneStateLinearSystem α τ target c₀ c₁ r₀ r₁ b x ↔
      OneStatePieceConditions α τ target c₀ c₁ r₀ r₁ x b := by
  sorry

end

section
open Set Paper36.Regularity Paper36.Nested
variable {H : ℕ} {S A : Type*} [Fintype S] [Fintype A]

open Paper36.Complexity

/-- Complete declaration of `Paper36.Complexity.one_state_LP_certificate_exact`; source support: S6.Thmtheorem2. -/
theorem one_state_LP_certificate_exact : ∀ (α τ target : ℚ) (c₀ c₁ r₀ r₁ : Fin H → ℚ)
    (ha : 0 < (α : ℝ)) (ha1 : (α : ℝ) ≤ 1)
    (hc₀ : ∀ h, (c₀ h : ℝ) ∈ Icc 0 1) (hc₁ : ∀ h, (c₁ h : ℝ) ∈ Icc 0 1),
    (∃ π : Nested.Policy Unit Bool,
      Nested.risk (α : ℝ) (twoActionCost (finiteScalar c₀) (finiteScalar c₁)) π oneStateKernel H 0 () ≤ (τ : ℝ) ∧
      (target : ℝ) ≤ Nested.reward (twoActionCost (finiteScalar r₀) (finiteScalar r₁)) π oneStateKernel H 0 ()) ↔
      ∃ b : Fin H → Bool, ∃ x : Fin H → ℝ, oneStateLinearSystem α τ target c₀ c₁ r₀ r₁ b x := by
  sorry

end

section
open Set Paper36.Regularity Paper36.Nested
variable {H : ℕ} {S A : Type*} [Fintype S] [Fintype A]

open Paper36.Complexity

/-- Complete declaration of `Paper36.Complexity.one_state_linear_atom_count`; source support: S6.Thmtheorem2. -/
theorem one_state_linear_atom_count : Fintype.card (OneStateLinearAtom H) = 3*H+2 := by
  sorry

end

section
open Set Paper36.Regularity Paper36.Nested
variable {H : ℕ} {S A : Type*} [Fintype S] [Fintype A]

open Paper36.Complexity

/-- Complete declaration of `Paper36.Complexity.one_state_piece_choice_count`; source support: S6.Thmtheorem2. -/
theorem one_state_piece_choice_count : Fintype.card (Fin H → Bool) = 2^H := by
  sorry

end

section
open Set Paper36.Regularity Paper36.Nested
variable {H : ℕ} {S A : Type*} [Fintype S] [Fintype A]

open Paper36.Complexity

/-- Complete declaration of `Paper36.Complexity.paddedSubsetSumInput_feasible_iff`; source support: S6.Thmtheorem2. -/
theorem paddedSubsetSumInput_feasible_iff : ∀ (w : Fin H → ℕ) (B : ℕ) (α : ℚ)
    (ha : 0 < α) (ha1 : α < 1) (hw : ∀ i, 0 < w i),
    (paddedSubsetSumInput w B α ha ha1).Feasible ↔
      ∃ s : Finset (Fin H), ∑ i ∈ s, w i = B := by
  sorry

end

section
open Set Paper36.Regularity Paper36.Nested
variable {H : ℕ} {S A : Type*} [Fintype S] [Fintype A]

open Paper36.Complexity

/-- Complete declaration of `Paper36.Complexity.padded_input_size_bound`; source support: S6.Thmtheorem2. -/
theorem padded_input_size_bound : ∀ (w : Fin H → ℕ) (B : ℕ),
    subsetInputBits (paddedWeights w B) B ≤ 2*subsetInputBits w B+3 := by
  sorry

end

section
open Set Paper36.Regularity Paper36.Nested
variable {H : ℕ} {S A : Type*} [Fintype S] [Fintype A]

open Paper36.Complexity

/-- Complete declaration of `Paper36.Complexity.padded_reduction_payload_bound`; source support: S6.Thmtheorem2. -/
theorem padded_reduction_payload_bound : ∀ (w : Fin H → ℕ) (B : ℕ),
    (∑ i, 4*fractionPayloadBits (paddedWeights w B i) (∑ j, paddedWeights w B j))+
      2*fractionPayloadBits B (∑ j, paddedWeights w B j) ≤
      12*(2*subsetInputBits w B+4)^2 := by
  sorry

end

end P36Contract.Complexity

namespace P36Contract.Tightening

section

open Paper36.Tightening

/-- Complete declaration of `Paper36.Tightening.every_action_law`; source support: S3.Thmtheorem1. -/
theorem every_action_law : ∀ (q : Action → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hs : ∑ a : Action, q a = 1),
    ∃ p : Policy, p.prob = q := by
  sorry

end

section

open Paper36.Tightening

/-- Complete declaration of `Paper36.Tightening.risk_action_law`; source support: S3.Thmtheorem1. -/
theorem risk_action_law : ∀ (α t : ℝ) (p : Policy),
    risk α t p = sInf (Set.range (fun z : ℝ =>
      z + (∑ a : Action, p.prob a * max (cost t a - z) 0) / α)) := by
  sorry

end

section

open Paper36.Tightening

/-- Complete declaration of `Paper36.Tightening.proposition_3_1`; source support: S3.Thmtheorem1. -/
theorem proposition_3_1 : ∀ (α : ℝ) (hα : 0 < α) (hα1 : α < 1),
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      IsLeast (Set.range (risk α t)) 0 ∧
      risk α t pureSafe < t ∧ t < risk α t pureBad ∧
      t - sInf (Set.range (risk α t)) = t ∧
      primalValue α t t = 1 ∧
      (∀ b : ℝ, 0 < b → b < t →
        primalValue α t b = α*b/t ∧ dualValue α t b = b/t ∧
          primalValue α t b < dualValue α t b) ∧
      Tendsto (fun b : ℝ => primalValue α t t - primalValue α t b)
        (𝓝[<] t) (𝓝 (1-α)) := by
  sorry

end

section

open Paper36.Tightening

/-- Complete declaration of `Paper36.Tightening.linear_regret`; source support: S3.Thmtheorem2. -/
theorem linear_regret : ∀ (α t : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (ht : 0 < t)
    (K : ℕ) (ε : Fin K → ℝ) (p : Fin K → Policy)
    (hε : ∀ k, 0 < ε k ∧ ε k < t)
    (hp : ∀ k, risk α t (p k) ≤ t-ε k),
    (1-α)*(K : ℝ) ≤ ∑ k : Fin K, (primalValue α t t - value (p k)) := by
  sorry

end

end P36Contract.Tightening

namespace P36Contract.CVaR

section
variable {Ω : Type*} [Fintype Ω]
variable {A : Type*} [Fintype A]

open Paper36.CVaR

/-- Complete declaration of `Paper36.CVaR.value_eq_primal_inf`; source support: A3.Thmtheorem1. -/
theorem value_eq_primal_inf : ∀ (P : Law Ω) {α : ℝ} (ha : 0 < α) (ha1 : α ≤ 1)
    (X : Ω → ℝ),
    value P α X = sInf (Set.range (primal P α X)) := by
  sorry

end

section
variable {Ω : Type*} [Fintype Ω]
variable {A : Type*} [Fintype A]

open Paper36.CVaR

/-- Complete declaration of `Paper36.CVaR.value_eq_density_sup`; source support: S5.Thmtheorem3. -/
theorem value_eq_density_sup : ∀ (P : Law Ω) {α : ℝ} (ha : 0 < α) (X : Ω → ℝ),
    value P α X = sSup ((fun ξ => expect P.mass (fun i => ξ i*X i)) ''
      {ξ | DensityEnvelope P α ξ}) := by
  sorry

end

section
variable {Ω : Type*} [Fintype Ω]
variable {A : Type*} [Fintype A]

open Paper36.CVaR

/-- Complete declaration of `Paper36.CVaR.value_lipschitz`; source support: A3.Thmtheorem1. -/
theorem value_lipschitz : ∀ (P : Law Ω) {α : ℝ} (ha : 0 < α) (ha1 : α ≤ 1)
    {X Y : Ω → ℝ} {d : ℝ} (h : ∀ i, |X i - Y i| ≤ d),
    |value P α X - value P α Y| ≤ d := by
  sorry

end

section
variable {Ω : Type*} [Fintype Ω]
variable {A : Type*} [Fintype A]

open Paper36.CVaR

/-- Complete declaration of `Paper36.CVaR.value_tv`; source support: A3.Thmtheorem1. -/
theorem value_tv : ∀ (P Q : Law Ω) {α : ℝ} (ha : 0 < α) (ha1 : α ≤ 1)
    {X : Ω → ℝ} {l u : ℝ} (hlu : l ≤ u)
    (hl : ∀ i, l ≤ X i) (hu : ∀ i, X i ≤ u),
    |value P α X - value Q α X| ≤ ((u-l)/α) * tv P Q := by
  sorry

end

section
variable {Ω : Type*} [Fintype Ω]
variable {A : Type*} [Fintype A]

open Paper36.CVaR

/-- Complete declaration of `Paper36.CVaR.value_joint_tv`; source support: A3.Thmtheorem1. -/
theorem value_joint_tv : ∀ (π : Law A) (P Q : A → Law Ω) {α R : ℝ}
    (ha : 0 < α) (ha1 : α ≤ 1) (hR : 0 ≤ R) (c : A → ℝ) (f : Ω → ℝ)
    (hf0 : ∀ i, 0 ≤ f i) (hfR : ∀ i, f i ≤ R),
    |value (joint π P) α (fun x => c x.1 + f x.2) -
     value (joint π Q) α (fun x => c x.1 + f x.2)| ≤
      (R/α) * ∑ a, π.mass a * tv (P a) (Q a) := by
  sorry

end

section
variable {Ω : Type*} [Fintype Ω]
variable {A : Type*} [Fintype A]

open Paper36.CVaR

/-- Complete declaration of `Paper36.CVaR.value_hellinger`; source support: S5.Thmtheorem1. -/
theorem value_hellinger : ∀ (P Q : Law Ω) {α : ℝ} (ha : 0 < α) (ha1 : α ≤ 1)
    {X : Ω → ℝ} {l u : ℝ} (hlu : l ≤ u)
    (hl : ∀ i, l ≤ X i) (hu : ∀ i, X i ≤ u),
    |value P α X-value Q α X| ≤
      (2*Real.sqrt 2*(u-l)/Real.sqrt α)*hellinger P Q := by
  sorry

end

section
variable {Ω : Type*} [Fintype Ω]
variable {A : Type*} [Fintype A]

open Paper36.CVaR

/-- Complete declaration of `Paper36.CVaR.hellingerSq_joint`; source support: S5.Thmtheorem2. -/
theorem hellingerSq_joint : ∀ (π : Law A) (P Q : A → Law Ω),
    hellingerSq (joint π P) (joint π Q) = ∑ a, π.mass a * hellingerSq (P a) (Q a) := by
  sorry

end

section
variable {Ω : Type*} [Fintype Ω]
variable {A : Type*} [Fintype A]

open Paper36.CVaR

/-- Complete declaration of `Paper36.CVaR.value_joint_hybrid`; source support: S5.Thmtheorem2. -/
theorem value_joint_hybrid : ∀ [DecidableEq A] (π : Law A) (P Q : A → Law Ω) {α R : ℝ}
    (ha : 0 < α) (ha1 : α ≤ 1) (hR : 0 ≤ R)
    (c : A → ℝ) (f : Ω → ℝ) (hc0 : ∀ a, 0 ≤ c a) (hc1 : ∀ a, c a ≤ 1)
    (hf0 : ∀ i, 0 ≤ f i) (hfR : ∀ i, f i ≤ R) (I : Finset A),
    |value (joint π P) α (fun x => c x.1+f x.2)-
      value (joint π Q) α (fun x => c x.1+f x.2)| ≤
      (R/α)*(∑ a, if a ∈ I then 0 else π.mass a*tv (P a) (Q a)) +
      (2*Real.sqrt 2*(R+1)/Real.sqrt α)*
        Real.sqrt (∑ a, if a ∈ I then π.mass a*hellingerSq (P a) (Q a) else 0) := by
  sorry

end

section
variable {Ω : Type*} [Fintype Ω]
variable {A : Type*} [Fintype A]

open Paper36.CVaR

/-- Complete declaration of `Paper36.CVaR.value_indicator`; source support: A6.Thmtheorem1, S7.Thmtheorem1. -/
theorem value_indicator : ∀ (P : Law Ω) {α d : ℝ} (ha : 0 < α) (ha1 : α ≤ 1)
    (hd : 0 ≤ d) (e : Ω → Prop) [DecidablePred e],
    value P α (fun i => if e i then d else 0) =
      d * min ((∑ i, if e i then P.mass i else 0)/α) 1 := by
  sorry

end

section
variable {Ω : Type*} [Fintype Ω]
variable {A : Type*} [Fintype A]

open Paper36.CVaR

/-- Complete declaration of `Paper36.CVaR.envelope_joint`; source support: S5.Thmtheorem3. -/
theorem envelope_joint : ∀ (π : Law A) (P : A → Law Ω) {α : ℝ}
    (w : A → Ω → ℝ) (hw : ∀ a, Envelope (P a) α (w a)),
    Envelope (joint π P) α (fun x => π.mass x.1 * w x.1 x.2) := by
  sorry

end

section
variable {Ω : Type*} [Fintype Ω]
variable {A : Type*} [Fintype A]

open Paper36.CVaR

/-- Complete declaration of `Paper36.CVaR.value_joint_ge_of_forall`; source support: S4.Thmtheorem1. -/
theorem value_joint_ge_of_forall : ∀ (π : Law A) (P : A → Law Ω) {α : ℝ}
    (ha : 0 < α) (ha1 : α ≤ 1) (X : A × Ω → ℝ) {l : ℝ}
    (hl : ∀ a, l ≤ value (P a) α (fun s => X (a,s))),
    l ≤ value (joint π P) α X := by
  sorry

end

end P36Contract.CVaR

namespace P36Contract.Regularity

section
variable {Ω : Type*} [Fintype Ω]

open Paper36.Regularity

/-- Complete declaration of `Paper36.Regularity.compactCVaR_eq_primalCVaR`; source support: S2.Thmtheorem1. -/
theorem compactCVaR_eq_primalCVaR : ∀ (α B : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hB : 0 ≤ B) (P : Law Ω) (X : Ω → ℝ) (hX : ∀ i, X i ∈ Icc 0 B),
    compactCVaR α B P X = primalCVaR α P X := by
  sorry

end

section
variable {Ω : Type*} [Fintype Ω]

open Paper36.Regularity

/-- Complete declaration of `Paper36.Regularity.continuous_compactCVaR`; source support: S2.Thmtheorem1. -/
theorem continuous_compactCVaR : ∀ (α B : ℝ),
    Continuous (fun p : Law Ω × (Ω → ℝ) => compactCVaR α B p.1 p.2) := by
  sorry

end

section
variable {Ω : Type*} [Fintype Ω]

open Paper36.Regularity

/-- Complete declaration of `Paper36.Regularity.automatic_uniform_margin`; source support: S2.Thmtheorem1. -/
theorem automatic_uniform_margin : ∀ {Q : Type*} [TopologicalSpace Q]
    (support : Set Q) (hcompact : IsCompact support) (hne : support.Nonempty)
    (g : Q → ℝ) (hg : ContinuousOn g support) (τ : ℝ)
    (hstrict : ∀ q ∈ support, g q < τ),
    0 < τ - sSup (g '' support) ∧
      ∀ q ∈ support, τ - sSup (g '' support) ≤ τ - g q := by
  sorry

end

end P36Contract.Regularity

namespace P36Contract.Target

section

open Paper36.Target

/-- Complete declaration of `Paper36.Target.lemma_5_9`; source support: S5.Thmtheorem9. -/
theorem lemma_5_9 : ∀ {s a h w δ : ℝ} (hs : 1 ≤ s) (ha : 1 ≤ a) (hh : 1 ≤ h)
    (hw : 0 ≤ w) (hδ : 0 < δ) (k : ℕ) (hk : 1 ≤ k) (j n : ℕ),
    (confidence (scale w s a) s a h k * Real.sqrt (k : ℝ) ≤
      target (scale w s a) (A0 s a h) (nu s) (M0 h) k) ∧
    (target (scale w s a) (A0 s a h) (nu s) (M0 h) (j + n) ≤
      target (scale w s a) (A0 s a h) (nu s) (M0 h) j +
      target (scale w s a) (A0 s a h) (nu s) (M0 h) n) ∧
    (sSup (Set.range (fun m : ℕ => max
      (target (scale w s a) (A0 s a h) (nu s) (M0 h) m - (m : ℝ) * δ) 0)) ≤
      residual (scale w s a) (A0 s a h) (nu s) (M0 h) δ) := by
  sorry

end

section

open Paper36.Target

/-- Complete declaration of `Paper36.Target.target_sublinear`; source support: S4.Thmtheorem2. -/
theorem target_sublinear : ∀ {c A ν M : ℝ} (hc : 0 ≤ c) (hA : 0 < A)
    (hM : 0 < M) (hν : 0 ≤ ν),
    Filter.Tendsto (fun n : ℕ => target c A ν M n / (n : ℝ)) Filter.atTop (nhds 0) := by
  sorry

end

section

open Paper36.Target

/-- Complete declaration of `Paper36.Target.target_monotone`; source support: S5.Thmtheorem9. -/
theorem target_monotone : ∀ {c A ν M : ℝ} (hc : 0 ≤ c) (hA : 0 ≤ A)
    (hν : 0 ≤ ν) (hM : 0 ≤ M),
    Monotone (target c A ν M) := by
  sorry

end

end P36Contract.Target

namespace P36Contract.Nested

section
open Paper36.Regularity
variable {S A : Type*} [Fintype S] [Fintype A]

open Paper36.Nested

/-- Complete declaration of `Paper36.Nested.risk_step_eq_primal`; source support: S2.Thmtheorem1, S4.Thmtheorem1. -/
theorem risk_step_eq_primal : ∀ (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1)
    (π : Policy S A) (q : Kernel S A) (n h : ℕ) (s : S),
    risk α c π q (n+1) h s = primalCVaR α (joint (π h s) (q s))
      (fun x => c h s x.1 + risk α c π q n (h+1) x.2) := by
  sorry

end

section
open Paper36.Regularity
variable {S A : Type*} [Fintype S] [Fintype A]

open Paper36.Nested

/-- Complete declaration of `Paper36.Nested.continuous_risk`; source support: S2.Thmtheorem1. -/
theorem continuous_risk : ∀ (α : ℝ) (c : ℕ → S → A → ℝ) (n h : ℕ) (s : S),
    Continuous (fun p : Policy S A × Kernel S A => risk α c p.1 p.2 n h s) := by
  sorry

end

section
open Paper36.Regularity
variable {S A : Type*} [Fintype S] [Fintype A]

open Paper36.Nested

/-- Complete declaration of `Paper36.Nested.uniform_margin`; source support: S2.Thmtheorem1. -/
theorem uniform_margin : ∀ [Nonempty A] (α : ℝ) (c : ℕ → S → A → ℝ)
    (n : ℕ) (s : S) (Q : Set (Kernel S A)) (hclosed : IsClosed Q) (hne : Q.Nonempty)
    (τ : ℝ) (hstrict : ∀ q ∈ Q, minimumRisk α c n 0 s q < τ),
    0 < τ - sSup (minimumRisk α c n 0 s '' Q) ∧
      ∀ q ∈ Q, τ - sSup (minimumRisk α c n 0 s '' Q) ≤ τ - minimumRisk α c n 0 s q := by
  sorry

end

section
open Paper36.Regularity
variable {S A : Type*} [Fintype S] [Fintype A]

open Paper36.Nested

/-- Complete declaration of `Paper36.Nested.exists_constrained_optimum`; source support: S4.Thmtheorem2. -/
theorem exists_constrained_optimum : ∀ (α : ℝ) (c r : ℕ → S → A → ℝ)
    (n h : ℕ) (s : S) (q : Kernel S A) (τ : ℝ)
    (hne : ∃ π : Policy S A, risk α c π q n h s ≤ τ),
    ∃ π : Policy S A, risk α c π q n h s ≤ τ ∧
      ∀ π', risk α c π' q n h s ≤ τ → reward r π' q n h s ≤ reward r π q n h s := by
  sorry

end

end P36Contract.Nested

namespace P36Contract.Calibration

section
open Paper36.Regularity Paper36.Nested
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]

open Paper36.Calibration

/-- Complete declaration of `Paper36.Calibration.dp_le_risk`; source support: S4.Thmtheorem1. -/
theorem dp_le_risk : ∀ (α : ℝ) (hα : 0 ≤ α) (c : ℕ → S → A → ℝ)
    (q : Kernel S A) (π : Policy S A) (n h : ℕ) (s : S),
    dp α c q n h s ≤ risk α c π q n h s := by
  sorry

end

section
open Paper36.Regularity Paper36.Nested
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]

open Paper36.Calibration

/-- Complete declaration of `Paper36.Calibration.exists_deterministic_minimizer`; source support: S4.Thmtheorem1. -/
theorem exists_deterministic_minimizer : ∀ (α : ℝ) (c : ℕ → S → A → ℝ)
    (q : Kernel S A) (n h : ℕ),
    ∃ π : Policy S A, Deterministic π ∧ ∀ s, risk α c π q n h s = dp α c q n h s := by
  sorry

end

section
open Paper36.Regularity Paper36.Nested
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]

open Paper36.Calibration

/-- Complete declaration of `Paper36.Calibration.minimumRisk_eq_dp`; source support: S4.Thmtheorem1. -/
theorem minimumRisk_eq_dp : ∀ (α : ℝ) (hα : 0 ≤ α) (c : ℕ → S → A → ℝ)
    (q : Kernel S A) (n h : ℕ) (s : S),
    minimumRisk α c n h s q = dp α c q n h s := by
  sorry

end

end P36Contract.Calibration

namespace P36Contract.Prior

section
open MeasureTheory Paper36.Regularity Paper36.Nested
variable {S A : Type*} [Fintype S] [Fintype A] [instNonemptyA : Nonempty A]
variable [MeasurableSpace (Kernel S A)]

open Paper36.Prior

/-- Complete declaration of `Paper36.Prior.lemma_2_1`; source support: S2.Thmtheorem1. -/
include instNonemptyA in
theorem lemma_2_1 : ∀ (μ : Measure (Kernel S A)) [IsProbabilityMeasure μ]
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (H : ℕ)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1) (s₁ : S)
    (τ : ℝ) (hstrict : ∀ q ∈ μ.support, minimumRisk α c H 0 s₁ q < τ),
    0 < τ - sSup (minimumRisk α c H 0 s₁ '' μ.support) ∧
      ∀ q ∈ μ.support, τ - sSup (minimumRisk α c H 0 s₁ '' μ.support) ≤
        τ - minimumRisk α c H 0 s₁ q := by
  sorry

end

section
open MeasureTheory Paper36.Regularity Paper36.Nested
variable {S A : Type*} [Fintype S] [Fintype A] [instNonemptyA : Nonempty A]
variable [MeasurableSpace (Kernel S A)]

open Paper36.Prior

/-- Complete declaration of `Paper36.Prior.source_risk_recursion`; source support: S2.Thmtheorem1. -/
theorem source_risk_recursion : ∀ (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1)
    (π : Policy S A) (q : Kernel S A) (n h : ℕ) (s : S),
    risk α c π q (n+1) h s = primalCVaR α (joint (π h s) (q s))
      (fun x => c h s x.1 + risk α c π q n (h+1) x.2) := by
  sorry

end

end P36Contract.Prior

namespace P36Contract.LowerBound

section

open Paper36.LowerBound

/-- Complete declaration of `Paper36.LowerBound.bound_closed`; source support: S7.Thmtheorem1. -/
theorem bound_closed : ∀ {β : ℝ} (hβ : 0 < β) (n : ℕ),
    bound β n = (1 - (1 - β)^n) / (2*β) - (n : ℝ)/4 := by
  sorry

end

section

open Paper36.LowerBound

/-- Complete declaration of `Paper36.LowerBound.exact_no_fallback_optimum`; source support: S7.Thmtheorem1. -/
theorem exact_no_fallback_optimum : ∀ {ι : Type*} [Fintype ι] (L : FailureLaw ι) (n : ℕ),
    IsLeast {v : ℝ | ∃ σ : Strategy ι, (∀ h, (σ h).safe = 0) ∧
      v = bayes L σ 0 [] n} (bound L.beta n) := by
  sorry

end

section

open Paper36.LowerBound

/-- Complete declaration of `Paper36.LowerBound.no_fallback_zero_reward`; source support: S7.Thmtheorem1. -/
theorem no_fallback_zero_reward : ∀ {ι : Type*} [Fintype ι] (L : FailureLaw ι)
    (σ : Strategy ι) (hσ : ∀ h, (σ h).safe = 0) (θ : Bool) (h : History ι) (n : ℕ),
    rewardRegret L σ θ h n = 0 := by
  sorry

end

section

open Paper36.LowerBound

/-- Complete declaration of `Paper36.LowerBound.no_fallback_tailored`; source support: S7.Thmtheorem1. -/
theorem no_fallback_tailored : ∀ {ι : Type*} [Fintype ι] (L : FailureLaw ι)
    (σ : Strategy ι) (hσ : ∀ h, (σ h).safe = 0)
    (hβ : 0 < L.beta) (hβ4 : L.beta ≤ 1/4),
    1/(32*L.beta) ≤ bayes L σ 0 [] (K0 L.beta) := by
  sorry

end

section

open Paper36.LowerBound

/-- Complete declaration of `Paper36.LowerBound.fallback_tradeoff`; source support: S7.Thmtheorem2. -/
theorem fallback_tradeoff : ∀ {ι : Type*} [Fintype ι] (L : FailureLaw ι) (σ : Strategy ι)
    (n : ℕ),
    bound L.beta n ≤ bayes L σ 0 [] n + (1/2)*bayesReward L σ [] n := by
  sorry

end

section

open Paper36.LowerBound

/-- Complete declaration of `Paper36.LowerBound.pareto_coefficients`; source support: S7.Thmtheorem2. -/
theorem pareto_coefficients : ∀ {β F G : ℝ} (hβ : 0 < β) (hβ4 : β ≤ 1/4)
    (hF : 0 ≤ F) (hG : 0 ≤ G)
    (h : 1/(32*β) ≤ G + (1/2)*F*Real.sqrt (K0 β : ℝ)),
    1/(64*β) ≤ G ∨ Real.sqrt 2/(32*Real.sqrt β) ≤ F := by
  sorry

end

section

open Paper36.LowerBound

/-- Complete declaration of `Paper36.LowerBound.exact_no_fallback_closed`; source support: S7.Thmtheorem1. -/
theorem exact_no_fallback_closed : ∀ {ι : Type*} [Fintype ι] (L : FailureLaw ι)
    (hβ : 0 < L.beta) (n : ℕ),
    IsLeast {v : ℝ | ∃ σ : Strategy ι, (∀ h, (σ h).safe = 0) ∧
      v = bayes L σ 0 [] n}
      ((1-(1-L.beta)^n)/(2*L.beta)-(n : ℝ)/4) := by
  sorry

end

section

open Paper36.LowerBound

/-- Complete declaration of `Paper36.LowerBound.fallback_pareto`; source support: S7.Thmtheorem2. -/
theorem fallback_pareto : ∀ {ι : Type*} [Fintype ι] (L : FailureLaw ι) (σ : Strategy ι)
    (hβ : 0 < L.beta) (hβ4 : L.beta ≤ 1/4) {F G : ℝ} (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hr : ∀ n, bayesReward L σ [] n ≤ F*Real.sqrt (n : ℝ))
    (hρ : ∀ n, bayes L σ 0 [] n ≤ G),
    1/(64*L.beta) ≤ G ∨ Real.sqrt 2/(32*Real.sqrt L.beta) ≤ F := by
  sorry

end

end P36Contract.LowerBound

namespace P36Contract.Assembly

section
open MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

open Paper36.Assembly

/-- Complete declaration of `Paper36.Assembly.conditional_expected_risk_bound`; source support: S4.Thmtheorem2, A2.Thmtheorem1. -/
theorem conditional_expected_risk_bound : ∀ (T : ℕ → ℝ) (d risk sampled : ℕ → Ω → ℝ)
    (ε : ℕ → ℝ) (τ Δ D R C : ℝ) (K : ℕ)
    (hd : ∀ n, Measurable (d n)) (hΔ : 0 < Δ)
    (hT : Monotone T) (hbase : 0 ≤ T 0 + τ) (hzero : T 0 = 0)
    (hsub : ∀ j n, T (j + n) ≤ T j + T n)
    (henv : ∀ n, T n - (n : ℝ) * Δ ≤ R)
    (hdeposit : ∀ᵐ ω ∂μ, DepositBounds T d Δ τ ω)
    (hrisk : ∀ n, Integrable (risk n) μ) (hsampled : ∀ n, Integrable (sampled n) μ)
    (hε : ∀ n, 0 ≤ ε n)
    (horacle : ∀ᵐ ω ∂μ, ∀ n,
      (Bank.calibrates T (fun j => d j ω) n → sampled n ω = τ - d (n + 1) ω) ∧
      (¬Bank.calibrates T (fun j => d j ω) n → sampled n ω ≤ τ + ε n))
    (hmodel : (∫ ω, total (fun n ω => risk n ω - sampled n ω) K ω ∂μ) ≤ C + D)
    (hdom : C ≤ T K),
    (∫ ω, total (fun n ω => risk n ω - τ) K ω ∂μ) ≤
      D + R + ∑ n ∈ Finset.range K, ε n := by
  sorry

end

section
open MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

open Paper36.Assembly

/-- Complete declaration of `Paper36.Assembly.conditional_expected_reward_bound`; source support: S4.Thmtheorem2, A2.Thmtheorem1. -/
theorem conditional_expected_reward_bound : ∀ (T : ℕ → ℝ)
    (d opt sampledOpt reward sampledReward : ℕ → Ω → ℝ) (ζ : ℕ → ℝ)
    (H Δ τ Q : ℝ) (K : ℕ)
    (hd : ∀ n, Measurable (d n)) (hH : 0 ≤ H) (hΔ : 0 < Δ)
    (hT : Monotone T) (hbase : 0 ≤ T 0 + τ)
    (hdeposit : ∀ᵐ ω ∂μ, DepositBounds T d Δ τ ω)
    (hopt : ∀ n, Integrable (opt n) μ) (hsopt : ∀ n, Integrable (sampledOpt n) μ)
    (hr : ∀ n, Integrable (reward n) μ) (hsr : ∀ n, Integrable (sampledReward n) μ)
    (hζ : ∀ n, 0 ≤ ζ n)
    (horacle : ∀ᵐ ω ∂μ, ∀ n,
      (Bank.calibrates T (fun j => d j ω) n → sampledOpt n ω - sampledReward n ω ≤ H) ∧
      (¬Bank.calibrates T (fun j => d j ω) n → sampledOpt n ω - sampledReward n ω ≤ ζ n))
    (hsym : (∫ ω, total (fun n ω => opt n ω - sampledOpt n ω) K ω ∂μ) = 0)
    (hmodel : (∫ ω, total (fun n ω => sampledReward n ω - reward n ω) K ω ∂μ) ≤ Q),
    (∫ ω, total (fun n ω => opt n ω - reward n ω) K ω ∂μ) ≤
      Q + H * ((T K + τ) / Δ) + ∑ n ∈ Finset.range K, ζ n := by
  sorry

end

section
open MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

open Paper36.Assembly

/-- Complete declaration of `Paper36.Assembly.total_symmetry_from_matching_expectations`; source support: S4.Thmtheorem2. -/
theorem total_symmetry_from_matching_expectations : ∀ (opt sampledOpt : ℕ → Ω → ℝ)
    (hopt : ∀ n, Integrable (opt n) μ) (hsopt : ∀ n, Integrable (sampledOpt n) μ)
    (hmatch : ∀ n, (∫ ω, opt n ω ∂μ) = (∫ ω, sampledOpt n ω ∂μ)) (K : ℕ),
    (∫ ω, total (fun n ω => opt n ω - sampledOpt n ω) K ω ∂μ) = 0 := by
  sorry

end

section
open MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

open Paper36.Assembly

/-- Complete declaration of `Paper36.Assembly.calibration_sparse_ae_actual`; source support: S4.Thmtheorem2. -/
theorem calibration_sparse_ae_actual : ∀ {s a h w Δ τ : ℝ} (d : ℕ → Ω → ℝ)
    (hs : 1 ≤ s) (ha : 1 ≤ a) (hh : 1 ≤ h) (hw : 0 ≤ w)
    (hΔ : 0 < Δ) (hτ : 0 ≤ τ)
    (hdeposit : ∀ᵐ ω ∂μ, DepositBounds (BankTarget.paperTarget s a h w) d Δ τ ω),
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun K : ℕ => countRV (BankTarget.paperTarget s a h w) d K ω / (K : ℝ))
      Filter.atTop (nhds 0) := by
  sorry

end

section
open MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

open Paper36.Assembly

/-- Complete declaration of `Paper36.Assembly.conditional_main_bounds`; source support: S4.Thmtheorem2, A2.Thmtheorem1. -/
theorem conditional_main_bounds : ∀ {s a h w Δ τ D Q : ℝ}
    (d risk sampledRisk opt sampledOpt reward sampledReward : ℕ → Ω → ℝ)
    (ε ζ : ℕ → ℝ) (K : ℕ) (hk : 1 ≤ K)
    (hs : 1 ≤ s) (ha : 1 ≤ a) (hh : 1 ≤ h) (hw : 0 ≤ w)
    (hΔ : 0 < Δ) (hτ : 0 ≤ τ) (hd : ∀ n, Measurable (d n))
    (hdeposit : ∀ᵐ ω ∂μ, DepositBounds (BankTarget.paperTarget s a h w) d Δ τ ω)
    (hrisk : ∀ n, Integrable (risk n) μ) (hsrisk : ∀ n, Integrable (sampledRisk n) μ)
    (hopt : ∀ n, Integrable (opt n) μ) (hsopt : ∀ n, Integrable (sampledOpt n) μ)
    (hr : ∀ n, Integrable (reward n) μ) (hsr : ∀ n, Integrable (sampledReward n) μ)
    (hε : ∀ n, 0 ≤ ε n) (hζ : ∀ n, 0 ≤ ζ n)
    (hriskOracle : ∀ᵐ ω ∂μ, ∀ n,
      (Bank.calibrates (BankTarget.paperTarget s a h w) (fun j => d j ω) n →
        sampledRisk n ω = τ - d (n + 1) ω) ∧
      (¬Bank.calibrates (BankTarget.paperTarget s a h w) (fun j => d j ω) n →
        sampledRisk n ω ≤ τ + ε n))
    (hrewardOracle : ∀ᵐ ω ∂μ, ∀ n,
      (Bank.calibrates (BankTarget.paperTarget s a h w) (fun j => d j ω) n →
        sampledOpt n ω - sampledReward n ω ≤ h) ∧
      (¬Bank.calibrates (BankTarget.paperTarget s a h w) (fun j => d j ω) n →
        sampledOpt n ω - sampledReward n ω ≤ ζ n))
    (hmodelRisk : (∫ ω, total (fun n ω => risk n ω - sampledRisk n ω) K ω ∂μ) ≤
      Target.confidence (Target.scale w s a) s a h K * Real.sqrt (K : ℝ) + D)
    (hmodelReward : (∫ ω, total (fun n ω => sampledReward n ω - reward n ω) K ω ∂μ) ≤ Q)
    (hsym : (∫ ω, total (fun n ω => opt n ω - sampledOpt n ω) K ω ∂μ) = 0),
    ((∫ ω, total (fun n ω => risk n ω - τ) K ω ∂μ) ≤
      D + BankTarget.paperResidual s a h w Δ + ∑ n ∈ Finset.range K, ε n) ∧
    ((∫ ω, total (fun n ω => opt n ω - reward n ω) K ω ∂μ) ≤
      Q + h * ((BankTarget.paperTarget s a h w K + τ) / Δ) +
        ∑ n ∈ Finset.range K, ζ n) ∧
    ((∫ ω, countRV (BankTarget.paperTarget s a h w) d K ω ∂μ) ≤
      min (K : ℝ) ((BankTarget.paperTarget s a h w K + τ) / Δ)) := by
  sorry

end

end P36Contract.Assembly

namespace P36Contract.Posterior

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ]
variable {History Model : Type*} [MeasurableSpace History] [MeasurableSpace Model]
  [StandardBorelSpace Model] [Nonempty Model]
  {history : Ω → History} {latent sampled : Ω → Model}

open Paper36.Posterior

/-- Complete declaration of `Paper36.Posterior.predictable_to_realized`; source support: A3.Thmtheorem3. -/
theorem predictable_to_realized : ∀ (ℱ : Filtration ℕ m0) (Z : ℕ → Ω → ℝ) (K : ℕ)
    {b ell : ℝ} (hb : 0 ≤ b) (hell : 0 < ell)
    (hZ : ∀ k < K, StronglyMeasurable[ℱ (k + 1)] (Z k))
    (hbound : ∀ k < K, ∀ᵐ ω ∂μ, 0 ≤ Z k ω ∧ Z k ω ≤ b),
    μ.real {ω | 2 * (∑ k ∈ Finset.range K, Z k ω) + 2 * b * ell <
      ∑ k ∈ Finset.range K, predictableMean (μ := μ) ℱ Z k ω} ≤ Real.exp (-ell) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ]
variable {History Model : Type*} [MeasurableSpace History] [MeasurableSpace Model]
  [StandardBorelSpace Model] [Nonempty Model]
  {history : Ω → History} {latent sampled : Ω → Model}

open Paper36.Posterior

/-- Complete declaration of `Paper36.Posterior.posterior_joint_identDistrib`; source support: S5.Thmtheorem5. -/
theorem posterior_joint_identDistrib : ∀ (hh : AEMeasurable history μ)
    (hl : AEMeasurable latent μ) (hs : AEMeasurable sampled μ)
    (hposterior : condDistrib latent history μ =ᵐ[μ.map history]
      condDistrib sampled history μ),
    IdentDistrib (fun ω => (history ω, latent ω)) (fun ω => (history ω, sampled ω)) μ μ := by
  sorry

end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ]
variable {History Model : Type*} [MeasurableSpace History] [MeasurableSpace Model]
  [StandardBorelSpace Model] [Nonempty Model]
  {history : Ω → History} {latent sampled : Ω → Model}

open Paper36.Posterior

/-- Complete declaration of `Paper36.Posterior.posterior_conditional_expectation`; source support: S5.Thmtheorem5. -/
theorem posterior_conditional_expectation : ∀ (hh : Measurable history)
    (hl : AEMeasurable latent μ) (hs : AEMeasurable sampled μ)
    (hposterior : condDistrib latent history μ =ᵐ[μ.map history]
      condDistrib sampled history μ)
    {f : History × Model → ℝ} (hf : StronglyMeasurable f)
    (hfl : Integrable (fun ω => f (history ω, latent ω)) μ)
    (hfs : Integrable (fun ω => f (history ω, sampled ω)) μ),
    μ[fun ω => f (history ω, sampled ω) | MeasurableSpace.comap history inferInstance] =ᵐ[μ]
      μ[fun ω => f (history ω, latent ω) | MeasurableSpace.comap history inferInstance] := by
  sorry

end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ]
variable {History Model : Type*} [MeasurableSpace History] [MeasurableSpace Model]
  [StandardBorelSpace Model] [Nonempty Model]
  {history : Ω → History} {latent sampled : Ω → Model}

open Paper36.Posterior

/-- Complete declaration of `Paper36.Posterior.posterior_failure_probability`; source support: S5.Thmtheorem5. -/
theorem posterior_failure_probability : ∀ (hh : AEMeasurable history μ)
    (hl : AEMeasurable latent μ) (hs : AEMeasurable sampled μ)
    (hposterior : condDistrib latent history μ =ᵐ[μ.map history]
      condDistrib sampled history μ)
    {C : Set (History × Model)} (hC : MeasurableSet C),
    μ {ω | (history ω, sampled ω) ∉ C} = μ {ω | (history ω, latent ω) ∉ C} := by
  sorry

end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ]
variable {History Model : Type*} [MeasurableSpace History] [MeasurableSpace Model]
  [StandardBorelSpace Model] [Nonempty Model]
  {history : Ω → History} {latent sampled : Ω → Model}

open Paper36.Posterior

/-- Complete declaration of `Paper36.Posterior.posterior_expectation_eq`; source support: S5.Thmtheorem8. -/
theorem posterior_expectation_eq : ∀ (hh : AEMeasurable history μ)
    (hl : AEMeasurable latent μ) (hs : AEMeasurable sampled μ)
    (hposterior : condDistrib latent history μ =ᵐ[μ.map history]
      condDistrib sampled history μ)
    {f : History × Model → ℝ} (hf : Measurable f),
    (∫ ω, f (history ω, latent ω) ∂μ) = ∫ ω, f (history ω, sampled ω) ∂μ := by
  sorry

end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ]
variable {History Model : Type*} [MeasurableSpace History] [MeasurableSpace Model]
  [StandardBorelSpace Model] [Nonempty Model]
  {history : Ω → History} {latent sampled : Ω → Model}

open Paper36.Posterior

/-- Complete declaration of `Paper36.Posterior.weighted_conditional_expectation`; source support: S5.Thmtheorem5. -/
theorem weighted_conditional_expectation : ∀ {m : MeasurableSpace Ω} (hm : m ≤ m0)
    {count weight : Ω → ℝ} (hw : StronglyMeasurable[m] weight)
    (hc : Integrable count μ) (hwc : Integrable (weight * count) μ),
    (∫ ω, weight ω * (μ[count|m]) ω ∂μ) = ∫ ω, weight ω * count ω ∂μ := by
  sorry

end

end P36Contract.Posterior

namespace P36Contract.CalibrationScan

section
open Paper36.Regularity Paper36.Nested

open Paper36.CalibrationScan

/-- Complete declaration of `Paper36.CalibrationScan.scan_feasible`; source support: S4.Thmtheorem1. -/
theorem scan_feasible : ∀ (n : ℕ) (cap loss : Fin n → ℝ) (r : ℝ)
    (hc : ∀ i, 0 ≤ cap i) (hr : 0 ≤ r) (ht : r ≤ ∑ i, cap i),
    (∀ i, 0 ≤ (scan n cap loss r).weights i ∧ (scan n cap loss r).weights i ≤ cap i) ∧
      (∑ i, (scan n cap loss r).weights i) = r ∧
      (scan n cap loss r).payoff = ∑ i, (scan n cap loss r).weights i * loss i := by
  sorry

end

section
open Paper36.Regularity Paper36.Nested

open Paper36.CalibrationScan

/-- Complete declaration of `Paper36.CalibrationScan.scan_primal_certificate`; source support: S4.Thmtheorem1. -/
theorem scan_primal_certificate : ∀ (n : ℕ) (cap loss : Fin n → ℝ) (r : ℝ)
    (hc : ∀ i, 0 ≤ cap i) (hr : 0 ≤ r) (ht : r ≤ ∑ i, cap i) (hsort : Antitone loss),
    (scan n cap loss r).payoff = r * (scan n cap loss r).threshold +
      ∑ i, cap i * max (loss i - (scan n cap loss r).threshold) 0 := by
  sorry

end

section
open Paper36.Regularity Paper36.Nested

open Paper36.CalibrationScan

/-- Complete declaration of `Paper36.CalibrationScan.rowScan_eq_value`; source support: S4.Thmtheorem1. -/
theorem rowScan_eq_value : ∀ (P : CVaR.Law (Fin n)) {α : ℝ} (ha : 0 < α) (ha1 : α ≤ 1)
    (loss : Fin n → ℝ) (hsort : Antitone loss),
    (rowScan P α loss).payoff = CVaR.value P α loss := by
  sorry

end

section
open Paper36.Regularity Paper36.Nested

open Paper36.CalibrationScan

/-- Complete declaration of `Paper36.CalibrationScan.rowScan_cost`; source support: S4.Thmtheorem1. -/
theorem rowScan_cost : ∀ (P : CVaR.Law (Fin n)) (α : ℝ) (loss : Fin n → ℝ),
    (rowScan P α loss).operations ≤ 5*n := by
  sorry

end

section
open Paper36.Regularity Paper36.Nested

open Paper36.CalibrationScan

/-- Complete declaration of `Paper36.CalibrationScan.evaluateDP_eq_minimumRisk`; source support: S4.Thmtheorem1. -/
theorem evaluateDP_eq_minimumRisk : ∀ {n m : ℕ} (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (c : ℕ → Fin n → Fin (m+1) → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (q : Nested.Kernel (Fin n) (Fin (m+1)))
    (sorter : (g : Fin n → ℝ) → SortedOrder n g) (k h : ℕ) (s : Fin n),
    (evaluateDP α c q sorter k h).value s = Nested.minimumRisk α c k h s q := by
  sorry

end

section
open Paper36.Regularity Paper36.Nested

open Paper36.CalibrationScan

/-- Complete declaration of `Paper36.CalibrationScan.proposition4_1_scan`; source support: S4.Thmtheorem1. -/
theorem proposition4_1_scan : ∀ {n m : ℕ} (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (c : ℕ → Fin n → Fin (m+1) → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (q : Nested.Kernel (Fin n) (Fin (m+1)))
    (sorter : (g : Fin n → ℝ) → SortedOrder n g) (K : ℕ)
    (hsort : ∀ g, (sorter g).operations ≤ K*n*n) (H h : ℕ) (s : Fin n),
    (evaluateDP α c q sorter H h).value s = Nested.minimumRisk α c H h s q ∧
      (evaluateDP α c q sorter H h).operations ≤ H*((K+7)*(m+1)*n*n) := by
  sorry

end

section
open Paper36.Regularity Paper36.Nested

open Paper36.CalibrationScan

/-- Complete declaration of `Paper36.CalibrationScan.evaluatedPolicy_optimal`; source support: S4.Thmtheorem1. -/
theorem evaluatedPolicy_optimal : ∀ {n m : ℕ} (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (c : ℕ → Fin n → Fin (m+1) → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (q : Nested.Kernel (Fin n) (Fin (m+1)))
    (sorter : (g : Fin n → ℝ) → SortedOrder n g) (k h : ℕ) (s : Fin n),
    Nested.risk α c (evaluatedPolicy α c q sorter k h) q k h s = Calibration.dp α c q k h s := by
  sorry

end

section
open Paper36.Regularity Paper36.Nested

open Paper36.CalibrationScan

/-- Complete declaration of `Paper36.CalibrationScan.proposition4_1_actions`; source support: S4.Thmtheorem1. -/
theorem proposition4_1_actions : ∀ {n m : ℕ} (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (c : ℕ → Fin n → Fin (m+1) → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (q : Nested.Kernel (Fin n) (Fin (m+1)))
    (sorter : (g : Fin n → ℝ) → SortedOrder n g) (K : ℕ)
    (hsort : ∀ g, (sorter g).operations ≤ K*n*n) (H h : ℕ),
    Calibration.Deterministic (evaluatedPolicy α c q sorter H h) ∧
    (∀ s, Nested.risk α c (evaluatedPolicy α c q sorter H h) q H h s = Nested.minimumRisk α c H h s q) ∧
    (evaluateDP α c q sorter H h).actionTables.length = H ∧
    (evaluateDP α c q sorter H h).operations ≤ H*((K+7)*(m+1)*n*n) := by
  sorry

end

section
open Paper36.Regularity Paper36.Nested

open Paper36.CalibrationScan

/-- Complete declaration of `Paper36.CalibrationScan.evaluateDP_table_lookup`; source support: S4.Thmtheorem1. -/
theorem evaluateDP_table_lookup : ∀ {n m : ℕ} (α : ℝ) (c : ℕ → Fin n → Fin (m+1) → ℝ)
    (q : Nested.Kernel (Fin n) (Fin (m+1)))
    (sorter : (g : Fin n → ℝ) → SortedOrder n g) (k h j : ℕ) (hj : j < k) (s : Fin n),
    ((evaluateDP α c q sorter k h).actionTables[j]?).map (fun v => vectorAt v s) =
      some ((evaluateDP α c q sorter k h).actions (h+j) s) := by
  sorry

end

section
open Paper36.Regularity Paper36.Nested

open Paper36.CalibrationScan

/-- Complete declaration of `Paper36.CalibrationScan.evaluateDP_cost_budget`; source support: S4.Thmtheorem1. -/
theorem evaluateDP_cost_budget : ∀ {n m : ℕ} (α : ℝ) (c : ℕ → Fin n → Fin (m+1) → ℝ)
    (q : Nested.Kernel (Fin n) (Fin (m+1)))
    (sorter : (g : Fin n → ℝ) → SortedOrder n g) (T : ℕ)
    (hsort : ∀ g, (sorter g).operations ≤ T) (k h : ℕ),
    (evaluateDP α c q sorter k h).operations ≤ k*(T+n*(m+1)*(5*n+1)+n*m) := by
  sorry

end

end P36Contract.CalibrationScan

namespace P36Contract.Algorithm

section
open Set Paper36.Regularity Paper36.Nested
variable {S A Ω : Type*} [Fintype S] [Fintype A] [instNonemptyA : Nonempty A]

open Paper36.Algorithm

/-- Complete declaration of `Paper36.Algorithm.selected_sampled_risk`; source support: S4.Thmtheorem2. -/
theorem selected_sampled_risk : ∀ {α τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} (O : Oracles α c r H s₁ τ Q)
    (T : ℕ → ℝ) (sample : ℕ → Ω → Kernel S A) (n : ℕ) (ω : Ω)
    (hsample : sample n ω ∈ Q),
    (Bank.calibrates T (fun j => deposits α τ c H s₁ sample j ω) n →
      risk α c (selected O T sample n ω) (sample n ω) H 0 s₁ =
        τ - deposits α τ c H s₁ sample (n+1) ω) ∧
    (¬ Bank.calibrates T (fun j => deposits α τ c H s₁ sample j ω) n →
      risk α c (selected O T sample n ω) (sample n ω) H 0 s₁ ≤ τ) := by
  sorry

end

section
open Set Paper36.Regularity Paper36.Nested
variable {S A Ω : Type*} [Fintype S] [Fintype A] [instNonemptyA : Nonempty A]

open Paper36.Algorithm

/-- Complete declaration of `Paper36.Algorithm.selected_sampled_reward`; source support: S4.Thmtheorem2. -/
theorem selected_sampled_reward : ∀ {α τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} (O : Oracles α c r H s₁ τ Q)
    (hr : ∀ h s a, r h s a ∈ Icc 0 1)
    (T : ℕ → ℝ) (sample : ℕ → Ω → Kernel S A) (n : ℕ) (ω : Ω)
    (hsample : sample n ω ∈ Q),
    (Bank.calibrates T (fun j => deposits α τ c H s₁ sample j ω) n →
      constrainedValue α c r H s₁ τ (sample n ω) -
        reward r (selected O T sample n ω) (sample n ω) H 0 s₁ ≤ H) ∧
    (¬ Bank.calibrates T (fun j => deposits α τ c H s₁ sample j ω) n →
      constrainedValue α c r H s₁ τ (sample n ω) -
        reward r (selected O T sample n ω) (sample n ω) H 0 s₁ = 0) := by
  sorry

end

section
open Set Paper36.Regularity Paper36.Nested
variable {S A Ω : Type*} [Fintype S] [Fintype A] [instNonemptyA : Nonempty A]

open Paper36.Algorithm

/-- Complete declaration of `Paper36.Algorithm.actual_deposit_bounds`; source support: S4.Thmtheorem2. -/
include instNonemptyA in
theorem actual_deposit_bounds : ∀ (α τ Δ : ℝ) (hα : 0 ≤ α)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1)
    (H : ℕ) (s₁ : S) (Q : Set (Kernel S A))
    (hgap : ∀ q ∈ Q, minimumRisk α c H 0 s₁ q ≤ τ - Δ)
    (sample : ℕ → Ω → Kernel S A) (ω : Ω) (hsample : ∀ n, sample n ω ∈ Q),
    ∀ n, Δ ≤ deposits α τ c H s₁ sample (n+1) ω ∧
      deposits α τ c H s₁ sample (n+1) ω ≤ τ := by
  sorry

end

section
open Set Paper36.Regularity Paper36.Nested
variable {S A Ω : Type*} [Fintype S] [Fintype A] [instNonemptyA : Nonempty A]

open Paper36.Algorithm

/-- Complete declaration of `Paper36.Algorithm.sampled_risk_bank`; source support: S4.Thmtheorem2. -/
theorem sampled_risk_bank : ∀ {α τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} (O : Oracles α c r H s₁ τ Q)
    (T : ℕ → ℝ) (sample : ℕ → Ω → Kernel S A) (ω : Ω)
    (hsample : ∀ n, sample n ω ∈ Q) (K : ℕ),
    (∑ n ∈ Finset.range K, (risk α c (selected O T sample n ω) (sample n ω) H 0 s₁ - τ)) ≤
      -Bank.bank T (fun j => deposits α τ c H s₁ sample j ω) K := by
  sorry

end

section
open Set Paper36.Regularity Paper36.Nested
variable {S A Ω : Type*} [Fintype S] [Fintype A] [instNonemptyA : Nonempty A]

open Paper36.Algorithm

/-- Complete declaration of `Paper36.Algorithm.risk_bank_certificate_path`; source support: S5.Thmtheorem6. -/
theorem risk_bank_certificate_path : ∀ {α τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} (O : Oracles α c r H s₁ τ Q)
    (T : ℕ → ℝ) (sample : ℕ → Ω → Kernel S A) (latent : Ω → Kernel S A)
    (ω : Ω) (hsample : ∀ n, sample n ω ∈ Q) (K : ℕ) (E : ℝ)
    (hmodel : (∑ n ∈ Finset.range K,
      (risk α c (selected O T sample n ω) (latent ω) H 0 s₁ -
       risk α c (selected O T sample n ω) (sample n ω) H 0 s₁)) ≤ E),
    (∑ n ∈ Finset.range K, (risk α c (selected O T sample n ω) (latent ω) H 0 s₁ - τ)) ≤
      E - Bank.bank T (fun j => deposits α τ c H s₁ sample j ω) K := by
  sorry

end

section
open Set Paper36.Regularity Paper36.Nested
variable {S A Ω : Type*} [Fintype S] [Fintype A] [instNonemptyA : Nonempty A]

open Paper36.Algorithm

/-- Complete declaration of `Paper36.Algorithm.exists_oracles`; source support: S4.Thmtheorem2. -/
include instNonemptyA in
theorem exists_oracles : ∀ (α τ : ℝ) (hα : 0 ≤ α) (c r : ℕ → S → A → ℝ)
    (H : ℕ) (s₁ : S) (Q : Set (Kernel S A))
    (hstrict : ∀ q ∈ Q, minimumRisk α c H 0 s₁ q < τ),
    Nonempty (Oracles α c r H s₁ τ Q) := by
  sorry

end

end P36Contract.Algorithm

namespace P36Contract.Approximation

section
open Paper36.Regularity Paper36.Nested Paper36.Algorithm
variable {S A Ω : Type*} [Fintype S] [Fintype A] [Nonempty A]

open Paper36.Approximation

/-- Complete declaration of `Paper36.Approximation.sampled_bank_cancellation`; source support: A2.Thmtheorem1. -/
theorem sampled_bank_cancellation : ∀ {α τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} {ε ζ : ℕ → ℝ} (O : Oracles α c r H s₁ τ Q ε ζ)
    (hε : ∀ n, 0 ≤ ε n) (T : ℕ → ℝ) (sample : ℕ → Ω → Kernel S A)
    (ω : Ω) (hs : ∀ n, sample n ω ∈ Q) (K : ℕ),
    (∑ n ∈ Finset.range K, (risk α c (selected O T sample n ω) (sample n ω) H 0 s₁ - τ)) ≤
      (∑ n ∈ Finset.range K, ε n) -
        Bank.bank T (fun j => Algorithm.deposits α τ c H s₁ sample j ω) K := by
  sorry

end

section
open Paper36.Regularity Paper36.Nested Paper36.Algorithm
variable {S A Ω : Type*} [Fintype S] [Fintype A] [Nonempty A]

open Paper36.Approximation

/-- Complete declaration of `Paper36.Approximation.sampled_reward_total`; source support: A2.Thmtheorem1. -/
theorem sampled_reward_total : ∀ {α τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} {ε ζ : ℕ → ℝ} (O : Oracles α c r H s₁ τ Q ε ζ)
    (exact : Algorithm.Oracles α c r H s₁ τ Q) (hζ : ∀ n, 0 ≤ ζ n)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (T : ℕ → ℝ) (sample : ℕ → Ω → Kernel S A) (ω : Ω)
    (hs : ∀ n, sample n ω ∈ Q) (K : ℕ),
    (∑ n ∈ Finset.range K, (constrainedValue α c r H s₁ τ (sample n ω) -
      reward r (selected O T sample n ω) (sample n ω) H 0 s₁)) ≤
      H * (Bank.count T (fun j => Algorithm.deposits α τ c H s₁ sample j ω) K : ℝ) +
        ∑ n ∈ Finset.range K, ζ n := by
  sorry

end

end P36Contract.Approximation

namespace P36Contract.BorelAlgorithm

section
open MeasureTheory Paper36.Regularity Paper36.Nested Paper36.Algorithm
variable {S A Ω : Type*} [Fintype S] [Fintype A] [Nonempty A] [MeasurableSpace Ω]

open Paper36.BorelAlgorithm

/-- Complete declaration of `Paper36.BorelAlgorithm.measurable_selected`; source support: S4.Thmtheorem2. -/
theorem measurable_selected : ∀ {α τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} (O : BorelOracles α c r H s₁ τ Q)
    (T : ℕ → ℝ) (sample : ℕ → Ω → Kernel S A) (hsample : ∀ n, Measurable (sample n))
    (n : ℕ),
    Measurable (fun ω => selected O.toOracles T sample n ω) := by
  sorry

end

section
open MeasureTheory Paper36.Regularity Paper36.Nested Paper36.Algorithm
variable {S A Ω : Type*} [Fintype S] [Fintype A] [Nonempty A] [MeasurableSpace Ω]

open Paper36.BorelAlgorithm

/-- Complete declaration of `Paper36.BorelAlgorithm.integrable_comparator`; source support: S5.Thmtheorem8. -/
theorem integrable_comparator : ∀ (μ : Measure Ω) [IsFiniteMeasure μ]
    {α τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} (O : BorelOracles α c r H s₁ τ Q)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (p : Ω → Kernel S A) (hp : Measurable p),
    Integrable (fun ω => comparator O (p ω)) μ := by
  sorry

end

end P36Contract.BorelAlgorithm

namespace P36Contract.BankTarget

section

open Paper36.BankTarget

/-- Complete declaration of `Paper36.BankTarget.actual_target_properties`; source support: S4.Thmtheorem2. -/
theorem actual_target_properties : ∀ {s a h w Δ : ℝ}
    (hs : 1 ≤ s) (ha : 1 ≤ a) (hh : 1 ≤ h) (hw : 0 ≤ w) (hΔ : 0 < Δ),
    Monotone (paperTarget s a h w) ∧ paperTarget s a h w 0 = 0 ∧
    (∀ j n, paperTarget s a h w (j + n) ≤
      paperTarget s a h w j + paperTarget s a h w n) ∧
    (∀ n, paperTarget s a h w n - (n : ℝ) * Δ ≤ paperResidual s a h w Δ) ∧
    Filter.Tendsto (fun n : ℕ => paperTarget s a h w n / (n : ℝ))
      Filter.atTop (nhds 0) := by
  sorry

end

section

open Paper36.BankTarget

/-- Complete declaration of `Paper36.BankTarget.calibration_count`; source support: S4.Thmtheorem2. -/
theorem calibration_count : ∀ {s a h w Δ τ : ℝ} (d : ℕ → ℝ)
    (hs : 1 ≤ s) (ha : 1 ≤ a) (hh : 1 ≤ h) (hw : 0 ≤ w)
    (hΔ : 0 < Δ) (hτ : 0 ≤ τ)
    (hdeposit : ∀ n, Bank.calibrates (paperTarget s a h w) d n →
      Δ ≤ d (n + 1) ∧ d (n + 1) ≤ τ) (K : ℕ),
    (Bank.count (paperTarget s a h w) d K : ℝ) ≤
      min (K : ℝ) ((paperTarget s a h w K + τ) / Δ) := by
  sorry

end

section

open Paper36.BankTarget

/-- Complete declaration of `Paper36.BankTarget.bank_deficit`; source support: S4.Thmtheorem2. -/
theorem bank_deficit : ∀ {s a h w Δ : ℝ} (d : ℕ → ℝ)
    (hs : 1 ≤ s) (ha : 1 ≤ a) (hh : 1 ≤ h) (hw : 0 ≤ w) (hΔ : 0 < Δ)
    (hdeposit : ∀ n, Bank.calibrates (paperTarget s a h w) d n → Δ ≤ d (n + 1))
    (K : ℕ),
    paperTarget s a h w K - Bank.bank (paperTarget s a h w) d K ≤
      paperResidual s a h w Δ := by
  sorry

end

section

open Paper36.BankTarget

/-- Complete declaration of `Paper36.BankTarget.calibration_sparse`; source support: S4.Thmtheorem2. -/
theorem calibration_sparse : ∀ {s a h w Δ τ : ℝ} (d : ℕ → ℝ)
    (hs : 1 ≤ s) (ha : 1 ≤ a) (hh : 1 ≤ h) (hw : 0 ≤ w)
    (hΔ : 0 < Δ) (hτ : 0 ≤ τ)
    (hdeposit : ∀ n, Bank.calibrates (paperTarget s a h w) d n →
      Δ ≤ d (n + 1) ∧ d (n + 1) ≤ τ),
    Filter.Tendsto (fun K : ℕ => (Bank.count (paperTarget s a h w) d K : ℝ) / (K : ℝ))
      Filter.atTop (nhds 0) := by
  sorry

end

end P36Contract.BankTarget

namespace P36Contract.Bounds

section

open Paper36.Bounds

/-- Complete declaration of `Paper36.Bounds.expected_high_eq_confidence`; source support: S5.Thmtheorem5. -/
theorem expected_high_eq_confidence : ∀ {s a h W : ℝ} (hs : 1 ≤ s) (ha : 1 ≤ a)
    (hh : 1 ≤ h) (K : ℕ) (hK : 1 ≤ K),
    4*W*Real.sqrt (Target.Lambda s a h K*(K : ℝ)*
      (2*(s*a)*Real.log (Real.exp 1*(K : ℝ)*h))) =
      Target.confidence (Target.scale W s a) s a h K * Real.sqrt (K : ℝ) := by
  sorry

end

section

open Paper36.Bounds

/-- Complete declaration of `Paper36.Bounds.reward_high_factor`; source support: S5.Thmtheorem8. -/
theorem reward_high_factor : ∀ {R h K L : ℝ} (hR : 0 ≤ R) (hh : 0 ≤ h)
    (hK : 0 ≤ K) (hL : 0 ≤ L),
    h*Real.sqrt (2*L)*(3*Real.sqrt (R*K*h)) =
      3*Real.sqrt 2*(h*Real.sqrt h*Real.sqrt (R*K*L)) := by
  sorry

end

section

open Paper36.Bounds

/-- Complete declaration of `Paper36.Bounds.certificate_budget_charge`; source support: S5.Thmtheorem6. -/
theorem certificate_budget_charge : ∀ {s a h δ : ℝ} (hs : 0 < s) (ha : 0 < a) (hh : 0 < h)
    (hδ : 0 < δ) {K : ℕ} (hK : 0 < K),
    (s*a)*((K : ℝ)*h)/certificateBudget s a h δ K = δ/(4*(K : ℝ)) := by
  sorry

end

end P36Contract.Bounds

namespace P36Contract.Confidence

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable [IsProbabilityMeasure μ] {History Model : Type*} [MeasurableSpace History] [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model]

open Paper36.Confidence

/-- Complete declaration of `Paper36.Confidence.posterior_prefix_failure_bound`; source support: S5.Thmtheorem5. -/
theorem posterior_prefix_failure_bound : ∀ {Row : Type*} [Fintype Row] {T : ℕ}
    (history : Ω → History) (latent sampled : Ω → Model)
    (count : Ω → Row → ℕ) (prefixBall : Ω → Row → ℕ → Set Model)
    (currentSet : Set (History × Model)) (hcurrent : MeasurableSet currentSet)
    (hh : AEMeasurable history μ) (hl : AEMeasurable latent μ) (hs : AEMeasurable sampled μ)
    (hposterior : condDistrib latent history μ =ᵐ[μ.map history] condDistrib sampled history μ)
    (hcount : ∀ ω r, count ω r ≤ T)
    (hzero : ∀ ω r θ, θ ∈ prefixBall ω r 0)
    (hcompat : ∀ ω θ, (history ω, θ) ∈ currentSet ↔
      ∀ r, θ ∈ prefixBall ω r (count ω r))
    {ε : ℝ≥0∞}
    (hprefix : ∀ r (n : Fin T), μ {ω | latent ω ∉ prefixBall ω r (n.val + 1)} ≤ ε),
    μ {ω | (history ω, latent ω) ∉ currentSet} ≤ (Fintype.card Row : ℝ≥0∞) * T * ε ∧
    μ {ω | (history ω, sampled ω) ∉ currentSet} ≤ (Fintype.card Row : ℝ≥0∞) * T * ε := by
  sorry

end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable [IsProbabilityMeasure μ] {History Model : Type*} [MeasurableSpace History] [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model]

open Paper36.Confidence

/-- Complete declaration of `Paper36.Confidence.posterior_joint_failure_bound`; source support: S5.Thmtheorem6. -/
theorem posterior_joint_failure_bound : ∀ {Episode I : Type*} [Fintype Episode] [Fintype I]
    (history : Episode → Ω → History) (latent : Ω → Model) (sampled : Episode → Ω → Model)
    (currentSet : Episode → Set (History × Model)) (prefixFailure : I → Set Ω)
    (hcurrent : ∀ k, MeasurableSet (currentSet k))
    (hh : ∀ k, AEMeasurable (history k) μ) (hl : AEMeasurable latent μ)
    (hs : ∀ k, AEMeasurable (sampled k) μ)
    (hposterior : ∀ k, condDistrib latent (history k) μ =ᵐ[μ.map (history k)]
      condDistrib (sampled k) (history k) μ)
    (hcompat : ∀ k, {ω | (history k ω, latent ω) ∉ currentSet k} ⊆ ⋃ i, prefixFailure i)
    {ε : ℝ≥0∞} (hprefix : ∀ i, μ (prefixFailure i) ≤ ε),
    μ ((⋃ i, prefixFailure i) ∪ ⋃ k, {ω | (history k ω, sampled k ω) ∉ currentSet k}) ≤
      (1 + (Fintype.card Episode : ℝ≥0∞)) * (Fintype.card I : ℝ≥0∞) * ε := by
  sorry

end

end P36Contract.Confidence

namespace P36Contract.Counts

section
variable {ι : Type*} [DecidableEq ι] {rows : Finset ι} {v : ι → ℕ → ℕ} {H : ℕ}

open Paper36.Counts

/-- Complete declaration of `Paper36.Counts.all_rows_low_charge`; source support: S5.Thmtheorem5. -/
theorem all_rows_low_charge : ∀ (hrows : rows.Nonempty) (hH : 0 < H)
    (htotal : ∀ k, ∑ x ∈ rows, v x k ≤ H) (K : ℕ),
    (∑ x ∈ rows, lowCharge (v x) H K) < 2 * rows.card * H := by
  sorry

end

section
variable {ι : Type*} [DecidableEq ι] {rows : Finset ι} {v : ι → ℕ → ℕ} {H : ℕ}

open Paper36.Counts

/-- Complete declaration of `Paper36.Counts.all_rows_log_charge`; source support: S5.Thmtheorem5. -/
theorem all_rows_log_charge : ∀ (hH : 0 < H)
    (htotal : ∀ k, ∑ x ∈ rows, v x k ≤ H) {K : ℕ} (hK : 1 ≤ K),
    (∑ x ∈ rows, highLogCharge (v x) H K) ≤
      2 * (rows.card : ℝ) * Real.log (Real.exp 1 * (K : ℝ) * H) := by
  sorry

end

section
variable {ι : Type*} [DecidableEq ι] {rows : Finset ι} {v : ι → ℕ → ℕ} {H : ℕ}

open Paper36.Counts

/-- Complete declaration of `Paper36.Counts.all_rows_sqrt_charge`; source support: S5.Thmtheorem5. -/
theorem all_rows_sqrt_charge : ∀ (hH : 0 < H)
    (htotal : ∀ k, ∑ x ∈ rows, v x k ≤ H) (K : ℕ),
    (∑ x ∈ rows, highSqrtCharge (v x) H K) ≤
      3 * Real.sqrt ((rows.card : ℝ) * (K : ℝ) * H) := by
  sorry

end

end P36Contract.Counts

namespace P36Contract.Divergence

section
open Paper36.CVaR
open scoped ENNReal
variable {Ω : Type*} [Fintype Ω]

open Paper36.CVaR

/-- Complete declaration of `Paper36.CVaR.hellinger_triangle`; source support: S5.Thmtheorem5. -/
theorem hellinger_triangle : ∀ (P Q R : Law Ω),
    hellinger P R ≤ hellinger P Q + hellinger Q R := by
  sorry

end

section
open Paper36.CVaR
open scoped ENNReal
variable {Ω : Type*} [Fintype Ω]

open Paper36.CVaR

/-- Complete declaration of `Paper36.CVaR.two_hellingerSq_le_kl`; source support: S5.Thmtheorem5. -/
theorem two_hellingerSq_le_kl : ∀ (P Q : Law Ω),
    ENNReal.ofReal (2*hellingerSq P Q) ≤ kl P Q := by
  sorry

end

section
open Paper36.CVaR
open scoped ENNReal
variable {Ω : Type*} [Fintype Ω]

open Paper36.CVaR

/-- Complete declaration of `Paper36.CVaR.hellinger_le_of_two_kl_same`; source support: S5.Thmtheorem5. -/
theorem hellinger_le_of_two_kl_same : ∀ (P Q empirical : Law Ω) {ε : ℝ} (hε : 0 ≤ ε)
    (hP : kl empirical P ≤ ENNReal.ofReal ε)
    (hQ : kl empirical Q ≤ ENNReal.ofReal ε),
    hellinger P Q ≤ Real.sqrt (2*ε) := by
  sorry

end

end P36Contract.Divergence

namespace P36Contract.Endpoints

section
open Set Paper36.Regularity
variable {Ω S A : Type*} [Fintype Ω] [Fintype S] [Fintype A]

open Paper36.Endpoints

/-- Complete declaration of `Paper36.Endpoints.cvar_one_eq_expectation`; source support: S4.Thmtheorem2. -/
theorem cvar_one_eq_expectation : ∀ (P : CVaR.Law Ω) (X : Ω → ℝ),
    CVaR.value P 1 X = CVaR.expect P.mass X := by
  sorry

end

section
open Set Paper36.Regularity
variable {Ω S A : Type*} [Fintype Ω] [Fintype S] [Fintype A]

open Paper36.Endpoints

/-- Complete declaration of `Paper36.Endpoints.nested_one_eq_expected_cost`; source support: S4.Thmtheorem2. -/
theorem nested_one_eq_expected_cost : ∀ (c : ℕ → S → A → ℝ)
    (hc : ∀ h s a, c h s a ∈ Icc 0 1)
    (π : Nested.Policy S A) (q : Nested.Kernel S A) (n h : ℕ) (s : S),
    Nested.risk 1 c π q n h s = Nested.reward c π q n h s := by
  sorry

end

section
open Set Paper36.Regularity
variable {Ω S A : Type*} [Fintype Ω] [Fintype S] [Fintype A]

open Paper36.Endpoints

/-- Complete declaration of `Paper36.Endpoints.one_stage_exact_oracles`; source support: S4.Thmtheorem2. -/
theorem one_stage_exact_oracles : ∀ (α τ : ℝ) (c r : ℕ → S → A → ℝ)
    (p : Nested.Kernel S A) (q : ℕ → Nested.Kernel S A)
    (π : ℕ → Nested.Policy S A) (comparator : Nested.Policy S A)
    (h : ℕ) (s : S)
    (hcf : Nested.risk α c comparator p 1 h s ≤ τ)
    (hco : ∀ π', Nested.risk α c π' p 1 h s ≤ τ →
      Nested.reward r π' p 1 h s ≤ Nested.reward r comparator p 1 h s)
    (hπf : ∀ n, Nested.risk α c (π n) (q n) 1 h s ≤ τ)
    (hπo : ∀ n π', Nested.risk α c π' (q n) 1 h s ≤ τ →
      Nested.reward r π' (q n) 1 h s ≤ Nested.reward r (π n) (q n) 1 h s)
    (K : ℕ),
    (∑ n ∈ Finset.range K, (Nested.risk α c (π n) p 1 h s - τ)) ≤ 0 ∧
    (∑ n ∈ Finset.range K, (Nested.reward r comparator p 1 h s -
      Nested.reward r (π n) p 1 h s)) = 0 := by
  sorry

end

section
open Set Paper36.Regularity
variable {Ω S A : Type*} [Fintype Ω] [Fintype S] [Fintype A]

open Paper36.Endpoints

/-- Complete declaration of `Paper36.Endpoints.one_stage_bayesian_exact`; source support: S4.Thmtheorem2. -/
theorem one_stage_bayesian_exact : ∀ {Ξ : Type*} [Fintype Ξ] (P : Law Ξ)
    (α τ : ℝ) (c r : ℕ → S → A → ℝ)
    (p : Ξ → Nested.Kernel S A) (q : ℕ → Ξ → Nested.Kernel S A)
    (π : ℕ → Ξ → Nested.Policy S A) (comparator : Ξ → Nested.Policy S A)
    (h : ℕ) (s : S)
    (hcf : ∀ ω, Nested.risk α c (comparator ω) (p ω) 1 h s ≤ τ)
    (hco : ∀ ω π', Nested.risk α c π' (p ω) 1 h s ≤ τ →
      Nested.reward r π' (p ω) 1 h s ≤ Nested.reward r (comparator ω) (p ω) 1 h s)
    (hπf : ∀ ω n, Nested.risk α c (π n ω) (q n ω) 1 h s ≤ τ)
    (hπo : ∀ ω n π', Nested.risk α c π' (q n ω) 1 h s ≤ τ →
      Nested.reward r π' (q n ω) 1 h s ≤ Nested.reward r (π n ω) (q n ω) 1 h s)
    (K : ℕ),
    expectation P (fun ω => ∑ n ∈ Finset.range K,
      (Nested.risk α c (π n ω) (p ω) 1 h s - τ)) ≤ 0 ∧
    expectation P (fun ω => ∑ n ∈ Finset.range K,
      (Nested.reward r (comparator ω) (p ω) 1 h s -
        Nested.reward r (π n ω) (p ω) 1 h s)) = 0 := by
  sorry

end

section
open Set Paper36.Regularity
variable {Ω S A : Type*} [Fintype Ω] [Fintype S] [Fintype A]

open Paper36.Endpoints

/-- Complete declaration of `Paper36.Endpoints.one_stage_bayesian_approximate`; source support: A2.Thmtheorem1. -/
theorem one_stage_bayesian_approximate : ∀ {Ξ : Type*} [Fintype Ξ] (P : Law Ξ)
    (α τ : ℝ) (c r : ℕ → S → A → ℝ)
    (p : Ξ → Nested.Kernel S A) (q : ℕ → Ξ → Nested.Kernel S A)
    (π : ℕ → Ξ → Nested.Policy S A) (comparator : Ξ → Nested.Policy S A)
    (h : ℕ) (s : S) (ε ζ : ℕ → ℝ)
    (hcf : ∀ ω, Nested.risk α c (comparator ω) (p ω) 1 h s ≤ τ)
    (hπf : ∀ ω n, Nested.risk α c (π n ω) (q n ω) 1 h s ≤ τ + ε n)
    (hπo : ∀ ω n π', Nested.risk α c π' (q n ω) 1 h s ≤ τ →
      Nested.reward r π' (q n ω) 1 h s ≤ Nested.reward r (π n ω) (q n ω) 1 h s + ζ n)
    (K : ℕ),
    expectation P (fun ω => ∑ n ∈ Finset.range K,
      (Nested.risk α c (π n ω) (p ω) 1 h s - τ)) ≤
      (∑ n ∈ Finset.range K, ε n) ∧
    expectation P (fun ω => ∑ n ∈ Finset.range K,
      (Nested.reward r (comparator ω) (p ω) 1 h s -
        Nested.reward r (π n ω) (p ω) 1 h s)) ≤ (∑ n ∈ Finset.range K, ζ n) := by
  sorry

end

section
open Set Paper36.Regularity
variable {Ω S A : Type*} [Fintype Ω] [Fintype S] [Fintype A]

open Paper36.Endpoints

/-- Complete declaration of `Paper36.Endpoints.one_stage_zero_calibration`; source support: S4.Thmtheorem2. -/
theorem one_stage_zero_calibration : ∀ (α s a : ℝ) (d : ℕ → ℝ) (K : ℕ),
    Bank.bank (BankTarget.paperTarget s a 1 (Weights.W α 1)) d K = 0 ∧
      Bank.count (BankTarget.paperTarget s a 1 (Weights.W α 1)) d K = 0 := by
  sorry

end

section
open Set Paper36.Regularity
variable {Ω S A : Type*} [Fintype Ω] [Fintype S] [Fintype A]

open Paper36.Endpoints

/-- Complete declaration of `Paper36.Endpoints.signed_guarantee_not_positive_or_safe`; source support: S2.Thmtheorem2, S5.Thmtheorem7. -/
theorem signed_guarantee_not_positive_or_safe : ∀ (α G : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hG : 0 ≤ G),
    ∃ K : ℕ,
      (∀ n, Nested.risk α exampleCost (alternatingPolicy n) exampleKernel 1 0 () ∈ Icc (0 : ℝ) 1) ∧
      (∀ N, (∑ n ∈ Finset.range N,
        (Nested.risk α exampleCost (alternatingPolicy n) exampleKernel 1 0 () - (1 : ℝ) / 2)) ≤ G) ∧
      G < (∑ n ∈ Finset.range (2 * K), max
        (Nested.risk α exampleCost (alternatingPolicy n) exampleKernel 1 0 () - (1 : ℝ) / 2) 0) ∧
      (1 : ℝ) / 2 < Nested.risk α exampleCost (alternatingPolicy 1) exampleKernel 1 0 () := by
  sorry

end

end P36Contract.Endpoints

namespace P36Contract.FinitePolicies

section
open Paper36.Regularity Paper36.Nested
variable {S A : Type*} [Fintype S] [Fintype A]

open Paper36.FinitePolicies

/-- Complete declaration of `Paper36.FinitePolicies.finite_horizon_equivalence`; source support: S6.Thmtheorem2. -/
theorem finite_horizon_equivalence : ∀ [Nonempty A] (α : ℝ)
    (c r : ℕ → S → A → ℝ) (q : Kernel S A) (π : Policy S A) (H : ℕ) (s : S),
    risk α c (extend (restrict H π)) q H 0 s = risk α c π q H 0 s ∧
      reward r (extend (restrict H π)) q H 0 s = reward r π q H 0 s := by
  sorry

end

end P36Contract.FinitePolicies

namespace P36Contract.HeterogeneousRareChain

section
open Finset Set Paper36.Regularity Paper36.LowerBound

open Paper36.LowerBound.Heterogeneous

/-- Complete declaration of `Paper36.LowerBound.Heterogeneous.stage_initial_risk`; source support: S7.Thmtheorem1. -/
theorem stage_initial_risk : ∀ {d : ℕ} (hd : 0 < d) (a : ℕ → ℝ) (ha : ∀ j, 0 < a j ∧ a j ≤ 1)
    (θ : Bool) (π : Nested.Policy (ChainState d) Bool),
    Paper36.StageRisk.risk a (chainCost (d+2)) (finitePolicy π) (finiteKernel (kernel hd a ha θ))
      (d+2) 0 start = π 0 start (!θ) := by
  sorry

end

section
open Finset Set Paper36.Regularity Paper36.LowerBound

open Paper36.LowerBound.Heterogeneous

/-- Complete declaration of `Paper36.LowerBound.Heterogeneous.full_trace_likelihood_equal`; source support: S7.Thmtheorem1. -/
theorem full_trace_likelihood_equal : ∀ {d : ℕ} (hd : 0 < d) (a : ℕ → ℝ)
    (ha : ∀ j, 0 < a j ∧ a j ≤ 1) (π : Nested.Policy (ChainState d) Bool)
    (xs : Trace d) (hx : ∀ e ∈ xs, e.2.2 ≠ good ∧ e.2.2 ≠ bad) (h : ℕ),
    traceLikelihood (kernel hd a ha false) π h xs = traceLikelihood (kernel hd a ha true) π h xs := by
  sorry

end

section
open Finset Set Paper36.Regularity Paper36.LowerBound

open Paper36.LowerBound.Heterogeneous

/-- Complete declaration of `Paper36.LowerBound.Heterogeneous.private_seed_exact_optimum`; source support: S7.Thmtheorem1. -/
theorem private_seed_exact_optimum : ∀ {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (hd : 0 < d) (a : ℕ → ℝ) (ha : ∀ j, 0 < a j ∧ a j ≤ 1) (k : ℕ),
    IsLeast {v : ℝ | ∃ σ : Ω → PhysicalController d,
      MeasureTheory.Integrable (fun ω => bayesDebt hd a ha (σ ω) [] k) μ ∧ v = seedDebt μ hd a ha σ k}
      ((1-(1-Paper36.Weights.prefixMass a (d+1))^k)/(2*Paper36.Weights.prefixMass a (d+1))-(k : ℝ)/4) := by
  sorry

end

section
open Finset Set Paper36.Regularity Paper36.LowerBound

open Paper36.LowerBound.Heterogeneous

/-- Complete declaration of `Paper36.LowerBound.Heterogeneous.finite_rates_exact_optimum`; source support: S7.Thmtheorem1. -/
theorem finite_rates_exact_optimum : ∀ {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (hd : 0 < d) (v : Fin (d+1) → ℝ) (hv : ∀ j, 0 < v j ∧ v j ≤ 1) (k : ℕ),
    IsLeast {z : ℝ | ∃ σ : Ω → PhysicalController d,
      MeasureTheory.Integrable (fun ω => bayesDebt hd (extendRates v) (extendRates_bounds v hv) (σ ω) [] k) μ ∧
      z = seedDebt μ hd (extendRates v) (extendRates_bounds v hv) σ k}
      ((1-(1-∏ j, v j)^k)/(2*∏ j, v j)-(k : ℝ)/4) := by
  sorry

end

section
open Finset Set Paper36.Regularity Paper36.LowerBound

open Paper36.LowerBound.Heterogeneous

/-- Complete declaration of `Paper36.LowerBound.Heterogeneous.finite_rates_tailored`; source support: S7.Thmtheorem1. -/
theorem finite_rates_tailored : ∀ {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (hd : 0 < d) (v : Fin (d+1) → ℝ) (hv : ∀ j, 0 < v j ∧ v j ≤ 1)
    (hβ4 : (∏ j, v j) ≤ 1/4) (σ : Ω → PhysicalController d)
    (hσ : MeasureTheory.Integrable
      (fun ω => bayesDebt hd (extendRates v) (extendRates_bounds v hv) (σ ω) [] (K0 (∏ j, v j))) μ),
    1/(32*∏ j, v j) ≤ seedDebt μ hd (extendRates v) (extendRates_bounds v hv) σ (K0 (∏ j, v j)) := by
  sorry

end

section
open Finset Set Paper36.Regularity Paper36.LowerBound

open Paper36.LowerBound.Heterogeneous

/-- Complete declaration of `Paper36.LowerBound.Heterogeneous.homogeneous_bayes_prior`; source support: S7.Thmtheorem1. -/
theorem homogeneous_bayes_prior : ∀ {d : ℕ} (hd : 0 < d) (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (σ : PhysicalController d) (hist : List (Trace d)) (k : ℕ),
    physicalBayesDebt hd α hα hα1 σ hist k =
      expectation uniformPrior (fun θ => physicalDebt hd α hα hα1 σ θ hist k) := by
  sorry

end

section
open Finset Set Paper36.Regularity Paper36.LowerBound

open Paper36.LowerBound.Heterogeneous

/-- Complete declaration of `Paper36.LowerBound.Heterogeneous.heterogeneous_bayes_prior`; source support: S7.Thmtheorem1. -/
theorem heterogeneous_bayes_prior : ∀ {d : ℕ} (hd : 0 < d) (a : ℕ → ℝ) (ha : ∀ j, 0 < a j ∧ a j ≤ 1)
    (σ : PhysicalController d) (hist : List (Trace d)) (k : ℕ),
    bayesDebt hd a ha σ hist k = expectation uniformPrior (fun θ => debt hd a ha σ θ hist k) := by
  sorry

end

section
open Finset Set Paper36.Regularity Paper36.LowerBound

open Paper36.LowerBound.Heterogeneous

/-- Complete declaration of `Paper36.LowerBound.Heterogeneous.homogeneous_constrained_comparator`; source support: S7.Thmtheorem1. -/
theorem homogeneous_constrained_comparator : ∀ {d : ℕ} (hd : 0 < d) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (θ : Bool),
    ∃ π : Nested.Policy (ChainState d) Bool,
      Nested.risk α (chainCost (d+2)) π (chainKernel hd α hα.le hα1 θ) (d+2) 0 start ≤ 1/4 ∧
      Nested.reward chainReward π (chainKernel hd α hα.le hα1 θ) (d+2) 0 start = 1 ∧
      ∀ π', Nested.risk α (chainCost (d+2)) π' (chainKernel hd α hα.le hα1 θ) (d+2) 0 start ≤ 1/4 →
        Nested.reward chainReward π' (chainKernel hd α hα.le hα1 θ) (d+2) 0 start ≤ 1 := by
  sorry

end

section
open Finset Set Paper36.Regularity Paper36.LowerBound

open Paper36.LowerBound.Heterogeneous

/-- Complete declaration of `Paper36.LowerBound.Heterogeneous.fallback_constrained_comparator`; source support: S7.Thmtheorem2. -/
theorem fallback_constrained_comparator : ∀ {d : ℕ} (hd : 0 < d) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (θ : Bool),
    ∃ π : Nested.Policy (ChainState d) (Option Bool),
      Nested.risk α (fallbackCost (d+2)) π (fallbackKernel hd α hα.le hα1 θ) (d+2) 0 start ≤ 1/4 ∧
      Nested.reward fallbackReward π (fallbackKernel hd α hα.le hα1 θ) (d+2) 0 start = 1 ∧
      ∀ π', Nested.risk α (fallbackCost (d+2)) π' (fallbackKernel hd α hα.le hα1 θ) (d+2) 0 start ≤ 1/4 →
        Nested.reward fallbackReward π' (fallbackKernel hd α hα.le hα1 θ) (d+2) 0 start ≤ 1 := by
  sorry

end

end P36Contract.HeterogeneousRareChain

namespace P36Contract.HybridCharging

section
open Paper36.CVaR Paper36.Simulation MeasureTheory
variable {S A : Type*} [Fintype S] [Fintype A]
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

open Paper36.HybridCharging

/-- Complete declaration of `Paper36.HybridCharging.actual_hybrid_stage`; source support: S5.Thmtheorem2. -/
theorem actual_hybrid_stage : ∀ (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1)
    (π : ℕ → Policy S A) (p : Kernel S A) (q : ℕ → Kernel S A)
    (s₀ : S) (N : ℕ → S × A → ℕ) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (H k h : ℕ) (hh : h < H)
    (hrow : ∀ s a, H+1 ≤ N k (s,a) →
      hellingerSq (p s a) (q k s a) ≤ 2 * Λ / N k (s,a)),
    let d := occupancy (adverseKernel α hα hα1 c (π k) p (H+1)) (dirac s₀) h
    expect d.mass (epsilon α c (π k) p (q k) (H+1) h) ≤
      Weights.w α (H+1) * nominalLow π p s₀ N H k h +
      4 * Real.sqrt (Λ * stageWeight α H h * nominalHigh π p s₀ N H k h) := by
  sorry

end

section
open Paper36.CVaR Paper36.Simulation MeasureTheory
variable {S A : Type*} [Fintype S] [Fintype A]
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

open Paper36.HybridCharging

/-- Complete declaration of `Paper36.HybridCharging.risk_hybrid_sum_bound`; source support: S5.Thmtheorem2. -/
theorem risk_hybrid_sum_bound : ∀ (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1)
    (π : ℕ → Policy S A) (p : Kernel S A) (q : ℕ → Kernel S A)
    (s₀ : S) (N : ℕ → S × A → ℕ) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (K H : ℕ) (hrow : ∀ k, k < K → ∀ s a, H+1 ≤ N k (s,a) →
      hellingerSq (p s a) (q k s a) ≤ 2 * Λ / N k (s,a)),
    (∑ k ∈ Finset.range K,
      (risk α c (π k) p (H+1) 0 s₀ - risk α c (π k) (q k) (H+1) 0 s₀)) ≤
      Weights.w α (H+1) * Ylo π p s₀ N K H +
      4 * Weights.W α (H+1) * Real.sqrt (Λ * (K : ℝ) * Yhi π p s₀ N K H) := by
  sorry

end

section
open Paper36.CVaR Paper36.Simulation MeasureTheory
variable {S A : Type*} [Fintype S] [Fintype A]
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

open Paper36.HybridCharging

/-- Complete declaration of `Paper36.HybridCharging.reward_charging_bound`; source support: S5.Thmtheorem8. -/
theorem reward_charging_bound : ∀ (r : ℕ → S → A → ℝ)
    (hr : ∀ h s a, 0 ≤ r h s a ∧ r h s a ≤ 1)
    (π : ℕ → Policy S A) (p : Kernel S A) (q : ℕ → Kernel S A)
    (s₀ : S) (N : ℕ → S × A → ℕ) {L : ℝ} (hL : 0 ≤ L)
    (K H : ℕ) (hrow : ∀ k, k < K → ∀ s a, H+1 ≤ N k (s,a) →
      tv (p s a) (q k s a) ≤ Real.sqrt (2*L / N k (s,a))),
    (∑ k ∈ Finset.range K,
      (ordinaryReward r (π k) (q k) (H+1) 0 s₀ - ordinaryReward r (π k) p (H+1) 0 s₀)) ≤
      ((H+1 : ℕ) : ℝ) * Ylo π p s₀ N K H +
      ((H+1 : ℕ) : ℝ) * Real.sqrt (2*L) * Ysqrt π p s₀ N K H := by
  sorry

end

section
open Paper36.CVaR Paper36.Simulation MeasureTheory
variable {S A : Type*} [Fintype S] [Fintype A]
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

open Paper36.HybridCharging

/-- Complete declaration of `Paper36.HybridCharging.masked_risk_hybrid_sum_bound`; source support: S5.Thmtheorem5. -/
theorem masked_risk_hybrid_sum_bound : ∀ (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1)
    (π : ℕ → Policy S A) (p : Kernel S A) (q : ℕ → Kernel S A)
    (s₀ : S) (N : ℕ → S × A → ℕ) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (K H : ℕ) (good : ℕ → Prop) [DecidablePred good]
    (hrow : ∀ k, k < K → good k → ∀ s a, H+1 ≤ N k (s,a) →
      hellingerSq (p s a) (q k s a) ≤ 2 * Λ / N k (s,a)),
    (∑ k ∈ Finset.range K, if good k then
      (risk α c (π k) p (H+1) 0 s₀ - risk α c (π k) (q k) (H+1) 0 s₀) else 0) ≤
      Weights.w α (H+1) * Ylo π p s₀ N K H +
      4 * Weights.W α (H+1) * Real.sqrt (Λ * (K : ℝ) * Yhi π p s₀ N K H) := by
  sorry

end

section
open Paper36.CVaR Paper36.Simulation MeasureTheory
variable {S A : Type*} [Fintype S] [Fintype A]
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

open Paper36.HybridCharging

/-- Complete declaration of `Paper36.HybridCharging.masked_reward_charging_bound`; source support: S5.Thmtheorem8. -/
theorem masked_reward_charging_bound : ∀ (r : ℕ → S → A → ℝ)
    (hr : ∀ h s a, 0 ≤ r h s a ∧ r h s a ≤ 1)
    (π : ℕ → Policy S A) (p : Kernel S A) (q : ℕ → Kernel S A)
    (s₀ : S) (N : ℕ → S × A → ℕ) {L : ℝ} (hL : 0 ≤ L)
    (K H : ℕ) (good : ℕ → Prop) [DecidablePred good]
    (hrow : ∀ k, k < K → good k → ∀ s a, H+1 ≤ N k (s,a) →
      tv (p s a) (q k s a) ≤ Real.sqrt (2*L / N k (s,a))),
    (∑ k ∈ Finset.range K, if good k then
      (ordinaryReward r (π k) (q k) (H+1) 0 s₀ - ordinaryReward r (π k) p (H+1) 0 s₀) else 0) ≤
      ((H+1 : ℕ) : ℝ) * Ylo π p s₀ N K H +
      ((H+1 : ℕ) : ℝ) * Real.sqrt (2*L) * Ysqrt π p s₀ N K H := by
  sorry

end

section
open Paper36.CVaR Paper36.Simulation MeasureTheory
variable {S A : Type*} [Fintype S] [Fintype A]
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

open Paper36.HybridCharging

/-- Complete declaration of `Paper36.HybridCharging.expected_charging_bound`; source support: S5.Thmtheorem5. -/
theorem expected_charging_bound : ∀ {F L Y : Ω → ℝ} {w W Λ : ℝ}
    (hF : Integrable F μ) (hL : Integrable L μ) (hY : Integrable Y μ)
    (hY0 : ∀ᵐ ω ∂μ, 0 ≤ Y ω) (hW : 0 ≤ W) (hΛ : 0 ≤ Λ) (K : ℕ)
    (hpath : ∀ᵐ ω ∂μ, F ω ≤ w * L ω + 4 * W * Real.sqrt (Λ * (K : ℝ) * Y ω)),
    (∫ ω, F ω ∂μ) ≤ w * (∫ ω, L ω ∂μ) +
      4 * W * Real.sqrt (Λ * (K : ℝ) * (∫ ω, Y ω ∂μ)) := by
  sorry

end

end P36Contract.HybridCharging

namespace P36Contract.Measurability

section
open MeasureTheory Paper36
variable {S A Ω : Type*} [Fintype S] [Fintype A] [MeasurableSpace Ω]

open Paper36.Measurability

/-- Complete declaration of `Paper36.Measurability.measurable_risk`; source support: S5.Thmtheorem5. -/
theorem measurable_risk : ∀ (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (π : Ω → Simulation.Policy S A) (p : Ω → Simulation.Kernel S A)
    (hπ : ∀ h s a, Measurable (fun ω => (π ω h s).mass a))
    (hp : ∀ s a t, Measurable (fun ω => (p ω s a).mass t)) (n h : ℕ) (s : S),
    Measurable (fun ω => Simulation.risk α c (π ω) (p ω) n h s) := by
  sorry

end

section
open MeasureTheory Paper36
variable {S A Ω : Type*} [Fintype S] [Fintype A] [MeasurableSpace Ω]

open Paper36.Measurability

/-- Complete declaration of `Paper36.Measurability.measurable_reward`; source support: S5.Thmtheorem8. -/
theorem measurable_reward : ∀ (r : ℕ → S → A → ℝ)
    (π : Ω → Simulation.Policy S A) (p : Ω → Simulation.Kernel S A)
    (hπ : ∀ h s a, Measurable (fun ω => (π ω h s).mass a))
    (hp : ∀ s a t, Measurable (fun ω => (p ω s a).mass t)) (n h : ℕ) (s : S),
    Measurable (fun ω => reward r (π ω) (p ω) n h s) := by
  sorry

end

section
open MeasureTheory Paper36
variable {S A Ω : Type*} [Fintype S] [Fintype A] [MeasurableSpace Ω]

open Paper36.Measurability

/-- Complete declaration of `Paper36.Measurability.integrable_risk`; source support: S5.Thmtheorem5. -/
theorem integrable_risk : ∀ (μ : Measure Ω) [IsFiniteMeasure μ]
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (π : Ω → Simulation.Policy S A) (p : Ω → Simulation.Kernel S A)
    (hπ : ∀ h s a, Measurable (fun ω => (π ω h s).mass a))
    (hp : ∀ s a t, Measurable (fun ω => (p ω s a).mass t)) (n h : ℕ) (s : S),
    Integrable (fun ω => Simulation.risk α c (π ω) (p ω) n h s) μ := by
  sorry

end

section
open MeasureTheory Paper36
variable {S A Ω : Type*} [Fintype S] [Fintype A] [MeasurableSpace Ω]

open Paper36.Measurability

/-- Complete declaration of `Paper36.Measurability.integrable_reward`; source support: S5.Thmtheorem8. -/
theorem integrable_reward : ∀ [Nonempty A] (μ : Measure Ω) [IsFiniteMeasure μ]
    (r : ℕ → S → A → ℝ) (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (π : Ω → Simulation.Policy S A) (p : Ω → Simulation.Kernel S A)
    (hπ : ∀ h s a, Measurable (fun ω => (π ω h s).mass a))
    (hp : ∀ s a t, Measurable (fun ω => (p ω s a).mass t)) (n h : ℕ) (s : S),
    Integrable (fun ω => reward r (π ω) (p ω) n h s) μ := by
  sorry

end

end P36Contract.Measurability

namespace P36Contract.PosteriorAlgorithm

section
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested Paper36.Algorithm
variable {S A Ω Model Hist : Type*} [Fintype S] [Fintype A] [instNonemptyA : Nonempty A] [MeasurableSpace Ω] [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model] [MeasurableSpace Hist] {μ : Measure Ω} [IsProbabilityMeasure μ]

open Paper36.PosteriorAlgorithm

/-- Complete declaration of `Paper36.PosteriorAlgorithm.posterior_support`; source support: S4.Thmtheorem2. -/
theorem posterior_support : ∀ (decode : Model → Kernel S A) (hdecode : Measurable decode)
    (latent : Ω → Model) (hlatent : Measurable latent)
    (sampled : ℕ → Ω → Model) (hsampled : ∀ k, Measurable (sampled k))
    (history : ℕ → Ω → Hist) (hhistory : ∀ k, Measurable (history k))
    (hposterior : ∀ k, condDistrib latent (history k) μ =ᵐ[μ.map (history k)]
      condDistrib (sampled k) (history k) μ),
    ∀ᵐ ω ∂μ, decode (latent ω) ∈ (prior (μ := μ) decode latent).support ∧
      ∀ k, decode (sampled k ω) ∈ (prior (μ := μ) decode latent).support := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested Paper36.Algorithm
variable {S A Ω Model Hist : Type*} [Fintype S] [Fintype A] [instNonemptyA : Nonempty A] [MeasurableSpace Ω] [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model] [MeasurableSpace Hist] {μ : Measure Ω} [IsProbabilityMeasure μ]

open Paper36.PosteriorAlgorithm

/-- Complete declaration of `Paper36.PosteriorAlgorithm.gap_positive`; source support: S2.Thmtheorem1. -/
include instNonemptyA in
theorem gap_positive : ∀ (decode : Model → Kernel S A) (hdecode : Measurable decode)
    (latent : Ω → Model) (hlatent : Measurable latent)
    (α τ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (H : ℕ)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1) (s₁ : S)
    (hstrict : ∀ q ∈ (prior (μ := μ) decode latent).support, minimumRisk α c H 0 s₁ q < τ),
    0 < gap (μ := μ) decode latent α τ c H s₁ ∧
      ∀ q ∈ (prior (μ := μ) decode latent).support,
        minimumRisk α c H 0 s₁ q ≤ τ - gap (μ := μ) decode latent α τ c H s₁ := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested Paper36.Algorithm
variable {S A Ω Model Hist : Type*} [Fintype S] [Fintype A] [instNonemptyA : Nonempty A] [MeasurableSpace Ω] [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model] [MeasurableSpace Hist] {μ : Measure Ω} [IsProbabilityMeasure μ]

open Paper36.PosteriorAlgorithm

/-- Complete declaration of `Paper36.PosteriorAlgorithm.comparator_symmetry`; source support: S5.Thmtheorem8. -/
theorem comparator_symmetry : ∀ (decode : Model → Kernel S A) (hdecode : Measurable decode)
    (latent sampled : Ω → Model) (hlatent : Measurable latent) (hsampled : Measurable sampled)
    (history : Ω → Hist) (hhistory : Measurable history)
    (hposterior : condDistrib latent history μ =ᵐ[μ.map history] condDistrib sampled history μ)
    {α τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} (O : BorelAlgorithm.BorelOracles α c r H s₁ τ Q)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (hsupport : ∀ᵐ ω ∂μ, decode (latent ω) ∈ Q ∧ decode (sampled ω) ∈ Q),
    (∫ ω, constrainedValue α c r H s₁ τ (decode (latent ω)) -
      constrainedValue α c r H s₁ τ (decode (sampled ω)) ∂μ) = 0 := by
  sorry

end

end P36Contract.PosteriorAlgorithm

namespace P36Contract.RareChain

section
open Finset Set Paper36.Regularity

open Paper36.LowerBound

/-- Complete declaration of `Paper36.LowerBound.chain_state_count`; source support: S7.Thmtheorem1. -/
theorem chain_state_count : ∀ (H : ℕ) (hH : 2 ≤ H),
    Fintype.card (ChainState (H-2)) = 2*H := by
  sorry

end

section
open Finset Set Paper36.Regularity

open Paper36.LowerBound

/-- Complete declaration of `Paper36.LowerBound.full_trace_likelihood_equal`; source support: S7.Thmtheorem1. -/
theorem full_trace_likelihood_equal : ∀ {d : ℕ} (hd : 0 < d) (α : ℝ)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (π : Nested.Policy (ChainState d) Bool)
    (xs : Trace d) (hx : ∀ e ∈ xs, e.2.2 ≠ good ∧ e.2.2 ≠ bad) (h : ℕ),
    traceLikelihood (chainKernel hd α hα hα1 false) π h xs =
      traceLikelihood (chainKernel hd α hα hα1 true) π h xs := by
  sorry

end

section
open Finset Set Paper36.Regularity

open Paper36.LowerBound

/-- Complete declaration of `Paper36.LowerBound.source_initial_risk`; source support: S7.Thmtheorem1. -/
theorem source_initial_risk : ∀ {d : ℕ} (hd : 0 < d) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (θ : Bool) (π : Nested.Policy (ChainState d) Bool),
    Nested.risk α (chainCost (d+2)) π (chainKernel hd α hα.le hα1 θ)
      (d+2) 0 start = π 0 start (!θ) := by
  sorry

end

section
open Finset Set Paper36.Regularity

open Paper36.LowerBound

/-- Complete declaration of `Paper36.LowerBound.private_seed_learner_lower`; source support: S7.Thmtheorem1. -/
theorem private_seed_learner_lower : ∀ {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (hd : 0 < d) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (σ : Ω → PhysicalController d) (k : ℕ)
    (hσ : MeasureTheory.Integrable (fun ω => physicalBayesDebt hd α hα.le hα1 (σ ω) [] k) μ),
    bound (α^(d+1)) k ≤ seedBayesDebt μ hd α hα.le hα1 σ k := by
  sorry

end

section
open Finset Set Paper36.Regularity

open Paper36.LowerBound

/-- Complete declaration of `Paper36.LowerBound.source_minimum_risk_zero`; source support: S7.Thmtheorem1. -/
theorem source_minimum_risk_zero : ∀ {d : ℕ} (hd : 0 < d) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (θ : Bool),
    Nested.minimumRisk α (chainCost (d+2)) (d+2) 0 start
      (chainKernel hd α hα.le hα1 θ) = 0 := by
  sorry

end

section
open Finset Set Paper36.Regularity

open Paper36.LowerBound

/-- Complete declaration of `Paper36.LowerBound.physical_reward_shortfall_zero`; source support: S7.Thmtheorem1. -/
theorem physical_reward_shortfall_zero : ∀ {d : ℕ} (hd : 0 < d) (α : ℝ)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (σ : PhysicalController d) (θ : Bool)
    (hist : List (Trace d)) (k : ℕ),
    physicalRewardShortfall hd α hα hα1 σ θ hist k = 0 := by
  sorry

end

section
open Finset Set Paper36.Regularity

open Paper36.LowerBound

/-- Complete declaration of `Paper36.LowerBound.physical_exact_optimum`; source support: S7.Thmtheorem1. -/
theorem physical_exact_optimum : ∀ {d : ℕ} (hd : 0 < d) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (k : ℕ),
    IsLeast {v : ℝ | ∃ σ : PhysicalController d,
      v = physicalBayesDebt hd α hα.le hα1 σ [] k}
      ((1-(1-α^(d+1))^k)/(2*α^(d+1))-(k : ℝ)/4) := by
  sorry

end

section
open Finset Set Paper36.Regularity

open Paper36.LowerBound

/-- Complete declaration of `Paper36.LowerBound.private_seed_exact_optimum`; source support: S7.Thmtheorem1. -/
theorem private_seed_exact_optimum : ∀ {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (hd : 0 < d) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ),
    IsLeast {v : ℝ | ∃ σ : Ω → PhysicalController d,
      MeasureTheory.Integrable (fun ω => physicalBayesDebt hd α hα.le hα1 (σ ω) [] k) μ ∧
      v = seedBayesDebt μ hd α hα.le hα1 σ k}
      ((1-(1-α^(d+1))^k)/(2*α^(d+1))-(k : ℝ)/4) := by
  sorry

end

section
open Finset Set Paper36.Regularity

open Paper36.LowerBound

/-- Complete declaration of `Paper36.LowerBound.private_seed_tailored`; source support: S7.Thmtheorem1. -/
theorem private_seed_tailored : ∀ {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (hd : 0 < d) {α : ℝ} (hα : 0 < α) (hα2 : α ≤ 1/2)
    (σ : Ω → PhysicalController d)
    (hσ : MeasureTheory.Integrable
      (fun ω => physicalBayesDebt hd α hα.le (by linarith) (σ ω) [] (K0 (α^(d+1)))) μ),
    1/(32*α^(d+1)) ≤ seedBayesDebt μ hd α hα.le (by linarith) σ (K0 (α^(d+1))) := by
  sorry

end

section
open Finset Set Paper36.Regularity

open Paper36.LowerBound

/-- Complete declaration of `Paper36.LowerBound.fallback_comparators`; source support: S7.Thmtheorem2. -/
theorem fallback_comparators : ∀ {d : ℕ} (hd : 0 < d) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1),
    (∀ θ : Bool,
      Nested.risk α (fallbackCost (d+2)) (fun _ _ => Nested.pure (some θ))
        (fallbackKernel hd α hα.le hα1 θ) (d+2) 0 start = 0 ∧
      Nested.reward fallbackReward (fun _ _ => Nested.pure (some θ))
        (fallbackKernel hd α hα.le hα1 θ) (d+2) 0 start = 1) ∧
    (∀ θ : Bool,
      Nested.risk α (fallbackCost (d+2)) (fun _ _ => Nested.pure none)
        (fallbackKernel hd α hα.le hα1 θ) (d+2) 0 start = 0 ∧
      Nested.reward fallbackReward (fun _ _ => Nested.pure none)
        (fallbackKernel hd α hα.le hα1 θ) (d+2) 0 start = 0) := by
  sorry

end

section
open Finset Set Paper36.Regularity

open Paper36.LowerBound

/-- Complete declaration of `Paper36.LowerBound.private_seed_fallback_tradeoff`; source support: S7.Thmtheorem2. -/
theorem private_seed_fallback_tradeoff : ∀ {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (hd : 0 < d) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (σ : Ω → FallbackController d) (k : ℕ)
    (hρ : MeasureTheory.Integrable
      (fun ω => fallbackBayes hd α hα.le hα1 (fallbackRiskScore hd α hα.le hα1) (σ ω) [] k) μ)
    (hr : MeasureTheory.Integrable
      (fun ω => fallbackBayes hd α hα.le hα1 (fallbackRewardScore hd α hα.le hα1) (σ ω) [] k) μ),
    bound (α^(d+1)) k ≤
      seedFallback μ hd α hα.le hα1 (fallbackRiskScore hd α hα.le hα1) σ k +
      (1/2)*seedFallback μ hd α hα.le hα1 (fallbackRewardScore hd α hα.le hα1) σ k := by
  sorry

end

section
open Finset Set Paper36.Regularity

open Paper36.LowerBound

/-- Complete declaration of `Paper36.LowerBound.private_seed_fallback_pareto`; source support: S7.Thmtheorem2. -/
theorem private_seed_fallback_pareto : ∀ {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (hd : 0 < d) {α : ℝ} (hα : 0 < α) (hα2 : α ≤ 1/2)
    (σ : Ω → FallbackController d) {F G : ℝ} (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hρi : ∀ k, MeasureTheory.Integrable
      (fun ω => fallbackBayes hd α hα.le (by linarith) (fallbackRiskScore hd α hα.le (by linarith)) (σ ω) [] k) μ)
    (hri : ∀ k, MeasureTheory.Integrable
      (fun ω => fallbackBayes hd α hα.le (by linarith) (fallbackRewardScore hd α hα.le (by linarith)) (σ ω) [] k) μ)
    (hρ : ∀ k, seedFallback μ hd α hα.le (by linarith)
      (fallbackRiskScore hd α hα.le (by linarith)) σ k ≤ G)
    (hr : ∀ k, seedFallback μ hd α hα.le (by linarith)
      (fallbackRewardScore hd α hα.le (by linarith)) σ k ≤ F*Real.sqrt (k : ℝ)),
    1/(64*α^(d+1)) ≤ G ∨ Real.sqrt 2/(32*Real.sqrt (α^(d+1))) ≤ F := by
  sorry

end

end P36Contract.RareChain

namespace P36Contract.RiskBridge

section
variable {Ω S A : Type*} [Fintype Ω] [Fintype S] [Fintype A]

open Paper36.RiskBridge

/-- Complete declaration of `Paper36.RiskBridge.compactCVaR_eq_value`; source support: S2.Thmtheorem1. -/
theorem compactCVaR_eq_value : ∀ (α B : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (hB : 0 ≤ B) (P : Regularity.Law Ω) (X : Ω → ℝ)
    (hX : ∀ i, X i ∈ Set.Icc 0 B),
    Regularity.compactCVaR α B P X = CVaR.value (ofRegular P) α X := by
  sorry

end

section
variable {Ω S A : Type*} [Fintype Ω] [Fintype S] [Fintype A]

open Paper36.RiskBridge

/-- Complete declaration of `Paper36.RiskBridge.risk_eq_nested`; source support: S5.Thmtheorem3. -/
theorem risk_eq_nested : ∀ (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (π : Nested.Policy S A) (p : Nested.Kernel S A) (n h : ℕ) (s : S),
    Simulation.risk α c (ofPolicy π) (ofKernel p) n h s = Nested.risk α c π p n h s := by
  sorry

end

section
variable {Ω S A : Type*} [Fintype Ω] [Fintype S] [Fintype A]

open Paper36.RiskBridge

/-- Complete declaration of `Paper36.RiskBridge.nested_nominal_simulation`; source support: S5.Thmtheorem8. -/
theorem nested_nominal_simulation : ∀ (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (π : Nested.Policy S A) (p q : Nested.Kernel S A) (H : ℕ) (s₀ : S),
    Nested.risk α c π p (H+1) 0 s₀-Nested.risk α c π q (H+1) 0 s₀ ≤
      ∑ h ∈ Finset.range H, ((H-h : ℕ) : ℝ)*(α⁻¹)^(h+1) *
        ∑ s, (Simulation.occupancy (Simulation.nominal (ofPolicy π) (ofKernel p))
          (Simulation.dirac s₀) h).mass s *
            ∑ a, π h s a * CVaR.tv (ofRegular (p s a)) (ofRegular (q s a)) := by
  sorry

end

section
variable {Ω S A : Type*} [Fintype Ω] [Fintype S] [Fintype A]

open Paper36.RiskBridge

/-- Complete declaration of `Paper36.RiskBridge.nested_uniform_fixed_policy_perturbation`; source support: A3.Thmtheorem1, A3.Thmtheorem2. -/
theorem nested_uniform_fixed_policy_perturbation : ∀ [Nonempty S] [Nonempty A]
    (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (π : Nested.Policy S A) (p q : Nested.Kernel S A) (n h : ℕ) (s : S),
    |Nested.risk α c π p n h s-Nested.risk α c π q n h s| ≤
      (n : ℝ)*((n : ℝ)-1)/(2*α)*Simulation.maxRowTV (ofKernel p) (ofKernel q) := by
  sorry

end

section
variable {Ω S A : Type*} [Fintype Ω] [Fintype S] [Fintype A]

open Paper36.RiskBridge

/-- Complete declaration of `Paper36.RiskBridge.nested_lemma_5_3`; source support: S5.Thmtheorem3. -/
theorem nested_lemma_5_3 : ∀ (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (π : Nested.Policy S A) (p q : Nested.Kernel S A) (H : ℕ) (s₀ : S),
    ∃ d : ℕ → CVaR.Law S, (d 0).mass s₀ = 1 ∧
      (Nested.risk α c π p (H+1) 0 s₀-Nested.risk α c π q (H+1) 0 s₀ ≤
        ∑ h ∈ Finset.range H, CVaR.expect (d h).mass
          (sourceLocalError α c π p q (H+1-(h+1)) h)) ∧
      (Nested.risk α c π p (H+1) 0 s₀-Nested.risk α c π q (H+1) 0 s₀ ≤
        ∑ h ∈ Finset.range H, ((H-h : ℕ) : ℝ)/α *
          ∑ s, (d h).mass s * ∑ a, π h s a * CVaR.tv (ofRegular (p s a)) (ofRegular (q s a))) ∧
      (∀ h s a, (d h).mass s*π h s a ≤
        (α⁻¹)^h*((Simulation.occupancy (Simulation.nominal (ofPolicy π) (ofKernel p))
          (Simulation.dirac s₀) h).mass s*π h s a)) := by
  sorry

end

section
variable {Ω S A : Type*} [Fintype Ω] [Fintype S] [Fintype A]

open Paper36.RiskBridge

/-- Complete declaration of `Paper36.RiskBridge.tightening_nested_risk`; source support: S3.Thmtheorem1. -/
theorem tightening_nested_risk : ∀ (α t : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (p : Tightening.Policy),
    Nested.risk α (tighteningCost t) (tighteningPolicy p) tighteningKernel 1 0 () =
      Tightening.risk α t p := by
  sorry

end

section
variable {Ω S A : Type*} [Fintype Ω] [Fintype S] [Fintype A]

open Paper36.RiskBridge

/-- Complete declaration of `Paper36.RiskBridge.tightening_nested_reward`; source support: S3.Thmtheorem1. -/
theorem tightening_nested_reward : ∀ (p : Tightening.Policy),
    Nested.reward tighteningReward (tighteningPolicy p) tighteningKernel 1 0 () =
      Tightening.value p := by
  sorry

end

section
variable {Ω S A : Type*} [Fintype Ω] [Fintype S] [Fintype A]

open Paper36.RiskBridge

/-- Complete declaration of `Paper36.RiskBridge.every_one_stage_behavior`; source support: S3.Thmtheorem1. -/
theorem every_one_stage_behavior : ∀ (α t : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (π : Nested.Policy Unit Tightening.Action),
    ∃ p : Tightening.Policy,
      Nested.risk α (tighteningCost t) π tighteningKernel 1 0 () = Tightening.risk α t p ∧
      Nested.reward tighteningReward π tighteningKernel 1 0 () = Tightening.value p := by
  sorry

end

end P36Contract.RiskBridge

namespace P36Contract.RowTapes

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories
open scoped ENNReal
variable {S : Type*} [Fintype S] [MeasurableSpace S] [DiscreteMeasurableSpace S] [DecidableEq S]
variable {M : Type*} [MeasurableSpace M]
variable {Ω W : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W]

open Paper36.RowTapes

/-- Complete declaration of `Paper36.RowTapes.method_types_arbitrary_prior`; source support: S5.Thmtheorem5. -/
theorem method_types_arbitrary_prior : ∀ [Nonempty S]
    (external : ExternalCategoricalConcentration (S := S))
    (row : M → Law S) (hrow : ∀ s, Measurable (fun m => (row m).mass s))
    (latent : Ω → M) (hl : Measurable latent) (n : ℕ) (hn : 0 < n)
    (sample : Ω → Fin n → S) (hs : AEMeasurable sample μ)
    (hcond : condDistrib sample latent μ =ᵐ[μ.map latent] iidKernel row hrow n)
    (Λ : ℝ) (hΛ : 0 ≤ Λ),
    μ {ω | ENNReal.ofReal (Λ / n) < kl (empirical hn (sample ω)) (row (latent ω))} ≤
      ENNReal.ofReal (((n+1 : ℕ) : ℝ) ^ Fintype.card S * Real.exp (-Λ)) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories
open scoped ENNReal
variable {S : Type*} [Fintype S] [MeasurableSpace S] [DiscreteMeasurableSpace S] [DecidableEq S]
variable {M : Type*} [MeasurableSpace M]
variable {Ω W : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W]

open Paper36.RowTapes

/-- Complete declaration of `Paper36.RowTapes.weissman_arbitrary_prior`; source support: S5.Thmtheorem8. -/
theorem weissman_arbitrary_prior : ∀ [Nonempty S]
    (external : ExternalCategoricalConcentration (S := S))
    (row : M → Law S) (hrow : ∀ s, Measurable (fun m => (row m).mass s))
    (latent : Ω → M) (hl : Measurable latent) (n : ℕ) (hn : 0 < n)
    (sample : Ω → Fin n → S) (hs : AEMeasurable sample μ)
    (hcond : condDistrib sample latent μ =ᵐ[μ.map latent] iidKernel row hrow n)
    (L : ℝ) (hL : 0 ≤ L),
    μ {ω | Real.sqrt (L / (2 * n)) < tv (empirical hn (sample ω)) (row (latent ω))} ≤
      ENNReal.ofReal (((2 : ℝ) ^ Fintype.card S - 2) * Real.exp (-L)) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories
open scoped ENNReal
variable {S : Type*} [Fintype S] [MeasurableSpace S] [DiscreteMeasurableSpace S] [DecidableEq S] [Nonempty S]
variable {Row M Hist Ω W : Type*} [Fintype Row] [MeasurableSpace M] [StandardBorelSpace M] [Nonempty M] [MeasurableSpace Hist] {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W]

open Paper36.RowTapes

/-- Complete declaration of `Paper36.RowTapes.current_kl_failure_bound`; source support: S5.Thmtheorem5. -/
theorem current_kl_failure_bound : ∀ (external : ExternalCategoricalConcentration (S := S))
    (row : M → Row → Law S) (hrow : ∀ r s, Measurable (fun m => (row m r).mass s))
    (N : Hist → Row → ℕ) (hN : ∀ r, Measurable (fun h => N h r))
    (observed : Hist → Row → Law S) (ho : ∀ r s, Measurable (fun h => (observed h r).mass s))
    (history : Ω → Hist) (hh : AEMeasurable history μ)
    (latent sampled : Ω → M) (hl : Measurable latent) (hs : AEMeasurable sampled μ)
    (hpost : condDistrib latent history μ =ᵐ[μ.map history] condDistrib sampled history μ)
    (tape : Ω → Row → ℕ → S) (ht : ∀ r n, Measurable (fun ω => tape ω r n))
    (hcond : ∀ r n, condDistrib (fun ω => (fun i : Fin n => tape ω r i.val)) latent μ =ᵐ[μ.map latent]
      iidKernel (fun m => row m r) (hrow r) n)
    (hobs : ∀ ω r (hn : 0 < N (history ω) r), observed (history ω) r =
      empirical hn (fun i : Fin (N (history ω) r) => tape ω r i.val))
    (T : ℕ) (hcount : ∀ ω r, N (history ω) r ≤ T) {budget : ℝ} (hb : 1 ≤ budget),
    μ {ω | (history ω, latent ω) ∉ currentKLSet row N observed (klThreshold (Fintype.card S) T budget)} ≤
      (Fintype.card Row : ℝ≥0∞) * T * ENNReal.ofReal (1 / budget) ∧
    μ {ω | (history ω, sampled ω) ∉ currentKLSet row N observed (klThreshold (Fintype.card S) T budget)} ≤
      (Fintype.card Row : ℝ≥0∞) * T * ENNReal.ofReal (1 / budget) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories
open scoped ENNReal
variable {S : Type*} [Fintype S] [MeasurableSpace S] [DiscreteMeasurableSpace S] [DecidableEq S] [Nonempty S]
variable {Row M Hist Ω W : Type*} [Fintype Row] [MeasurableSpace M] [StandardBorelSpace M] [Nonempty M] [MeasurableSpace Hist] {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W]

open Paper36.RowTapes

/-- Complete declaration of `Paper36.RowTapes.current_hellinger_radius`; source support: S5.Thmtheorem5. -/
theorem current_hellinger_radius : ∀ (row : M → Row → Law S) (N : Hist → Row → ℕ)
    (observed : Hist → Row → Law S) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (history : Ω → Hist) (latent sampled : Ω → M) (ω : Ω)
    (htrue : (history ω, latent ω) ∈ currentKLSet row N observed Λ)
    (hsample : (history ω, sampled ω) ∈ currentKLSet row N observed Λ)
    (r : Row) (hn : 0 < N (history ω) r),
    hellingerSq (row (latent ω) r) (row (sampled ω) r) ≤ 2 * Λ / N (history ω) r := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories
open scoped ENNReal
variable {S : Type*} [Fintype S] [MeasurableSpace S] [DiscreteMeasurableSpace S] [DecidableEq S] [Nonempty S]
variable {Row M Hist Ω W : Type*} [Fintype Row] [MeasurableSpace M] [StandardBorelSpace M] [Nonempty M] [MeasurableSpace Hist] {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W]

open Paper36.RowTapes

/-- Complete declaration of `Paper36.RowTapes.all_episodes_kl_failure_bound`; source support: S5.Thmtheorem6. -/
theorem all_episodes_kl_failure_bound : ∀ {Episode : Type*} [Fintype Episode]
    (external : ExternalCategoricalConcentration (S := S))
    (row : M → Row → Law S) (hrow : ∀ r s, Measurable (fun m => (row m r).mass s))
    (N : Hist → Row → ℕ) (hN : ∀ r, Measurable (fun h => N h r))
    (observed : Hist → Row → Law S) (ho : ∀ r s, Measurable (fun h => (observed h r).mass s))
    (history : Episode → Ω → Hist) (hh : ∀ k, AEMeasurable (history k) μ)
    (latent : Ω → M) (sampled : Episode → Ω → M)
    (hl : Measurable latent) (hs : ∀ k, AEMeasurable (sampled k) μ)
    (hpost : ∀ k, condDistrib latent (history k) μ =ᵐ[μ.map (history k)]
      condDistrib (sampled k) (history k) μ)
    (tape : Ω → Row → ℕ → S) (ht : ∀ r n, Measurable (fun ω => tape ω r n))
    (hcond : ∀ r n, condDistrib (fun ω => (fun i : Fin n => tape ω r i.val)) latent μ =ᵐ[μ.map latent]
      iidKernel (fun m => row m r) (hrow r) n)
    (hobs : ∀ k ω r (hn : 0 < N (history k ω) r), observed (history k ω) r =
      empirical hn (fun i : Fin (N (history k ω) r) => tape ω r i.val))
    (T : ℕ) (hcount : ∀ k ω r, N (history k ω) r ≤ T) {budget : ℝ} (hb : 1 ≤ budget),
    μ ((⋃ i : Row × Fin T, {ω | latent ω ∉ tapeKLBall row tape
      (klThreshold (Fintype.card S) T budget) ω i.1 (i.2.val+1)}) ∪
      ⋃ k, {ω | (history k ω, sampled k ω) ∉
        currentKLSet row N observed (klThreshold (Fintype.card S) T budget)}) ≤
      (1 + (Fintype.card Episode : ℝ≥0∞)) * (Fintype.card Row : ℝ≥0∞) * T *
        ENNReal.ofReal (1 / budget) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories
open scoped ENNReal
variable {S : Type*} [Fintype S] [MeasurableSpace S] [DiscreteMeasurableSpace S] [DecidableEq S] [Nonempty S]
variable {Row M Hist Ω W : Type*} [Fintype Row] [MeasurableSpace M] [StandardBorelSpace M] [Nonempty M] [MeasurableSpace Hist] {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W]

open Paper36.RowTapes

/-- Complete declaration of `Paper36.RowTapes.current_tv_failure_bound`; source support: S5.Thmtheorem8. -/
theorem current_tv_failure_bound : ∀ (external : ExternalCategoricalConcentration (S := S))
    (row : M → Row → Law S) (hrow : ∀ r s, Measurable (fun m => (row m r).mass s))
    (N : Hist → Row → ℕ) (hN : ∀ r, Measurable (fun h => N h r))
    (observed : Hist → Row → Law S) (ho : ∀ r s, Measurable (fun h => (observed h r).mass s))
    (history : Ω → Hist) (hh : AEMeasurable history μ)
    (latent sampled : Ω → M) (hl : Measurable latent) (hs : AEMeasurable sampled μ)
    (hpost : condDistrib latent history μ =ᵐ[μ.map history] condDistrib sampled history μ)
    (tape : Ω → Row → ℕ → S) (ht : ∀ r n, Measurable (fun ω => tape ω r n))
    (hcond : ∀ r n, condDistrib (fun ω => (fun i : Fin n => tape ω r i.val)) latent μ =ᵐ[μ.map latent]
      iidKernel (fun m => row m r) (hrow r) n)
    (hobs : ∀ ω r (hn : 0 < N (history ω) r), observed (history ω) r =
      empirical hn (fun i : Fin (N (history ω) r) => tape ω r i.val))
    (T : ℕ) (hcount : ∀ ω r, N (history ω) r ≤ T) {budget : ℝ} (hb : 1 ≤ budget),
    μ {ω | (history ω, latent ω) ∉ currentTVSet row N observed (tvThreshold (Fintype.card S) budget)} ≤
      (Fintype.card Row : ℝ≥0∞) * T * ENNReal.ofReal (1 / budget) ∧
    μ {ω | (history ω, sampled ω) ∉ currentTVSet row N observed (tvThreshold (Fintype.card S) budget)} ≤
      (Fintype.card Row : ℝ≥0∞) * T * ENNReal.ofReal (1 / budget) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories
open scoped ENNReal
variable {S : Type*} [Fintype S] [MeasurableSpace S] [DiscreteMeasurableSpace S] [DecidableEq S] [Nonempty S]
variable {Row M Hist Ω W : Type*} [Fintype Row] [MeasurableSpace M] [StandardBorelSpace M] [Nonempty M] [MeasurableSpace Hist] {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W]

open Paper36.RowTapes

/-- Complete declaration of `Paper36.RowTapes.current_tv_radius`; source support: S5.Thmtheorem8. -/
theorem current_tv_radius : ∀ (row : M → Row → Law S) (N : Hist → Row → ℕ)
    (observed : Hist → Row → Law S) {L : ℝ} (hL : 0 ≤ L)
    (history : Ω → Hist) (latent sampled : Ω → M) (ω : Ω)
    (htrue : (history ω, latent ω) ∈ currentTVSet row N observed L)
    (hsample : (history ω, sampled ω) ∈ currentTVSet row N observed L)
    (r : Row) (hn : 0 < N (history ω) r),
    tv (row (latent ω) r) (row (sampled ω) r) ≤ Real.sqrt (2 * L / N (history ω) r) := by
  sorry

end

end P36Contract.RowTapes

namespace P36Contract.Scaling

section
open Filter Asymptotics

open Paper36.Scaling

/-- Complete declaration of `Paper36.Scaling.target_log_sqrt_bound`; source support: S4.Thmtheorem2. -/
theorem target_log_sqrt_bound : ∀ {c A ν M : ℝ} (hc : 0 ≤ c) (hA : 0 < A)
    (hM : 0 < M) (hν : 0 ≤ ν) {n : ℕ} (hn : 1 ≤ n),
    Target.target c A ν M n ≤ coefficient c A ν M * Real.sqrt (n : ℝ) *
      (1 + Real.log (n : ℝ)) := by
  sorry

end

section
open Filter Asymptotics

open Paper36.Scaling

/-- Complete declaration of `Paper36.Scaling.target_isBigO`; source support: S4.Thmtheorem2. -/
theorem target_isBigO : ∀ {c A ν M : ℝ} (hc : 0 ≤ c) (hA : 0 < A)
    (hM : 0 < M) (hν : 0 ≤ ν),
    (fun n : ℕ => Target.target c A ν M n) =O[atTop]
      (fun n : ℕ => Real.sqrt (n : ℝ) * (1 + Real.log (n : ℝ))) := by
  sorry

end

end P36Contract.Scaling

namespace P36Contract.Simulation

section
open Paper36.CVaR
variable {S A : Type*} [Fintype S] [Fintype A]

open Paper36.Simulation

/-- Complete declaration of `Paper36.Simulation.distorted_simulation_full`; source support: S5.Thmtheorem3. -/
theorem distorted_simulation_full : ∀ (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (π : Policy S A) (p q : Kernel S A)
    (H : ℕ) (s₀ : S),
    let d := occupancy (adverseKernel α ha ha1 c π p H) (dirac s₀)
    risk α c π p H 0 s₀-risk α c π q H 0 s₀ ≤
      ∑ h ∈ Finset.range H, expect (d h).mass (epsilon α c π p q H h) := by
  sorry

end

section
open Paper36.CVaR
variable {S A : Type*} [Fintype S] [Fintype A]

open Paper36.Simulation

/-- Complete declaration of `Paper36.Simulation.distorted_action_domination`; source support: S5.Thmtheorem4. -/
theorem distorted_action_domination : ∀ (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (π : Policy S A) (p : Kernel S A)
    (H h : ℕ) (s₀ s : S) (a : A),
    (occupancy (adverseKernel α ha ha1 c π p H) (dirac s₀) h).mass s * (π h s).mass a ≤
      (α⁻¹)^h * ((occupancy (nominal π p) (dirac s₀) h).mass s * (π h s).mass a) := by
  sorry

end

section
open Paper36.CVaR
variable {S A : Type*} [Fintype S] [Fintype A]

open Paper36.Simulation

/-- Complete declaration of `Paper36.Simulation.distorted_simulation_tv`; source support: S5.Thmtheorem3. -/
theorem distorted_simulation_tv : ∀ (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1)
    (π : Policy S A) (p q : Kernel S A) (H : ℕ) (s₀ : S),
    let d := occupancy (adverseKernel α ha ha1 c π p (H+1)) (dirac s₀)
    risk α c π p (H+1) 0 s₀-risk α c π q (H+1) 0 s₀ ≤
      ∑ h ∈ Finset.range H, ((H-h : ℕ) : ℝ)/α *
        ∑ s, (d h).mass s * ∑ a, (π h s).mass a * tv (p s a) (q s a) := by
  sorry

end

section
open Paper36.CVaR
variable {S A : Type*} [Fintype S] [Fintype A]

open Paper36.Simulation

/-- Complete declaration of `Paper36.Simulation.uniform_fixed_policy_perturbation`; source support: A3.Thmtheorem1, A3.Thmtheorem2. -/
theorem uniform_fixed_policy_perturbation : ∀ [Nonempty S] [Nonempty A]
    (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1)
    (π : Policy S A) (p q : Kernel S A) (n h : ℕ) (s : S),
    |risk α c π p n h s-risk α c π q n h s| ≤
      (n : ℝ)*((n : ℝ)-1)/(2*α)*maxRowTV p q := by
  sorry

end

section
open Paper36.CVaR
variable {S A : Type*} [Fintype S] [Fintype A]

open Paper36.Simulation

/-- Complete declaration of `Paper36.Simulation.lemma_5_3`; source support: S5.Thmtheorem3. -/
theorem lemma_5_3 : ∀ (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1)
    (π : Policy S A) (p q : Kernel S A) (H : ℕ) (s₀ : S),
    ∃ d : ℕ → Law S, (d 0).mass s₀ = 1 ∧
      (risk α c π p (H+1) 0 s₀-risk α c π q (H+1) 0 s₀ ≤
        ∑ h ∈ Finset.range H, expect (d h).mass (epsilon α c π p q (H+1) h)) ∧
      (risk α c π p (H+1) 0 s₀-risk α c π q (H+1) 0 s₀ ≤
        ∑ h ∈ Finset.range H, ((H-h : ℕ) : ℝ)/α *
          ∑ s, (d h).mass s * ∑ a, (π h s).mass a * tv (p s a) (q s a)) ∧
      (∀ h s a, (d h).mass s*(π h s).mass a ≤
        (α⁻¹)^h*((occupancy (nominal π p) (dirac s₀) h).mass s*(π h s).mass a)) := by
  sorry

end

end P36Contract.Simulation

namespace P36Contract.SourceBank

section
open Paper36.Regularity Paper36.Nested Paper36.Algorithm
variable {S A Ω : Type*} [Fintype S] [Fintype A] [instNonemptyA : Nonempty A]

open Paper36.SourceBank

/-- Complete declaration of `Paper36.SourceBank.calibration_count`; source support: S4.Thmtheorem2. -/
include instNonemptyA in
theorem calibration_count : ∀ (α τ Δ : ℝ) (hα : 0 < α) (hΔ : 0 < Δ) (hτ : 0 ≤ τ)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (H : ℕ) (hH : 1 ≤ H) (s₁ : S) (Q : Set (Kernel S A))
    (hgap : ∀ q ∈ Q, minimumRisk α c H 0 s₁ q ≤ τ - Δ)
    (sample : ℕ → Ω → Kernel S A) (ω : Ω) (hsample : ∀ n, sample n ω ∈ Q) (K : ℕ),
    (Bank.count (target (S := S) (A := A) α H)
      (fun j => deposits α τ c H s₁ sample j ω) K : ℝ) ≤
      min (K : ℝ) ((target (S := S) (A := A) α H K + τ)/Δ) := by
  sorry

end

section
open Paper36.Regularity Paper36.Nested Paper36.Algorithm
variable {S A Ω : Type*} [Fintype S] [Fintype A] [instNonemptyA : Nonempty A]

open Paper36.SourceBank

/-- Complete declaration of `Paper36.SourceBank.bank_deficit`; source support: S4.Thmtheorem2. -/
include instNonemptyA in
theorem bank_deficit : ∀ (α τ Δ : ℝ) (hα : 0 < α) (hΔ : 0 < Δ)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (H : ℕ) (hH : 1 ≤ H) (s₁ : S) (Q : Set (Kernel S A))
    (hgap : ∀ q ∈ Q, minimumRisk α c H 0 s₁ q ≤ τ - Δ)
    (sample : ℕ → Ω → Kernel S A) (ω : Ω) (hsample : ∀ n, sample n ω ∈ Q) (K : ℕ),
    target (S := S) (A := A) α H K -
      Bank.bank (target (S := S) (A := A) α H) (fun j => deposits α τ c H s₁ sample j ω) K ≤
      residual (S := S) (A := A) α Δ H := by
  sorry

end

section
open Paper36.Regularity Paper36.Nested Paper36.Algorithm
variable {S A Ω : Type*} [Fintype S] [Fintype A] [instNonemptyA : Nonempty A]

open Paper36.SourceBank

/-- Complete declaration of `Paper36.SourceBank.calibration_sparse`; source support: S4.Thmtheorem2. -/
include instNonemptyA in
theorem calibration_sparse : ∀ (α τ Δ : ℝ) (hα : 0 < α) (hΔ : 0 < Δ) (hτ : 0 ≤ τ)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (H : ℕ) (hH : 1 ≤ H) (s₁ : S) (Q : Set (Kernel S A))
    (hgap : ∀ q ∈ Q, minimumRisk α c H 0 s₁ q ≤ τ - Δ)
    (sample : ℕ → Ω → Kernel S A) (ω : Ω) (hsample : ∀ n, sample n ω ∈ Q),
    Filter.Tendsto (fun K : ℕ =>
      (Bank.count (target (S := S) (A := A) α H)
        (fun j => deposits α τ c H s₁ sample j ω) K : ℝ)/(K : ℝ))
      Filter.atTop (nhds 0) := by
  sorry

end

section
open Paper36.Regularity Paper36.Nested Paper36.Algorithm
variable {S A Ω : Type*} [Fintype S] [Fintype A] [instNonemptyA : Nonempty A]

open Paper36.SourceBank

/-- Complete declaration of `Paper36.SourceBank.horizon_one_target`; source support: S4.Thmtheorem2. -/
theorem horizon_one_target : ∀ (α : ℝ),
    target (S := S) (A := A) α 1 = fun _ => 0 := by
  sorry

end

end P36Contract.SourceBank

namespace P36Contract.SourceEndpoints

section
open MeasureTheory Paper36.Regularity Paper36.Nested Paper36.Algorithm
variable {S A Ω : Type*} [Fintype S] [Fintype A] [Nonempty A]

open Paper36.SourceEndpoints

/-- Complete declaration of `Paper36.SourceEndpoints.horizon_one_any_prior`; source support: S4.Thmtheorem2. -/
theorem horizon_one_any_prior : ∀ [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {α τ : ℝ} {c r : ℕ → S → A → ℝ} {s₁ : S} {Q : Set (Kernel S A)}
    (O : Oracles α c r 1 s₁ τ Q)
    (sample : ℕ → Ω → Kernel S A) (latent : Ω → Kernel S A)
    (hsupport : ∀ᵐ ω ∂μ, latent ω ∈ Q ∧ ∀ n, sample n ω ∈ Q) (K : ℕ),
    ((∫ ω, ∑ n ∈ Finset.range K,
      (risk α c (selected O (SourceBank.target (S := S) (A := A) α 1) sample n ω)
        (latent ω) 1 0 s₁ - τ) ∂μ) ≤ 0) ∧
    ((∫ ω, ∑ n ∈ Finset.range K,
      (constrainedValue α c r 1 s₁ τ (latent ω) -
        reward r (selected O (SourceBank.target (S := S) (A := A) α 1) sample n ω)
          (latent ω) 1 0 s₁) ∂μ) = 0) ∧
    (∀ ω, Bank.bank (SourceBank.target (S := S) (A := A) α 1)
      (fun j => deposits α τ c 1 s₁ sample j ω) K = 0 ∧
      Bank.count (SourceBank.target (S := S) (A := A) α 1)
        (fun j => deposits α τ c 1 s₁ sample j ω) K = 0) := by
  sorry

end

end P36Contract.SourceEndpoints

namespace P36Contract.StageCalibration

section
open Set Paper36.CVaR Paper36.Simulation MeasureTheory
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]

open Paper36.StageCalibration

/-- Complete declaration of `Paper36.StageCalibration.exists_deterministic_minimizer`; source support: S4.Thmtheorem1. -/
theorem exists_deterministic_minimizer : ∀ (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (q : Kernel S A) (n h : ℕ),
    ∃ π : Policy S A, Deterministic π ∧ ∀ s, StageRisk.risk β c π q n h s = dp β c q n h s := by
  sorry

end

section
open Set Paper36.CVaR Paper36.Simulation MeasureTheory
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]

open Paper36.StageCalibration

/-- Complete declaration of `Paper36.StageCalibration.risk_eq_compact`; source support: S4.Thmtheorem1. -/
theorem risk_eq_compact : ∀ (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1)
    (π : Nested.Policy S A) (q : Nested.Kernel S A) (n h : ℕ) (s : S),
    StageRisk.risk β c (RiskBridge.ofPolicy π) (RiskBridge.ofKernel q) n h s =
      compactRisk β c π q n h s := by
  sorry

end

section
open Set Paper36.CVaR Paper36.Simulation MeasureTheory
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]

open Paper36.StageCalibration

/-- Complete declaration of `Paper36.StageCalibration.continuous_actualRisk`; source support: S2.Thmtheorem1. -/
theorem continuous_actualRisk : ∀ (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1)
    (n h : ℕ) (s : S),
    Continuous (fun p : Nested.Policy S A × Nested.Kernel S A =>
      StageRisk.risk β c (RiskBridge.ofPolicy p.1) (RiskBridge.ofKernel p.2) n h s) := by
  sorry

end

section
open Set Paper36.CVaR Paper36.Simulation MeasureTheory
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]

open Paper36.StageCalibration

/-- Complete declaration of `Paper36.StageCalibration.continuous_minimumRisk`; source support: S2.Thmtheorem1. -/
theorem continuous_minimumRisk : ∀ (β : ℕ → ℝ) (c : ℕ → S → A → ℝ)
    (n h : ℕ) (s : S),
    Continuous (minimumRisk β c n h s : Nested.Kernel S A → ℝ) := by
  sorry

end

section
open Set Paper36.CVaR Paper36.Simulation MeasureTheory
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]

open Paper36.StageCalibration

/-- Complete declaration of `Paper36.StageCalibration.minimumRisk_eq_dp`; source support: S4.Thmtheorem1. -/
theorem minimumRisk_eq_dp : ∀ (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1)
    (q : Nested.Kernel S A) (n h : ℕ) (s : S),
    minimumRisk β c n h s q = dp β c (RiskBridge.ofKernel q) n h s := by
  sorry

end

section
open Set Paper36.CVaR Paper36.Simulation MeasureTheory
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]

open Paper36.StageCalibration

/-- Complete declaration of `Paper36.StageCalibration.exists_constrained_optimum`; source support: S4.Thmtheorem2. -/
theorem exists_constrained_optimum : ∀ (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1)
    (n h : ℕ) (s : S) (q : Nested.Kernel S A) (τ : ℝ)
    (hne : ∃ π : Nested.Policy S A,
      StageRisk.risk β c (RiskBridge.ofPolicy π) (RiskBridge.ofKernel q) n h s ≤ τ),
    ∃ π : Nested.Policy S A,
      StageRisk.risk β c (RiskBridge.ofPolicy π) (RiskBridge.ofKernel q) n h s ≤ τ ∧
      ∀ π', StageRisk.risk β c (RiskBridge.ofPolicy π') (RiskBridge.ofKernel q) n h s ≤ τ →
        Nested.reward r π' q n h s ≤ Nested.reward r π q n h s := by
  sorry

end

section
open Set Paper36.CVaR Paper36.Simulation MeasureTheory
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] [MeasurableSpace (Paper36.Nested.Kernel S A)]

open Paper36.StageCalibration

/-- Complete declaration of `Paper36.StageCalibration.prior_support_uniform_gap`; source support: S2.Thmtheorem1. -/
theorem prior_support_uniform_gap : ∀ (μ : Measure (Nested.Kernel S A)) [IsProbabilityMeasure μ]
    (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1) (H : ℕ)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1) (s₁ : S)
    (τ : ℝ) (hstrict : ∀ q ∈ μ.support, ∃ π : Policy S A,
      StageRisk.risk β c π (RiskBridge.ofKernel q) H 0 s₁ < τ),
    0 < τ - sSup (minimumRisk β c H 0 s₁ '' μ.support) ∧
      ∀ q ∈ μ.support, τ - sSup (minimumRisk β c H 0 s₁ '' μ.support) ≤
        τ - dp β c (RiskBridge.ofKernel q) H 0 s₁ := by
  sorry

end

section
open Set Paper36.CVaR Paper36.Simulation MeasureTheory
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] [MeasurableSpace (Paper36.Nested.Kernel S A)]

open Paper36.StageCalibration

/-- Complete declaration of `Paper36.StageCalibration.calibration_deposit_bounds`; source support: S4.Thmtheorem2. -/
theorem calibration_deposit_bounds : ∀ (μ : Measure (Nested.Kernel S A)) [IsProbabilityMeasure μ]
    (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1) (H : ℕ)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1) (s₁ : S)
    (τ : ℝ) (hstrict : ∀ q ∈ μ.support, ∃ π : Policy S A,
      StageRisk.risk β c π (RiskBridge.ofKernel q) H 0 s₁ < τ),
    0 < uniformGap μ β c H s₁ τ ∧ ∀ q ∈ μ.support,
      uniformGap μ β c H s₁ τ ≤ τ-dp β c (RiskBridge.ofKernel q) H 0 s₁ ∧
      τ-dp β c (RiskBridge.ofKernel q) H 0 s₁ ≤ τ := by
  sorry

end

end P36Contract.StageCalibration

namespace P36Contract.StageCharging

section
open Paper36.CVaR Paper36.Simulation Paper36.HybridCharging
variable {S A : Type*} [Fintype S] [Fintype A]

open Paper36.StageCharging

/-- Complete declaration of `Paper36.StageCharging.actual_hybrid_stage`; source support: S5.Thmtheorem2. -/
theorem actual_hybrid_stage : ∀ (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1)
    (π : ℕ → Policy S A) (p : Kernel S A) (q : ℕ → Kernel S A)
    (s₀ : S) (N : ℕ → S × A → ℕ) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (H k h : ℕ) (hh : h < H)
    (hrow : ∀ s a, H+1 ≤ N k (s,a) →
      hellingerSq (p s a) (q k s a) ≤ 2 * Λ / N k (s,a)),
    let d := occupancy (StageRisk.adverseKernel β hβ c (π k) p (H+1)) (dirac s₀) h
    expect d.mass (StageRisk.localError β c (π k) p (q k) (H-h) h) ≤
      Weights.stagew β (H+1) * nominalLow π p s₀ N H k h +
      4 * Real.sqrt (Λ * stageWeight β H h * nominalHigh π p s₀ N H k h) := by
  sorry

end

section
open Paper36.CVaR Paper36.Simulation Paper36.HybridCharging
variable {S A : Type*} [Fintype S] [Fintype A]

open Paper36.StageCharging

/-- Complete declaration of `Paper36.StageCharging.risk_hybrid_sum_bound_stage`; source support: S5.Thmtheorem2. -/
theorem risk_hybrid_sum_bound_stage : ∀ (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1)
    (π : ℕ → Policy S A) (p : Kernel S A) (q : ℕ → Kernel S A)
    (s₀ : S) (N : ℕ → S × A → ℕ) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (K H : ℕ) (hrow : ∀ k, k < K → ∀ s a, H+1 ≤ N k (s,a) →
      hellingerSq (p s a) (q k s a) ≤ 2 * Λ / N k (s,a)),
    (∑ k ∈ Finset.range K,
      (StageRisk.risk β c (π k) p (H+1) 0 s₀ - StageRisk.risk β c (π k) (q k) (H+1) 0 s₀)) ≤
      Weights.stagew β (H+1) * Ylo π p s₀ N K H +
      4 * Real.sqrt (Weights.stageWsq β (H+1)) * Real.sqrt (Λ * (K : ℝ) * Yhi π p s₀ N K H) := by
  sorry

end

section
open Paper36.CVaR Paper36.Simulation Paper36.HybridCharging
variable {S A : Type*} [Fintype S] [Fintype A]

open Paper36.StageCharging

/-- Complete declaration of `Paper36.StageCharging.masked_risk_hybrid_sum_bound_stage`; source support: S5.Thmtheorem5. -/
theorem masked_risk_hybrid_sum_bound_stage : ∀ (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1)
    (π : ℕ → Policy S A) (p : Kernel S A) (q : ℕ → Kernel S A)
    (s₀ : S) (N : ℕ → S × A → ℕ) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (K H : ℕ) (good : ℕ → Prop) [DecidablePred good]
    (hrow : ∀ k, k < K → good k → ∀ s a, H+1 ≤ N k (s,a) →
      hellingerSq (p s a) (q k s a) ≤ 2 * Λ / N k (s,a)),
    (∑ k ∈ Finset.range K, if good k then
      (StageRisk.risk β c (π k) p (H+1) 0 s₀ - StageRisk.risk β c (π k) (q k) (H+1) 0 s₀) else 0) ≤
      Weights.stagew β (H+1) * Ylo π p s₀ N K H +
      4 * Real.sqrt (Weights.stageWsq β (H+1)) * Real.sqrt (Λ * (K : ℝ) * Yhi π p s₀ N K H) := by
  sorry

end

end P36Contract.StageCharging

namespace P36Contract.StageRisk

section
open Paper36.CVaR Paper36.Simulation
variable {S A : Type*} [Fintype S] [Fintype A]

open Paper36.StageRisk

/-- Complete declaration of `Paper36.StageRisk.occupancy_domination`; source support: S5.Thmtheorem4. -/
theorem occupancy_domination : ∀ (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (π : Policy S A) (p : Kernel S A)
    (H h : ℕ) (s₀ s : S),
    (occupancy (adverseKernel β hβ c π p H) (dirac s₀) h).mass s ≤
      (Weights.prefixMass β h)⁻¹ * (occupancy (nominal π p) (dirac s₀) h).mass s := by
  sorry

end

section
open Paper36.CVaR Paper36.Simulation
variable {S A : Type*} [Fintype S] [Fintype A]

open Paper36.StageRisk

/-- Complete declaration of `Paper36.StageRisk.distorted_action_domination`; source support: S5.Thmtheorem4. -/
theorem distorted_action_domination : ∀ (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (π : Policy S A) (p : Kernel S A)
    (H h : ℕ) (s₀ s : S) (a : A),
    (occupancy (adverseKernel β hβ c π p H) (dirac s₀) h).mass s * (π h s).mass a ≤
      (Weights.prefixMass β h)⁻¹ *
        ((occupancy (nominal π p) (dirac s₀) h).mass s * (π h s).mass a) := by
  sorry

end

section
open Paper36.CVaR Paper36.Simulation
variable {S A : Type*} [Fintype S] [Fintype A]

open Paper36.StageRisk

/-- Complete declaration of `Paper36.StageRisk.distorted_simulation`; source support: S5.Thmtheorem3. -/
theorem distorted_simulation : ∀ (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (π : Policy S A) (p q : Kernel S A) (H : ℕ) (s₀ : S),
    risk β c π p H 0 s₀ - risk β c π q H 0 s₀ ≤
      ∑ h ∈ Finset.range H, expect
        (occupancy (adverseKernel β hβ c π p H) (dirac s₀) h).mass
        (localError β c π p q (H-(h+1)) h) := by
  sorry

end

section
open Paper36.CVaR Paper36.Simulation
variable {S A : Type*} [Fintype S] [Fintype A]

open Paper36.StageRisk

/-- Complete declaration of `Paper36.StageRisk.distorted_simulation_transitions`; source support: S5.Thmtheorem3. -/
theorem distorted_simulation_transitions : ∀ (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (π : Policy S A) (p q : Kernel S A) (H : ℕ) (s₀ : S),
    risk β c π p (H+1) 0 s₀ - risk β c π q (H+1) 0 s₀ ≤
      ∑ h ∈ Finset.range H, expect
        (occupancy (adverseKernel β hβ c π p (H+1)) (dirac s₀) h).mass
        (localError β c π p q (H-h) h) := by
  sorry

end

end P36Contract.StageRisk

namespace P36Contract.Statistical

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation Paper36.Trajectories Paper36.RowTapes Paper36.StatisticalCounts Paper36.Statistical.PosteriorSystem
open scoped ENNReal
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A] [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
variable {Ω Info Model Hist : Type*} [MeasurableSpace Ω] [MeasurableSpace Info] [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model] [MeasurableSpace Hist] {μ : Measure Ω} [IsProbabilityMeasure μ] {T : ℕ} {s₀ : S}
variable {H : ℕ} (E' : EpisodeSystem μ Info S A (H+1) s₀) (P' : Paper36.Statistical.PosteriorSystem (Model := Model) (Hist := Hist) E')

open Paper36.Statistical
open Paper36.Statistical.PosteriorSystem

/-- Complete declaration of `Paper36.Statistical.PosteriorSystem.lemma_5_5`; source support: S5.Thmtheorem5. -/
theorem PosteriorSystem__lemma_5_5 : ∀ (external : ExternalCategoricalConcentration (S := S))
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (c : ℕ → S → A → ℝ)
    (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1) {K : ℕ} (hK : 1 ≤ K),
    (∑ k ∈ Finset.range K, ∫ ω, P'.riskError α c k ω ∂μ) ≤
      Target.confidence (Target.scale (Weights.W α (H+1)) (Fintype.card S) (Fintype.card A))
        (Fintype.card S) (Fintype.card A) (H+1) K * Real.sqrt (K : ℝ) +
      (2 * (Fintype.card S : ℝ) * (Fintype.card A : ℝ) * (H+1) * Weights.w α (H+1) + (H+1 : ℝ)/2) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation Paper36.Trajectories Paper36.RowTapes Paper36.StatisticalCounts Paper36.Statistical.PosteriorSystem
open scoped ENNReal
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A] [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
variable {Ω Info Model Hist : Type*} [MeasurableSpace Ω] [MeasurableSpace Info] [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model] [MeasurableSpace Hist] {μ : Measure Ω} [IsProbabilityMeasure μ] {T : ℕ} {s₀ : S}
variable {H : ℕ} (E' : EpisodeSystem μ Info S A (H+1) s₀) (P' : Paper36.Statistical.PosteriorSystem (Model := Model) (Hist := Hist) E')

open Paper36.Statistical
open Paper36.Statistical.PosteriorSystem

/-- Complete declaration of `Paper36.Statistical.PosteriorSystem.lemma_5_8`; source support: S5.Thmtheorem8. -/
theorem PosteriorSystem__lemma_5_8 : ∀ (external : ExternalCategoricalConcentration (S := S))
    (r : ℕ → S → A → ℝ) (hr : ∀ h s a, 0 ≤ r h s a ∧ r h s a ≤ 1)
    {K : ℕ} (hK : 1 ≤ K),
    (∑ k ∈ Finset.range K, ∫ ω, P'.rewardError r k ω ∂μ) ≤
      8 * (H+1) * Real.sqrt (H+1) * Real.sqrt
        ((Fintype.card S : ℝ) * (Fintype.card A : ℝ) * (K : ℝ) *
          Bounds.rewardLog (Fintype.card S) (Fintype.card A) (H+1) K) + (H+1 : ℝ)/2 := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation Paper36.Trajectories Paper36.RowTapes Paper36.StatisticalCounts Paper36.Statistical.PosteriorSystem
open scoped ENNReal
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A] [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
variable {Ω Info Model Hist : Type*} [MeasurableSpace Ω] [MeasurableSpace Info] [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model] [MeasurableSpace Hist] {μ : Measure Ω} [IsProbabilityMeasure μ] {T : ℕ} {s₀ : S}
variable {H : ℕ} (E' : EpisodeSystem μ Info S A (H+1) s₀) (P' : Paper36.Statistical.PosteriorSystem (Model := Model) (Hist := Hist) E')

open Paper36.Statistical
open Paper36.Statistical.PosteriorSystem

/-- Complete declaration of `Paper36.Statistical.PosteriorSystem.theorem_5_6`; source support: S5.Thmtheorem6. -/
theorem PosteriorSystem__theorem_5_6 : ∀ (external : ExternalCategoricalConcentration (S := S))
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (c : ℕ → S → A → ℝ)
    (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1)
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (hinfo : ∀ k, MeasurableSpace.comap (E'.info k) inferInstance = ℱ k)
    (hpath : ∀ k, Measurable[ℱ (k+1), inferInstance] (E'.path k))
    {K : ℕ} (hK : 1 ≤ K) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1),
    μ.real {ω | Bounds.certificate (Fintype.card S) (Fintype.card A) (H+1)
      (Weights.W α (H+1)) (Weights.w α (H+1)) δ K <
        ∑ k ∈ Finset.range K, P'.riskError α c k ω} ≤ δ := by
  sorry

end

end P36Contract.Statistical

namespace P36Contract.StatisticalCounts

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation Paper36.Trajectories Paper36.StatisticalCounts.EpisodeSystem
open scoped ENNReal
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A] [DecidableEq S] [DecidableEq A]
variable {Ω Info : Type*} [MeasurableSpace Ω] [MeasurableSpace Info] {μ : Measure Ω} [IsProbabilityMeasure μ] {T : ℕ} {s₀ : S} (E : Paper36.StatisticalCounts.EpisodeSystem μ Info S A T s₀)
variable {H : ℕ} (F : Paper36.StatisticalCounts.EpisodeSystem μ Info S A (H+1) s₀)

open Paper36.StatisticalCounts
open Paper36.StatisticalCounts.EpisodeSystem

/-- Complete declaration of `Paper36.StatisticalCounts.EpisodeSystem.integral_totalNominal_le`; source support: S5.Thmtheorem5. -/
theorem EpisodeSystem__integral_totalNominal_le : ∀ (w : Weight (Info := Info) (S := S) (A := A))
    (hw : ∀ k row, Measurable (fun i => w k i row))
    (hb : ∀ k i row, 0 ≤ w k i row ∧ w k i row ≤ 1) (K L : ℕ) (hLT : L ≤ T),
    (∫ ω, E.totalNominal w K L ω ∂μ) ≤ ∫ ω, E.totalRealized w K ω ∂μ := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation Paper36.Trajectories Paper36.StatisticalCounts.EpisodeSystem
open scoped ENNReal
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A] [DecidableEq S] [DecidableEq A]
variable {Ω Info : Type*} [MeasurableSpace Ω] [MeasurableSpace Info] {μ : Measure Ω} [IsProbabilityMeasure μ] {T : ℕ} {s₀ : S} (E : Paper36.StatisticalCounts.EpisodeSystem μ Info S A T s₀)
variable {H : ℕ} (F : Paper36.StatisticalCounts.EpisodeSystem μ Info S A (H+1) s₀)

open Paper36.StatisticalCounts
open Paper36.StatisticalCounts.EpisodeSystem

/-- Complete declaration of `Paper36.StatisticalCounts.EpisodeSystem.conditional_realizedEpisode`; source support: A3.Thmtheorem3. -/
theorem EpisodeSystem__conditional_realizedEpisode : ∀ (w : Weight (Info := Info) (S := S) (A := A))
    (hw : ∀ k row, Measurable (fun i => w k i row))
    (hb : ∀ k i row, 0 ≤ w k i row ∧ w k i row ≤ 1) (k : ℕ),
    μ[E.realizedEpisode w k | MeasurableSpace.comap (E.info k) inferInstance] =ᵐ[μ]
      E.nominalEpisode w T k := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation Paper36.Trajectories Paper36.StatisticalCounts.EpisodeSystem
open scoped ENNReal
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A] [DecidableEq S] [DecidableEq A]
variable {Ω Info : Type*} [MeasurableSpace Ω] [MeasurableSpace Info] {μ : Measure Ω} [IsProbabilityMeasure μ] {T : ℕ} {s₀ : S} (E : Paper36.StatisticalCounts.EpisodeSystem μ Info S A T s₀)
variable {H : ℕ} (F : Paper36.StatisticalCounts.EpisodeSystem μ Info S A (H+1) s₀)

open Paper36.StatisticalCounts
open Paper36.StatisticalCounts.EpisodeSystem

/-- Complete declaration of `Paper36.StatisticalCounts.EpisodeSystem.integral_Ylo_le`; source support: S5.Thmtheorem5. -/
theorem EpisodeSystem__integral_Ylo_le : ∀ (K : ℕ),
    (∫ ω, HybridCharging.Ylo (F.selectedPolicy ω) (F.latent ω) s₀ (F.frozenCounts ω) K H ∂μ) ≤
      2*(Fintype.card (S × A):ℝ)*(H+1) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation Paper36.Trajectories Paper36.StatisticalCounts.EpisodeSystem
open scoped ENNReal
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A] [DecidableEq S] [DecidableEq A]
variable {Ω Info : Type*} [MeasurableSpace Ω] [MeasurableSpace Info] {μ : Measure Ω} [IsProbabilityMeasure μ] {T : ℕ} {s₀ : S} (E : Paper36.StatisticalCounts.EpisodeSystem μ Info S A T s₀)
variable {H : ℕ} (F : Paper36.StatisticalCounts.EpisodeSystem μ Info S A (H+1) s₀)

open Paper36.StatisticalCounts
open Paper36.StatisticalCounts.EpisodeSystem

/-- Complete declaration of `Paper36.StatisticalCounts.EpisodeSystem.integral_Yhi_le`; source support: S5.Thmtheorem5. -/
theorem EpisodeSystem__integral_Yhi_le : ∀ {K : ℕ} (hK : 1 ≤ K),
    (∫ ω, HybridCharging.Yhi (F.selectedPolicy ω) (F.latent ω) s₀ (F.frozenCounts ω) K H ∂μ) ≤
      2*(Fintype.card (S × A):ℝ)*Real.log (Real.exp 1*(K:ℝ)*(H+1)) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation Paper36.Trajectories Paper36.StatisticalCounts.EpisodeSystem
open scoped ENNReal
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A] [DecidableEq S] [DecidableEq A]
variable {Ω Info : Type*} [MeasurableSpace Ω] [MeasurableSpace Info] {μ : Measure Ω} [IsProbabilityMeasure μ] {T : ℕ} {s₀ : S} (E : Paper36.StatisticalCounts.EpisodeSystem μ Info S A T s₀)
variable {H : ℕ} (F : Paper36.StatisticalCounts.EpisodeSystem μ Info S A (H+1) s₀)

open Paper36.StatisticalCounts
open Paper36.StatisticalCounts.EpisodeSystem

/-- Complete declaration of `Paper36.StatisticalCounts.EpisodeSystem.integral_Ysqrt_le`; source support: S5.Thmtheorem8. -/
theorem EpisodeSystem__integral_Ysqrt_le : ∀ (K : ℕ),
    (∫ ω, HybridCharging.Ysqrt (F.selectedPolicy ω) (F.latent ω) s₀ (F.frozenCounts ω) K H ∂μ) ≤
      3*Real.sqrt ((Fintype.card (S × A):ℝ)*(K:ℝ)*(H+1)) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation Paper36.Trajectories Paper36.StatisticalCounts.EpisodeSystem
open scoped ENNReal
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A] [DecidableEq S] [DecidableEq A]
variable {Ω Info : Type*} [MeasurableSpace Ω] [MeasurableSpace Info] {μ : Measure Ω} [IsProbabilityMeasure μ] {T : ℕ} {s₀ : S} (E : Paper36.StatisticalCounts.EpisodeSystem μ Info S A T s₀)
variable {H : ℕ} (F : Paper36.StatisticalCounts.EpisodeSystem μ Info S A (H+1) s₀)

open Paper36.StatisticalCounts
open Paper36.StatisticalCounts.EpisodeSystem

/-- Complete declaration of `Paper36.StatisticalCounts.EpisodeSystem.Ylo_probability_bound`; source support: S5.Thmtheorem6. -/
theorem EpisodeSystem__Ylo_probability_bound : ∀ (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (hinfo : ∀ k, MeasurableSpace.comap (F.info k) inferInstance = ℱ k)
    (hpath : ∀ k, Measurable[ℱ (k+1), inferInstance] (F.path k))
    (K : ℕ) {ell : ℝ} (hell : 0 < ell),
    μ.real {ω | 4*(Fintype.card (S × A):ℝ)*(H+1)+2*(H+1)*ell <
      HybridCharging.Ylo (F.selectedPolicy ω) (F.latent ω) s₀ (F.frozenCounts ω) K H} ≤
      Real.exp (-ell) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation Paper36.Trajectories Paper36.StatisticalCounts.EpisodeSystem
open scoped ENNReal
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A] [DecidableEq S] [DecidableEq A]
variable {Ω Info : Type*} [MeasurableSpace Ω] [MeasurableSpace Info] {μ : Measure Ω} [IsProbabilityMeasure μ] {T : ℕ} {s₀ : S} (E : Paper36.StatisticalCounts.EpisodeSystem μ Info S A T s₀)
variable {H : ℕ} (F : Paper36.StatisticalCounts.EpisodeSystem μ Info S A (H+1) s₀)

open Paper36.StatisticalCounts
open Paper36.StatisticalCounts.EpisodeSystem

/-- Complete declaration of `Paper36.StatisticalCounts.EpisodeSystem.Yhi_probability_bound`; source support: S5.Thmtheorem6. -/
theorem EpisodeSystem__Yhi_probability_bound : ∀ (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (hinfo : ∀ k, MeasurableSpace.comap (F.info k) inferInstance = ℱ k)
    (hpath : ∀ k, Measurable[ℱ (k+1), inferInstance] (F.path k))
    {K : ℕ} (hK : 1 ≤ K) {ell : ℝ} (hell : 0 < ell),
    μ.real {ω | 4*(Fintype.card (S × A):ℝ)*Real.log (Real.exp 1*(K:ℝ)*(H+1))+2*ell <
      HybridCharging.Yhi (F.selectedPolicy ω) (F.latent ω) s₀ (F.frozenCounts ω) K H} ≤
      Real.exp (-ell) := by
  sorry

end

end P36Contract.StatisticalCounts

namespace P36Contract.Trajectories

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation
open scoped ENNReal
universe u
variable {S A X Y : Type u} [Fintype S] [Fintype A]
variable {Ω Info : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace Info]

open Paper36.Trajectories

/-- Complete declaration of `Paper36.Trajectories.expectedVisits_eq_occupancy`; source support: S5.Thmtheorem5. -/
theorem expectedVisits_eq_occupancy : ∀ [DecidableEq S] [DecidableEq A]
    (π : Policy S A) (p : Simulation.Kernel S A) (row : S × A) (H : ℕ) (s₀ : S),
    expectedVisits π p row H 0 s₀ = ∑ h ∈ Finset.range H,
      (occupancy (nominal π p) (dirac s₀) h).mass row.1 * (π h row.1).mass row.2 := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation
open scoped ENNReal
universe u
variable {S A X Y : Type u} [Fintype S] [Fintype A]
variable {Ω Info : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace Info]

open Paper36.Trajectories

/-- Complete declaration of `Paper36.Trajectories.conditional_visitCount_of_trajectoryKernel`; source support: S5.Thmtheorem5. -/
theorem conditional_visitCount_of_trajectoryKernel : ∀ (πOf : Info → Policy S A) (pOf : Info → Simulation.Kernel S A)
    (hπ : ∀ h s a, Measurable (fun i => (πOf i h s).mass a))
    (htrans : ∀ s a t, Measurable (fun i => (pOf i s a).mass t))
    (H : ℕ) (s₀ : S) (info : Ω → Info) (path : Ω → Trajectory S A H)
    (hi : Measurable info) (hp : AEMeasurable path μ)
    (hmodel : condDistrib path info μ =ᵐ[μ.map info]
      trajectoryKernel πOf pOf hπ htrans H s₀) (row : S × A),
    μ[fun ω => (visitCount row H (path ω) : ℝ) |
      MeasurableSpace.comap info inferInstance] =ᵐ[μ]
      fun ω => ∑ h ∈ Finset.range H,
        (occupancy (nominal (πOf (info ω)) (pOf (info ω))) (dirac s₀) h).mass row.1 *
          (πOf (info ω) h row.1).mass row.2 := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation
open scoped ENNReal
universe u
variable {S A X Y : Type u} [Fintype S] [Fintype A]
variable {Ω Info : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace Info]

open Paper36.Trajectories

/-- Complete declaration of `Paper36.Trajectories.weighted_visit_identity`; source support: S5.Thmtheorem5. -/
theorem weighted_visit_identity : ∀ (πOf : Info → Policy S A) (pOf : Info → Simulation.Kernel S A)
    (hπ : ∀ h s a, Measurable (fun i => (πOf i h s).mass a))
    (htrans : ∀ s a t, Measurable (fun i => (pOf i s a).mass t))
    (H : ℕ) (s₀ : S) (info : Ω → Info) (path : Ω → Trajectory S A H)
    (hi : Measurable info) (hp : AEMeasurable path μ)
    (hmodel : condDistrib path info μ =ᵐ[μ.map info]
      trajectoryKernel πOf pOf hπ htrans H s₀)
    (weight : Info → ℝ) (hw : Measurable weight) (hwb : ∀ i, 0 ≤ weight i ∧ weight i ≤ 1)
    (row : S × A),
    (∫ ω, weight (info ω) * nominalVisits (πOf (info ω)) (pOf (info ω)) s₀ H row ∂μ) =
      ∫ ω, weight (info ω) * (visitCount row H (path ω) : ℝ) ∂μ := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation
open scoped ENNReal
universe u
variable {S A X Y : Type u} [Fintype S] [Fintype A]
variable {Ω Info : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace Info]

open Paper36.Trajectories

/-- Complete declaration of `Paper36.Trajectories.weighted_partial_visit_le`; source support: S5.Thmtheorem5. -/
theorem weighted_partial_visit_le : ∀ (πOf : Info → Policy S A) (pOf : Info → Simulation.Kernel S A)
    (hπ : ∀ h s a, Measurable (fun i => (πOf i h s).mass a))
    (htrans : ∀ s a t, Measurable (fun i => (pOf i s a).mass t))
    (H L : ℕ) (hLH : L ≤ H) (s₀ : S) (info : Ω → Info) (path : Ω → Trajectory S A H)
    (hi : Measurable info) (hp : AEMeasurable path μ)
    (hmodel : condDistrib path info μ =ᵐ[μ.map info]
      trajectoryKernel πOf pOf hπ htrans H s₀)
    (weight : Info → ℝ) (hw : Measurable weight) (hwb : ∀ i, 0 ≤ weight i ∧ weight i ≤ 1)
    (row : S × A),
    (∫ ω, weight (info ω) * nominalVisits (πOf (info ω)) (pOf (info ω)) s₀ L row ∂μ) ≤
      ∫ ω, weight (info ω) * (visitCount row H (path ω) : ℝ) ∂μ := by
  sorry

end

end P36Contract.Trajectories

namespace P36Contract.Weights

section

open Paper36.Weights

/-- Complete declaration of `Paper36.Weights.Wsq_lower`; source support: S4.Thmtheorem2, A2.Thmtheorem2. -/
theorem Wsq_lower : ∀ {α : ℝ} (hα : 0 < α) {H : ℕ} (hH : 2 ≤ H),
    4 * (α⁻¹)^(H - 1) ≤ Wsq α H := by
  sorry

end

section

open Paper36.Weights

/-- Complete declaration of `Paper36.Weights.Wsq_upper`; source support: S4.Thmtheorem2, A2.Thmtheorem2. -/
theorem Wsq_upper : ∀ {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (H : ℕ),
    Wsq α H ≤ (H : ℝ)^3 * (α⁻¹)^(H - 1) := by
  sorry

end

section

open Paper36.Weights

/-- Complete declaration of `Paper36.Weights.w_upper`; source support: S4.Thmtheorem2, A2.Thmtheorem2. -/
theorem w_upper : ∀ {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (H : ℕ),
    w α H ≤ (H : ℝ) * (α⁻¹)^(H - 1) := by
  sorry

end

section

open Paper36.Weights

/-- Complete declaration of `Paper36.Weights.expectation_endpoint`; source support: S4.Thmtheorem2, A2.Thmtheorem2. -/
theorem expectation_endpoint : ∀ (H : ℕ),
    Wsq 1 H ≤ (H : ℝ)^3 ∧ w 1 H ≤ H := by
  sorry

end

section

open Paper36.Weights

/-- Complete declaration of `Paper36.Weights.stage_low_coefficient`; source support: A2.Thmtheorem3. -/
theorem stage_low_coefficient : ∀ (α : ℕ → ℝ) (b : ℝ) {h : ℕ} (hh : 1 ≤ h),
    (b / α h) / prefixMass α (h - 1) = b / prefixMass α h := by
  sorry

end

section

open Paper36.Weights

/-- Complete declaration of `Paper36.Weights.stage_high_coefficient`; source support: A2.Thmtheorem3. -/
theorem stage_high_coefficient : ∀ {α : ℕ → ℝ} (b : ℝ) {h : ℕ} (hh : 1 ≤ h)
    (hα : 0 < α h),
    (2 * Real.sqrt 2 * b / Real.sqrt (α h))^2 / prefixMass α (h - 1) =
      8 * b^2 / prefixMass α h := by
  sorry

end

section

open Paper36.Weights

/-- Complete declaration of `Paper36.Weights.w_eq_paper_max`; source support: S4.Thmtheorem2. -/
theorem w_eq_paper_max : ∀ {α : ℝ} (hα : 0 < α) {H : ℕ} (hH : 2 ≤ H),
    w α H = (Finset.Icc 1 (H - 1)).sup'
      (by refine ⟨1, ?_⟩; simp; omega)
      (fun h => ((H - h : ℕ) : ℝ) * (α⁻¹)^h) := by
  sorry

end

end P36Contract.Weights

namespace P36Contract.AdaptiveTapes

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories
open scoped ENNReal
variable {I J S Row : Type*} [Fintype I] [Fintype J] [Fintype S] [Fintype Row] [MeasurableSpace S] [DiscreteMeasurableSpace S]
variable {Hist : Type*}

open Paper36.AdaptiveTapes

/-- Complete declaration of `Paper36.AdaptiveTapes.pop_law`; source support: S5.Thmtheorem5. -/
theorem pop_law : ∀ (P : Row → Law S) (r : Row) (n : ℕ),
    (lawMeasure (stackLaw P (n+1))).map
      (fun tape => (remaining r tape, head r tape)) =
      (lawMeasure (stackLaw P n)).prod (lawMeasure (P r)) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories
open scoped ENNReal
variable {I J S Row : Type*} [Fintype I] [Fintype J] [Fintype S] [Fintype Row] [MeasurableSpace S] [DiscreteMeasurableSpace S]
variable {Hist : Type*}

open Paper36.AdaptiveTapes

/-- Complete declaration of `Paper36.AdaptiveTapes.adaptive_stack_coupling`; source support: S5.Thmtheorem5. -/
theorem adaptive_stack_coupling : ∀ (P : Row → Law S) (choose : Hist → Law Row)
    (update : Hist → Row → S → Hist) (payoff : Hist → ℝ) (n : ℕ) (h : Hist),
    expect (stackLaw P n).mass (tapedValue choose update payoff n h) =
      onlineValue P choose update payoff n h := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories
open scoped ENNReal
variable {I J S Row : Type*} [Fintype I] [Fintype J] [Fintype S] [Fintype Row] [MeasurableSpace S] [DiscreteMeasurableSpace S]
variable {Hist : Type*}

open Paper36.AdaptiveTapes

/-- Complete declaration of `Paper36.AdaptiveTapes.adaptive_stack_coupling_integrated`; source support: S5.Thmtheorem5. -/
theorem adaptive_stack_coupling_integrated : ∀ {M : Type*} [MeasurableSpace M]
    (prior : Measure M) (P : M → Row → Law S) (choose : M → Hist → Law Row)
    (update : M → Hist → Row → S → Hist) (payoff : M → Hist → ℝ)
    (initial : M → Hist) (n : ℕ),
    (∫ m, expect (stackLaw (P m) n).mass
      (tapedValue (choose m) (update m) (payoff m) n (initial m)) ∂prior) =
      ∫ m, onlineValue (P m) (choose m) (update m) (payoff m) n (initial m) ∂prior := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories
open scoped ENNReal
variable {I J S Row : Type*} [Fintype I] [Fintype J] [Fintype S] [Fintype Row] [MeasurableSpace S] [DiscreteMeasurableSpace S]
variable {Hist : Type*}

open Paper36.AdaptiveTapes

/-- Complete declaration of `Paper36.AdaptiveTapes.runTape_prefixCompatible`; source support: S5.Thmtheorem5. -/
theorem runTape_prefixCompatible : ∀ (choose : List (Row × S) → Row) (tape : Row → ℕ → S)
    (n : ℕ) (history : List (Row × S)) (h : PrefixCompatible tape history),
    PrefixCompatible tape (runTape choose tape n history) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories
open scoped ENNReal
variable {I J S Row : Type*} [Fintype I] [Fintype J] [Fintype S] [Fintype Row] [MeasurableSpace S] [DiscreteMeasurableSpace S]
variable {Hist : Type*}

open Paper36.AdaptiveTapes

/-- Complete declaration of `Paper36.AdaptiveTapes.observed_prefix`; source support: S5.Thmtheorem5. -/
theorem observed_prefix : ∀ (choose : List (Row × S) → Row) (tape : Row → ℕ → S)
    (n : ℕ) (r : Row),
    rowObservations (runTape choose tape n []) r =
      List.ofFn (fun i : Fin (rowCount (runTape choose tape n []) r) => tape r i.val) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories
open scoped ENNReal
variable {I J S Row : Type*} [Fintype I] [Fintype J] [Fintype S] [Fintype Row] [MeasurableSpace S] [DiscreteMeasurableSpace S]
variable {Hist : Type*}

open Paper36.AdaptiveTapes

/-- Complete declaration of `Paper36.AdaptiveTapes.adaptive_unused_independent`; source support: S5.Thmtheorem5. -/
theorem adaptive_unused_independent : ∀ (P : Row → Law S) (choose : Hist → Law Row)
    (update : Hist → Row → S → Hist) (L : ℕ) (payoff : Hist → Stack Row S L → ℝ)
    (n : ℕ) (h : Hist),
    expect (stackLaw P (L+n)).mass (residualValue choose update L payoff n h) =
      onlineValue P choose update (fun h => expect (stackLaw P L).mass (payoff h)) n h := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories
open scoped ENNReal
universe v
variable {State Action : Type v} [Fintype State] [Fintype Action]
  [DecidableEq State] [DecidableEq Action] [MeasurableSpace State] [DiscreteMeasurableSpace State]
variable {Info : Type*} [MeasurableSpace Info]

open Paper36.AdaptiveTapes

/-- Complete declaration of `Paper36.AdaptiveTapes.tapedTrajectory_mass_average`; source support: S5.Thmtheorem5. -/
theorem tapedTrajectory_mass_average : ∀ (π : Simulation.Policy State Action)
    (p : Simulation.Kernel State Action) (n h : ℕ) (s : State) (path : Trajectory State Action n),
    expect (stackLaw (fun r : State × Action => p r.1 r.2) n).mass
      (fun tape => (tapedTrajectory π n h s tape).mass path) =
      (trajectoryLaw π p n h s).mass path := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories
open scoped ENNReal
universe v
variable {State Action : Type v} [Fintype State] [Fintype Action]
  [DecidableEq State] [DecidableEq Action] [MeasurableSpace State] [DiscreteMeasurableSpace State]
variable {Info : Type*} [MeasurableSpace Info]

open Paper36.AdaptiveTapes

/-- Complete declaration of `Paper36.AdaptiveTapes.tapedTrajectory_prefixCompatible`; source support: S5.Thmtheorem5. -/
theorem tapedTrajectory_prefixCompatible : ∀ (π : Simulation.Policy State Action)
    (original : (State × Action) → ℕ → State) (n : ℕ)
    (history : List ((State × Action) × State)) (hcompat : PrefixCompatible original history)
    (stage : ℕ) (s : State) (path : Trajectory State Action n)
    (hp : 0 < (tapedTrajectory π n stage s (window original (rowCount history) n)).mass path),
    initialState n path = s ∧ PrefixCompatible original (history ++ transitionTrace n path) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories
open scoped ENNReal
universe v
variable {State Action : Type v} [Fintype State] [Fintype Action]
  [DecidableEq State] [DecidableEq Action] [MeasurableSpace State] [DiscreteMeasurableSpace State]
variable {Info : Type*} [MeasurableSpace Info]

open Paper36.AdaptiveTapes

/-- Complete declaration of `Paper36.AdaptiveTapes.episodeHistory_count_prefix`; source support: S5.Thmtheorem5. -/
theorem episodeHistory_count_prefix : ∀ (T : ℕ) (paths : ℕ → Trajectory State Action T)
    (k : ℕ) (row : State × Action),
    rowCount (episodeHistory T paths k) row = Counts.before (fun j => visitCount row T (paths j)) k := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories
open scoped ENNReal
universe v
variable {State Action : Type v} [Fintype State] [Fintype Action]
  [DecidableEq State] [DecidableEq Action] [MeasurableSpace State] [DiscreteMeasurableSpace State]
variable {Info : Type*} [MeasurableSpace Info]

open Paper36.AdaptiveTapes

/-- Complete declaration of `Paper36.AdaptiveTapes.tapedEpisodeKernel_trajectory`; source support: S5.Thmtheorem5. -/
theorem tapedEpisodeKernel_trajectory : ∀ (πOf : Info → Simulation.Policy State Action) (pOf : Info → Simulation.Kernel State Action)
    (hπ : ∀ h s a, Measurable (fun i => (πOf i h s).mass a))
    (hp : ∀ s a t, Measurable (fun i => (pOf i s a).mass t))
    (n : ℕ) (s₀ : State),
    (tapedEpisodeKernel πOf pOf hπ hp n s₀).map Prod.snd = trajectoryKernel πOf pOf hπ hp n s₀ := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories
open scoped ENNReal
universe v
variable {State Action : Type v} [Fintype State] [Fintype Action]
  [DecidableEq State] [DecidableEq Action] [MeasurableSpace State] [DiscreteMeasurableSpace State]
variable {Info : Type*} [MeasurableSpace Info]

open Paper36.AdaptiveTapes

/-- Complete declaration of `Paper36.AdaptiveTapes.conditional_trajectory_of_tapedEpisode`; source support: S5.Thmtheorem5. -/
theorem conditional_trajectory_of_tapedEpisode : ∀ [Nonempty State] [Nonempty Action]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (πOf : Info → Simulation.Policy State Action) (pOf : Info → Simulation.Kernel State Action)
    (hπ : ∀ h s a, Measurable (fun i => (πOf i h s).mass a))
    (hp : ∀ s a t, Measurable (fun i => (pOf i s a).mass t))
    (n : ℕ) (s₀ : State) (info : Ω → Info)
    (sample : Ω → Stack (State × Action) State n × Trajectory State Action n)
    (hsample : AEMeasurable sample μ)
    (hgen : condDistrib sample info μ =ᵐ[μ.map info] tapedEpisodeKernel πOf pOf hπ hp n s₀),
    condDistrib (fun ω => (sample ω).2) info μ =ᵐ[μ.map info] trajectoryKernel πOf pOf hπ hp n s₀ := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories
open scoped ENNReal
universe v
variable {State Action : Type v} [Fintype State] [Fintype Action]
  [DecidableEq State] [DecidableEq Action] [MeasurableSpace State] [DiscreteMeasurableSpace State]
variable {Info : Type*} [MeasurableSpace Info]

open Paper36.AdaptiveTapes

/-- Complete declaration of `Paper36.AdaptiveTapes.tapedTrajectory_ae_observedEmpirical`; source support: S5.Thmtheorem5. -/
theorem tapedTrajectory_ae_observedEmpirical : ∀ (π : Simulation.Policy State Action)
    (original : (State × Action) → ℕ → State) (n : ℕ)
    (history : List ((State × Action) × State)) (hcompat : PrefixCompatible original history)
    (stage : ℕ) (s : State),
    ∀ᵐ path ∂lawMeasure (tapedTrajectory π n stage s (window original (rowCount history) n)),
      ∀ row (hn : 0 < rowCount (history ++ transitionTrace n path) row),
        observedEmpirical s (history ++ transitionTrace n path) row =
          RowTapes.empirical hn (fun i : Fin (rowCount (history ++ transitionTrace n path) row) => original row i.val) := by
  sorry

end

end P36Contract.AdaptiveTapes

namespace P36Contract.InfiniteTapes

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories
open scoped ENNReal
variable {I J S M : Type*} [Fintype S] [MeasurableSpace S] [DiscreteMeasurableSpace S] [MeasurableSpace M] {Row : Type*}

open Paper36.InfiniteTapes

/-- Complete declaration of `Paper36.InfiniteTapes.infinite_projection`; source support: S5.Thmtheorem5. -/
theorem infinite_projection : ∀ [Fintype J] [DecidableEq J] (P : I → Law S) (e : J ↪ I),
    (infiniteLaw P).map (fun tape j => tape (e j)) = lawMeasure (finiteLaw (fun j => P (e j))) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories
open scoped ENNReal
variable {I J S M : Type*} [Fintype S] [MeasurableSpace S] [DiscreteMeasurableSpace S] [MeasurableSpace M] {Row : Type*}

open Paper36.InfiniteTapes

/-- Complete declaration of `Paper36.InfiniteTapes.row_prefix_law`; source support: S5.Thmtheorem5. -/
theorem row_prefix_law : ∀ (P : Row → Law S) (r : Row) (n : ℕ),
    (infiniteLaw (fun c : Row × ℕ => P c.1)).map (tapePrefix r n) =
      lawMeasure (RowTapes.iidLaw (P r) n) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories
open scoped ENNReal
variable {I J S M : Type*} [Fintype S] [MeasurableSpace S] [DiscreteMeasurableSpace S] [MeasurableSpace M] {Row : Type*}

open Paper36.InfiniteTapes

/-- Complete declaration of `Paper36.InfiniteTapes.rowKernel_prefix`; source support: S5.Thmtheorem5. -/
theorem rowKernel_prefix : ∀ (P : M → Row → Law S)
    (hP : ∀ r s, Measurable (fun m => (P m r).mass s)) (r : Row) (n : ℕ),
    (rowKernel P hP).map (tapePrefix r n) = RowTapes.iidKernel (fun m => P m r) (hP r) n := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories
open scoped ENNReal
variable {I J S M : Type*} [Fintype S] [MeasurableSpace S] [DiscreteMeasurableSpace S] [MeasurableSpace M] {Row : Type*}

open Paper36.InfiniteTapes

/-- Complete declaration of `Paper36.InfiniteTapes.priorTapes_prefix_condDistrib`; source support: S5.Thmtheorem5. -/
theorem priorTapes_prefix_condDistrib : ∀ [Nonempty S] (ν : Measure M) [IsProbabilityMeasure ν]
    (P : M → Row → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (r : Row) (n : ℕ),
    condDistrib (fun x : M × (Row × ℕ → S) => tapePrefix r n x.2) Prod.fst (priorTapes ν P hP)
      =ᵐ[ν] RowTapes.iidKernel (fun m => P m r) (hP r) n := by
  sorry

end

end P36Contract.InfiniteTapes

namespace P36Contract.Main

section
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested Paper36.Algorithm
  Paper36.StatisticalCounts Paper36.Statistical
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {Ω Info Model Hist : Type*} [MeasurableSpace Ω] [MeasurableSpace Info]
  [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model] [MeasurableSpace Hist]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℕ} {s₀ : S}
variable {E : EpisodeSystem μ Info S A (H+1) s₀}
  (P : PosteriorSystem (Model := Model) (Hist := Hist) E)

open Paper36.Main

/-- Complete declaration of `Paper36.Main.theorem_4_2`; source support: S4.Thmtheorem2, Thmalgorithm1. -/
theorem theorem_4_2 : ∀ (external : RowTapes.ExternalCategoricalConcentration (S := S))
    (α τ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hτ : 0 ≤ τ)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (hstrict : ∀ q ∈ support P, minimumRisk α c (H+1) 0 s₀ q < τ)
    (O : BorelAlgorithm.BorelOracles α c r (H+1) s₀ τ (support P))
    (hrun : ∀ n ω, policy P n ω = Algorithm.selected O.toOracles
      (target (S := S) (A := A) (H := H) α) (samples P) n ω),
    ∀ K, 1 ≤ K →
    ((∫ ω, Assembly.total (fun n ω => trueRisk P α c n ω - τ) K ω ∂μ) ≤
      SourceBank.riskEnvelope (S := S) (A := A) α (delta P α τ c) (H+1)) ∧
    ((∫ ω, Assembly.total (fun n ω => optimum P α τ c r ω - trueReward P r n ω) K ω ∂μ) ≤
      rewardAllowance (S := S) (A := A) (H := H) K + (H+1 : ℝ) *
        ((target (S := S) (A := A) (H := H) α K + τ) / delta P α τ c)) ∧
    ((∫ ω, Assembly.countRV (target (S := S) (A := A) (H := H) α) (deposit P α τ c) K ω ∂μ) ≤
      min (K : ℝ) ((target (S := S) (A := A) (H := H) α K + τ) / delta P α τ c)) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested Paper36.Algorithm
  Paper36.StatisticalCounts Paper36.Statistical
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {Ω Info Model Hist : Type*} [MeasurableSpace Ω] [MeasurableSpace Info]
  [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model] [MeasurableSpace Hist]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℕ} {s₀ : S}
variable {E : EpisodeSystem μ Info S A (H+1) s₀}
  (P : PosteriorSystem (Model := Model) (Hist := Hist) E)

open Paper36.Main

/-- Complete declaration of `Paper36.Main.certified_performance`; source support: A2.Thmtheorem1. -/
theorem certified_performance : ∀ (external : RowTapes.ExternalCategoricalConcentration (S := S))
    (α τ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hτ : 0 ≤ τ)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (hstrict : ∀ q ∈ support P, minimumRisk α c (H+1) 0 s₀ q < τ)
    (O : BorelAlgorithm.BorelOracles α c r (H+1) s₀ τ (support P))
    (ε ζ : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hζ : ∀ n, 0 ≤ ζ n)
    (hriskOracle : ∀ᵐ ω ∂μ, ∀ n,
      (Bank.calibrates (target (S := S) (A := A) (H := H) α) (fun j => deposit P α τ c j ω) n →
        sampledRisk P α c n ω = τ - deposit P α τ c (n+1) ω) ∧
      (¬Bank.calibrates (target (S := S) (A := A) (H := H) α) (fun j => deposit P α τ c j ω) n →
        sampledRisk P α c n ω ≤ τ + ε n))
    (hrewardOracle : ∀ᵐ ω ∂μ, ∀ n,
      (Bank.calibrates (target (S := S) (A := A) (H := H) α) (fun j => deposit P α τ c j ω) n →
        sampledOptimum P α τ c r n ω - sampledReward P r n ω ≤ (H+1 : ℝ)) ∧
      (¬Bank.calibrates (target (S := S) (A := A) (H := H) α) (fun j => deposit P α τ c j ω) n →
        sampledOptimum P α τ c r n ω - sampledReward P r n ω ≤ ζ n))
    {K : ℕ} (hK : 1 ≤ K),
    ((∫ ω, Assembly.total (fun n ω => trueRisk P α c n ω - τ) K ω ∂μ) ≤
      SourceBank.riskEnvelope (S := S) (A := A) α (delta P α τ c) (H+1) + ∑ n ∈ Finset.range K, ε n) ∧
    ((∫ ω, Assembly.total (fun n ω => optimum P α τ c r ω - trueReward P r n ω) K ω ∂μ) ≤
      rewardAllowance (S := S) (A := A) (H := H) K + (H+1 : ℝ) *
        ((target (S := S) (A := A) (H := H) α K + τ) / delta P α τ c) + ∑ n ∈ Finset.range K, ζ n) ∧
    ((∫ ω, Assembly.countRV (target (S := S) (A := A) (H := H) α) (deposit P α τ c) K ω ∂μ) ≤
      min (K : ℝ) ((target (S := S) (A := A) (H := H) α K + τ) / delta P α τ c)) := by
  sorry

end

end P36Contract.Main

namespace P36Contract.MainExtensions

section
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested Paper36.Algorithm
  Paper36.StatisticalCounts Paper36.Statistical
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {Ω Info Model Hist : Type*} [MeasurableSpace Ω] [MeasurableSpace Info]
  [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model] [MeasurableSpace Hist]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℕ} {s₀ : S}
variable {E : EpisodeSystem μ Info S A (H+1) s₀}
  (P : PosteriorSystem (Model := Model) (Hist := Hist) E)

open Paper36.Main

/-- Complete declaration of `Paper36.Main.pathwise_calibration`; source support: S4.Thmtheorem2. -/
theorem pathwise_calibration : ∀ (α τ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hτ : 0 ≤ τ)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hstrict : ∀ q ∈ support P, minimumRisk α c (H+1) 0 s₀ q < τ),
    0 < delta P α τ c ∧
    ∀ᵐ ω ∂μ,
      (∀ K, (Bank.count (target (S := S) (A := A) (H := H) α)
        (fun j => deposit P α τ c j ω) K : ℝ) ≤
        min (K : ℝ) ((target (S := S) (A := A) (H := H) α K + τ) / delta P α τ c)) ∧
      Filter.Tendsto (fun K : ℕ =>
        (Bank.count (target (S := S) (A := A) (H := H) α)
          (fun j => deposit P α τ c j ω) K : ℝ) / (K : ℝ)) Filter.atTop (nhds 0) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested Paper36.Algorithm
  Paper36.StatisticalCounts Paper36.Statistical
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {Ω Info Model Hist : Type*} [MeasurableSpace Ω] [MeasurableSpace Info]
  [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model] [MeasurableSpace Hist]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℕ} {s₀ : S}
variable {E : EpisodeSystem μ Info S A (H+1) s₀}
  (P : PosteriorSystem (Model := Model) (Hist := Hist) E)

open Paper36.Main

/-- Complete declaration of `Paper36.Main.risk_bank_certificate`; source support: S5.Thmtheorem6. -/
theorem risk_bank_certificate : ∀ (external : RowTapes.ExternalCategoricalConcentration (S := S))
    (α τ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (O : BorelAlgorithm.BorelOracles α c r (H+1) s₀ τ (support P))
    (hrun : ∀ n ω, policy P n ω = Algorithm.selected O.toOracles
      (target (S := S) (A := A) (H := H) α) (samples P) n ω)
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (hinfo : ∀ k, MeasurableSpace.comap (E.info k) inferInstance = ℱ k)
    (hpath : ∀ k, Measurable[ℱ (k+1), inferInstance] (E.path k))
    {K : ℕ} (hK : 1 ≤ K) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1),
    μ.real {ω | Bounds.certificate (Fintype.card S) (Fintype.card A) (H+1)
        (Weights.W α (H+1)) (Weights.w α (H+1)) δ K -
          Bank.bank (target (S := S) (A := A) (H := H) α) (fun j => deposit P α τ c j ω) K <
        Assembly.total (fun n ω => trueRisk P α c n ω - τ) K ω} ≤ δ := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested Paper36.Algorithm
  Paper36.StatisticalCounts Paper36.Statistical
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {Ω Info Model Hist : Type*} [MeasurableSpace Ω] [MeasurableSpace Info]
  [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model] [MeasurableSpace Hist]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℕ} {s₀ : S}
variable {E : EpisodeSystem μ Info S A (H+1) s₀}
  (P : PosteriorSystem (Model := Model) (Hist := Hist) E)

open Paper36.Main

/-- Complete declaration of `Paper36.Main.corollary_B_1`; source support: A2.Thmtheorem1. -/
theorem corollary_B_1 : ∀ (external : RowTapes.ExternalCategoricalConcentration (S := S))
    (α τ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hτ : 0 ≤ τ)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (hstrict : ∀ q ∈ support P, minimumRisk α c (H+1) 0 s₀ q < τ)
    (O : BorelAlgorithm.BorelOracles α c r (H+1) s₀ τ (support P))
    (ε ζ : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hζ : ∀ n, 0 ≤ ζ n)
    (O' : Approximation.Oracles α c r (H+1) s₀ τ (support P) ε ζ)
    (hrun : ∀ n ω, policy P n ω = Approximation.selected O'
      (target (S := S) (A := A) (H := H) α) (samples P) n ω),
    ∀ K, 1 ≤ K →
    ((∫ ω, Assembly.total (fun n ω => trueRisk P α c n ω - τ) K ω ∂μ) ≤
      SourceBank.riskEnvelope (S := S) (A := A) α (delta P α τ c) (H+1) + ∑ n ∈ Finset.range K, ε n) ∧
    ((∫ ω, Assembly.total (fun n ω => optimum P α τ c r ω - trueReward P r n ω) K ω ∂μ) ≤
      rewardAllowance (S := S) (A := A) (H := H) K + (H+1 : ℝ) *
        ((target (S := S) (A := A) (H := H) α K + τ) / delta P α τ c) + ∑ n ∈ Finset.range K, ζ n) ∧
    ((∫ ω, Assembly.countRV (target (S := S) (A := A) (H := H) α) (deposit P α τ c) K ω ∂μ) ≤
      min (K : ℝ) ((target (S := S) (A := A) (H := H) α K + τ) / delta P α τ c)) := by
  sorry

end

end P36Contract.MainExtensions

namespace P36Contract.MainEndpoints

section
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested Paper36.Algorithm
  Paper36.StatisticalCounts Paper36.Statistical
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {Ω Info Model Hist : Type*} [MeasurableSpace Ω] [MeasurableSpace Info]
  [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model] [MeasurableSpace Hist]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {s₀ : S}
variable {E : EpisodeSystem μ Info S A 1 s₀}
  (P : PosteriorSystem (Model := Model) (Hist := Hist) E)

open Paper36.Main

/-- Complete declaration of `Paper36.Main.theorem_4_2_horizon_one`; source support: S4.Thmtheorem2. -/
theorem theorem_4_2_horizon_one : ∀ (α τ : ℝ) (c r : ℕ → S → A → ℝ)
    (O : BorelAlgorithm.BorelOracles α c r 1 s₀ τ (support P))
    (hrun : ∀ n ω, policy P n ω = Algorithm.selected O.toOracles
      (target (S := S) (A := A) (H := 0) α) (samples P) n ω) (K : ℕ),
    ((∫ ω, Assembly.total (fun n ω => trueRisk P α c n ω - τ) K ω ∂μ) ≤ 0) ∧
    ((∫ ω, Assembly.total (fun n ω => optimum P α τ c r ω - trueReward P r n ω) K ω ∂μ) = 0) ∧
    (∀ ω, Bank.bank (target (S := S) (A := A) (H := 0) α) (fun j => deposit P α τ c j ω) K = 0 ∧
      Bank.count (target (S := S) (A := A) (H := 0) α) (fun j => deposit P α τ c j ω) K = 0) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested Paper36.Algorithm
  Paper36.StatisticalCounts Paper36.Statistical
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {Ω Info Model Hist : Type*} [MeasurableSpace Ω] [MeasurableSpace Info]
  [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model] [MeasurableSpace Hist]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {s₀ : S}
variable {E : EpisodeSystem μ Info S A 1 s₀}
  (P : PosteriorSystem (Model := Model) (Hist := Hist) E)

open Paper36.Main

/-- Complete declaration of `Paper36.Main.corollary_B_1_horizon_one`; source support: A2.Thmtheorem1. -/
theorem corollary_B_1_horizon_one : ∀ (α τ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (O : BorelAlgorithm.BorelOracles α c r 1 s₀ τ (support P))
    (ε ζ : ℕ → ℝ)
    (O' : Approximation.Oracles α c r 1 s₀ τ (support P) ε ζ)
    (hrun : ∀ n ω, policy P n ω = Approximation.selected O'
      (target (S := S) (A := A) (H := 0) α) (samples P) n ω) (K : ℕ),
    ((∫ ω, Assembly.total (fun n ω => trueRisk P α c n ω - τ) K ω ∂μ) ≤ ∑ n ∈ Finset.range K, ε n) ∧
    ((∫ ω, Assembly.total (fun n ω => optimum P α τ c r ω - trueReward P r n ω) K ω ∂μ) ≤
      ∑ n ∈ Finset.range K, ζ n) := by
  sorry

end

end P36Contract.MainEndpoints

namespace P36Contract.StageStatistical

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation Paper36.Trajectories Paper36.RowTapes Paper36.StatisticalCounts Paper36.Statistical.PosteriorSystem
open scoped ENNReal
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A] [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
variable {Ω Info Model Hist : Type*} [MeasurableSpace Ω] [MeasurableSpace Info] [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model] [MeasurableSpace Hist] {μ : Measure Ω} [IsProbabilityMeasure μ] {T : ℕ} {s₀ : S}
variable {H : ℕ} (E' : EpisodeSystem μ Info S A (H+1) s₀) (P' : Paper36.Statistical.PosteriorSystem (Model := Model) (Hist := Hist) E')

open Paper36.Statistical
open Paper36.Statistical.PosteriorSystem

/-- Complete declaration of `Paper36.Statistical.PosteriorSystem.stage_lemma_5_5`; source support: A2.Thmtheorem3, S5.Thmtheorem5. -/
theorem PosteriorSystem__stage_lemma_5_5 : ∀ (external : ExternalCategoricalConcentration (S := S))
    (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1) (c : ℕ → S → A → ℝ)
    (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1) {K : ℕ} (hK : 1 ≤ K),
    (∑ k ∈ Finset.range K, ∫ ω, P'.stageRiskError β c k ω ∂μ) ≤
      Target.confidence (Target.scale (Real.sqrt (Weights.stageWsq β (H+1))) (Fintype.card S) (Fintype.card A))
        (Fintype.card S) (Fintype.card A) (H+1) K * Real.sqrt (K : ℝ) +
      (2 * (Fintype.card S : ℝ) * (Fintype.card A : ℝ) * (H+1) * Weights.stagew β (H+1) + (H+1 : ℝ)/2) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation Paper36.Trajectories Paper36.RowTapes Paper36.StatisticalCounts Paper36.Statistical.PosteriorSystem
open scoped ENNReal
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A] [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
variable {Ω Info Model Hist : Type*} [MeasurableSpace Ω] [MeasurableSpace Info] [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model] [MeasurableSpace Hist] {μ : Measure Ω} [IsProbabilityMeasure μ] {T : ℕ} {s₀ : S}
variable {H : ℕ} (E' : EpisodeSystem μ Info S A (H+1) s₀) (P' : Paper36.Statistical.PosteriorSystem (Model := Model) (Hist := Hist) E')

open Paper36.Statistical
open Paper36.Statistical.PosteriorSystem

/-- Complete declaration of `Paper36.Statistical.PosteriorSystem.stage_theorem_5_6`; source support: A2.Thmtheorem3, S5.Thmtheorem6. -/
theorem PosteriorSystem__stage_theorem_5_6 : ∀ (external : ExternalCategoricalConcentration (S := S))
    (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1) (c : ℕ → S → A → ℝ)
    (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1)
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (hinfo : ∀ k, MeasurableSpace.comap (E'.info k) inferInstance = ℱ k)
    (hpath : ∀ k, Measurable[ℱ (k+1), inferInstance] (E'.path k))
    {K : ℕ} (hK : 1 ≤ K) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1),
    μ.real {ω | Bounds.certificate (Fintype.card S) (Fintype.card A) (H+1)
      (Real.sqrt (Weights.stageWsq β (H+1))) (Weights.stagew β (H+1)) δ K <
        ∑ k ∈ Finset.range K, P'.stageRiskError β c k ω} ≤ δ := by
  sorry

end

end P36Contract.StageStatistical

namespace P36Contract.StageAlgorithm

section
open Set MeasureTheory Paper36.Nested
variable {S A Ω : Type*} [Fintype S] [Fintype A] [Nonempty A]

open Paper36.StageAlgorithm

/-- Complete declaration of `Paper36.StageAlgorithm.exists_oracles`; source support: A2.Thmtheorem3, S4.Thmtheorem1. -/
theorem exists_oracles : ∀ (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1) (τ : ℝ)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1)
    (H : ℕ) (s₁ : S) (Q : Set (Kernel S A))
    (hstrict : ∀ q ∈ Q, ∃ π : Simulation.Policy S A,
      StageRisk.risk β c π (RiskBridge.ofKernel q) H 0 s₁ < τ),
    Nonempty (Oracles β c r H s₁ τ Q) := by
  sorry

end

section
open Set MeasureTheory Paper36.Nested
variable {S A Ω : Type*} [Fintype S] [Fintype A] [Nonempty A]

open Paper36.StageAlgorithm

/-- Complete declaration of `Paper36.StageAlgorithm.sampled_risk_bank`; source support: A2.Thmtheorem3. -/
theorem sampled_risk_bank : ∀ {β : ℕ → ℝ} {τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} (O : Oracles β c r H s₁ τ Q)
    (T : ℕ → ℝ) (sample : ℕ → Ω → Kernel S A) (ω : Ω)
    (hsample : ∀ n, sample n ω ∈ Q) (K : ℕ),
    (∑ n ∈ Finset.range K, (risk β c (selected O T sample n ω) (sample n ω) H 0 s₁ - τ)) ≤
      -Bank.bank T (fun j => deposits β τ c H s₁ sample j ω) K := by
  sorry

end

section
open Set MeasureTheory Paper36.Nested
variable {S A Ω : Type*} [Fintype S] [Fintype A] [Nonempty A]

open Paper36.StageAlgorithm

/-- Complete declaration of `Paper36.StageAlgorithm.sampled_reward_count`; source support: A2.Thmtheorem3. -/
theorem sampled_reward_count : ∀ {β : ℕ → ℝ} {τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} (O : Oracles β c r H s₁ τ Q)
    (hr : ∀ h s a, r h s a ∈ Icc 0 1) (T : ℕ → ℝ)
    (sample : ℕ → Ω → Kernel S A) (ω : Ω) (hsample : ∀ n, sample n ω ∈ Q) (K : ℕ),
    (∑ n ∈ Finset.range K, (constrainedValue β c r H s₁ τ (sample n ω) -
      Nested.reward r (selected O T sample n ω) (sample n ω) H 0 s₁)) ≤
      (H : ℝ) * (Bank.count T (fun j => deposits β τ c H s₁ sample j ω) K : ℝ) := by
  sorry

end

section
open Set MeasureTheory Paper36.Nested
variable {S A Ω : Type*} [Fintype S] [Fintype A] [Nonempty A]
variable [MeasurableSpace Ω]

open Paper36.StageAlgorithm

/-- Complete declaration of `Paper36.StageAlgorithm.measurable_selected`; source support: A2.Thmtheorem3. -/
theorem measurable_selected : ∀ {β : ℕ → ℝ} {τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} (O : BorelOracles β c r H s₁ τ Q)
    (hβ : ∀ j, 0 < β j ∧ β j ≤ 1) (hc : ∀ h s a, c h s a ∈ Icc 0 1)
    (T : ℕ → ℝ) (sample : ℕ → Ω → Kernel S A) (hsample : ∀ n, Measurable (sample n))
    (n : ℕ),
    Measurable (fun ω => selected O.toOracles T sample n ω) := by
  sorry

end

section
open Set MeasureTheory Paper36.Nested
variable {S A Ω : Type*} [Fintype S] [Fintype A] [Nonempty A]
variable (ν : Measure (Kernel S A)) [IsProbabilityMeasure ν]
  (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
  (τ : ℝ) (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1)
  (H : ℕ) (s₁ : S)
  (hstrict : ∀ q ∈ ν.support, ∃ π : Simulation.Policy S A,
    StageRisk.risk β c π (RiskBridge.ofKernel q) H 0 s₁ < τ)

open Paper36.StageAlgorithm

/-- Complete declaration of `Paper36.StageAlgorithm.calibration_count`; source support: A2.Thmtheorem3. -/
include hβ hc hstrict in
theorem calibration_count : ∀ (hH : 1 ≤ H) (sample : ℕ → Ω → Kernel S A) (ω : Ω)
    (hsample : ∀ n, sample n ω ∈ ν.support) (K : ℕ),
    (Bank.count (StageCharging.stageTarget (S := S) (A := A) β H)
      (fun j => deposits β τ c H s₁ sample j ω) K : ℝ) ≤
      min (K : ℝ) ((StageCharging.stageTarget (S := S) (A := A) β H K + τ) /
        StageCalibration.uniformGap ν β c H s₁ τ) := by
  sorry

end

section
open Set MeasureTheory Paper36.Nested
variable {S A Ω : Type*} [Fintype S] [Fintype A] [Nonempty A]
variable (ν : Measure (Kernel S A)) [IsProbabilityMeasure ν]
  (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
  (τ : ℝ) (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1)
  (H : ℕ) (s₁ : S)
  (hstrict : ∀ q ∈ ν.support, ∃ π : Simulation.Policy S A,
    StageRisk.risk β c π (RiskBridge.ofKernel q) H 0 s₁ < τ)

open Paper36.StageAlgorithm

/-- Complete declaration of `Paper36.StageAlgorithm.bank_deficit`; source support: A2.Thmtheorem3. -/
include hβ hc hstrict in
theorem bank_deficit : ∀ (hH : 1 ≤ H) (sample : ℕ → Ω → Kernel S A) (ω : Ω)
    (hsample : ∀ n, sample n ω ∈ ν.support) (K : ℕ),
    StageCharging.stageTarget (S := S) (A := A) β H K -
      Bank.bank (StageCharging.stageTarget (S := S) (A := A) β H)
        (fun j => deposits β τ c H s₁ sample j ω) K ≤
      StageCharging.stageResidual (S := S) (A := A) β H
        (StageCalibration.uniformGap ν β c H s₁ τ) := by
  sorry

end

section
open Set MeasureTheory Paper36.Nested
variable {S A Ω : Type*} [Fintype S] [Fintype A] [Nonempty A]
variable (ν : Measure (Kernel S A)) [IsProbabilityMeasure ν]
  (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
  (τ : ℝ) (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1)
  (H : ℕ) (s₁ : S)
  (hstrict : ∀ q ∈ ν.support, ∃ π : Simulation.Policy S A,
    StageRisk.risk β c π (RiskBridge.ofKernel q) H 0 s₁ < τ)

open Paper36.StageAlgorithm

/-- Complete declaration of `Paper36.StageAlgorithm.calibration_sparse`; source support: A2.Thmtheorem3. -/
include hβ hc hstrict in
theorem calibration_sparse : ∀ (hH : 1 ≤ H) (sample : ℕ → Ω → Kernel S A) (ω : Ω)
    (hsample : ∀ n, sample n ω ∈ ν.support),
    Filter.Tendsto (fun K : ℕ =>
      (Bank.count (StageCharging.stageTarget (S := S) (A := A) β H)
        (fun j => deposits β τ c H s₁ sample j ω) K : ℝ) / (K : ℝ))
      Filter.atTop (nhds 0) := by
  sorry

end

section
open Set MeasureTheory Paper36.Nested
variable {S A Ω : Type*} [Fintype S] [Fintype A] [Nonempty A]
variable (ν : Measure (Kernel S A)) [IsProbabilityMeasure ν]
  (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
  (τ : ℝ) (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1)
  (H : ℕ) (s₁ : S)
  (hstrict : ∀ q ∈ ν.support, ∃ π : Simulation.Policy S A,
    StageRisk.risk β c π (RiskBridge.ofKernel q) H 0 s₁ < τ)

open Paper36.StageAlgorithm

/-- Complete declaration of `Paper36.StageAlgorithm.sampled_reward_bound`; source support: A2.Thmtheorem3. -/
include hβ hc hstrict in
theorem sampled_reward_bound : ∀ (r : ℕ → S → A → ℝ) (hr : ∀ h s a, r h s a ∈ Icc 0 1)
    (O : Oracles β c r H s₁ τ ν.support) (hH : 1 ≤ H)
    (sample : ℕ → Ω → Kernel S A) (ω : Ω) (hsample : ∀ n, sample n ω ∈ ν.support) (K : ℕ),
    (∑ n ∈ Finset.range K, (constrainedValue β c r H s₁ τ (sample n ω) -
      Nested.reward r (selected O (StageCharging.stageTarget (S := S) (A := A) β H) sample n ω)
        (sample n ω) H 0 s₁)) ≤
      (H : ℝ) * min (K : ℝ) ((StageCharging.stageTarget (S := S) (A := A) β H K + τ) /
        StageCalibration.uniformGap ν β c H s₁ τ) := by
  sorry

end

section
open Set MeasureTheory Paper36.Nested
variable {S A Ω : Type*} [Fintype S] [Fintype A] [Nonempty A]
variable (ν : Measure (Kernel S A)) [IsProbabilityMeasure ν]
  (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
  (τ : ℝ) (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1)
  (H : ℕ) (s₁ : S)
  (hstrict : ∀ q ∈ ν.support, ∃ π : Simulation.Policy S A,
    StageRisk.risk β c π (RiskBridge.ofKernel q) H 0 s₁ < τ)
variable [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (sample : ℕ → Ω → Kernel S A) (hsample : ∀ n, Measurable (sample n))
  (hsupport : ∀ᵐ ω ∂μ, ∀ n, sample n ω ∈ ν.support)

open Paper36.StageAlgorithm

/-- Complete declaration of `Paper36.StageAlgorithm.expected_calibration_count`; source support: A2.Thmtheorem3. -/
include hβ hc hstrict hsample hsupport in
theorem expected_calibration_count : ∀ (hH : 1 ≤ H) (K : ℕ),
    (∫ ω, Assembly.countRV (StageCharging.stageTarget (S := S) (A := A) β H)
      (deposits β τ c H s₁ sample) K ω ∂μ) ≤
      min (K : ℝ) ((StageCharging.stageTarget (S := S) (A := A) β H K + τ) /
        StageCalibration.uniformGap ν β c H s₁ τ) := by
  sorry

end

section
open Set MeasureTheory Paper36.Nested
variable {S A Ω : Type*} [Fintype S] [Fintype A] [Nonempty A]
variable (ν : Measure (Kernel S A)) [IsProbabilityMeasure ν]
  (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
  (τ : ℝ) (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1)
  (H : ℕ) (s₁ : S)
  (hstrict : ∀ q ∈ ν.support, ∃ π : Simulation.Policy S A,
    StageRisk.risk β c π (RiskBridge.ofKernel q) H 0 s₁ < τ)
variable [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (sample : ℕ → Ω → Kernel S A) (hsample : ∀ n, Measurable (sample n))
  (hsupport : ∀ᵐ ω ∂μ, ∀ n, sample n ω ∈ ν.support)

open Paper36.StageAlgorithm

/-- Complete declaration of `Paper36.StageAlgorithm.expected_bank_deficit`; source support: A2.Thmtheorem3. -/
include hβ hc hstrict hsample hsupport in
theorem expected_bank_deficit : ∀ (hH : 1 ≤ H) (K : ℕ),
    StageCharging.stageTarget (S := S) (A := A) β H K -
      (∫ ω, Assembly.bankRV (StageCharging.stageTarget (S := S) (A := A) β H)
        (deposits β τ c H s₁ sample) K ω ∂μ) ≤
      StageCharging.stageResidual (S := S) (A := A) β H
        (StageCalibration.uniformGap ν β c H s₁ τ) := by
  sorry

end

section
open Set MeasureTheory Paper36.Nested
variable {S A Ω : Type*} [Fintype S] [Fintype A] [Nonempty A]

open Paper36.StageAlgorithm

/-- Complete declaration of `Paper36.StageAlgorithm.risk_bank_certificate_path`; source support: A2.Thmtheorem3, S5.Thmtheorem6. -/
theorem risk_bank_certificate_path : ∀ {β : ℕ → ℝ} {τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} (O : Oracles β c r H s₁ τ Q)
    (T : ℕ → ℝ) (sample : ℕ → Ω → Kernel S A) (latent : Ω → Kernel S A) (ω : Ω)
    (hsample : ∀ n, sample n ω ∈ Q) (K : ℕ) (E : ℝ)
    (hmodel : (∑ n ∈ Finset.range K,
      (risk β c (selected O T sample n ω) (latent ω) H 0 s₁ -
        risk β c (selected O T sample n ω) (sample n ω) H 0 s₁)) ≤ E),
    (∑ n ∈ Finset.range K, (risk β c (selected O T sample n ω) (latent ω) H 0 s₁ - τ)) ≤
      E - Bank.bank T (fun j => deposits β τ c H s₁ sample j ω) K := by
  sorry

end

section
variable {S A : Type*} [Fintype S] [Fintype A]

open Paper36.StageCharging

/-- Complete declaration of `Paper36.StageCharging.stage_target_properties`; source support: A2.Thmtheorem3. -/
theorem stage_target_properties : ∀ [Nonempty A] (β : ℕ → ℝ) (H : ℕ) (s₁ : S)
    (hH : 1 ≤ H) {Δ : ℝ} (hΔ : 0 < Δ),
    Monotone (stageTarget (S := S) (A := A) β H) ∧
      stageTarget (S := S) (A := A) β H 0 = 0 ∧
      (∀ j n, stageTarget (S := S) (A := A) β H (j+n) ≤
        stageTarget (S := S) (A := A) β H j + stageTarget (S := S) (A := A) β H n) ∧
      (∀ n, stageTarget (S := S) (A := A) β H n - (n : ℝ)*Δ ≤
        stageResidual (S := S) (A := A) β H Δ) ∧
      Filter.Tendsto (fun n : ℕ => stageTarget (S := S) (A := A) β H n / (n : ℝ))
        Filter.atTop (nhds 0) := by
  sorry

end

section
open Set MeasureTheory Paper36.Nested
variable {S A Ω : Type*} [Fintype S] [Fintype A] [Nonempty A]
variable [MeasurableSpace Ω]
variable {Model Hist : Type*} [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model]
  [MeasurableSpace Hist] {μ : Measure Ω} [IsProbabilityMeasure μ]

open Paper36.StageAlgorithm

/-- Complete declaration of `Paper36.StageAlgorithm.comparator_symmetry`; source support: A2.Thmtheorem3, S5.Thmtheorem8. -/
theorem comparator_symmetry : ∀ (decode : Model → Kernel S A) (hdecode : Measurable decode)
    (latent sampled : Ω → Model) (hlatent : Measurable latent) (hsampled : Measurable sampled)
    (history : Ω → Hist) (hhistory : Measurable history)
    (hposterior : ProbabilityTheory.condDistrib latent history μ =ᵐ[μ.map history]
      ProbabilityTheory.condDistrib sampled history μ)
    {τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {masses : ℕ → ℝ} {Q : Set (Kernel S A)} (O : BorelOracles masses c r H s₁ τ Q)
    (hr : ∀ h s a, r h s a ∈ Icc 0 1)
    (hsupport : ∀ᵐ ω ∂μ, decode (latent ω) ∈ Q ∧ decode (sampled ω) ∈ Q),
    (∫ ω, constrainedValue masses c r H s₁ τ (decode (latent ω)) -
      constrainedValue masses c r H s₁ τ (decode (sampled ω)) ∂μ) = 0 := by
  sorry

end

end P36Contract.StageAlgorithm

namespace P36Contract.SourceScaling

section
open Paper36 Asymptotics Filter

open Paper36.SourceScaling

/-- Complete declaration of `Paper36.SourceScaling.target_log_envelope`; source support: S4.Thmtheorem2. -/
theorem target_log_envelope : ∀ {s a h w : ℝ} (hs : 1 ≤ s) (ha : 1 ≤ a)
    (hh : 1 ≤ h) (hw : 0 ≤ w) {K : ℕ} (hK : 1 ≤ K),
    BankTarget.paperTarget s a h w K ≤
      Scaling.coefficient (Target.scale w s a) (Target.A0 s a h) (Target.nu s) (Target.M0 h) *
        Real.sqrt (K : ℝ) * (1 + Real.log (K : ℝ)) := by
  sorry

end

section
open Paper36 Asymptotics Filter

open Paper36.SourceScaling

/-- Complete declaration of `Paper36.SourceScaling.reward_log_envelope`; source support: S4.Thmtheorem2. -/
theorem reward_log_envelope : ∀ {s a h : ℝ} (hs : 1 ≤ s) (ha : 1 ≤ a) (hh : 1 ≤ h)
    {K : ℕ} (hK : 1 ≤ K),
    8 * h * Real.sqrt h * Real.sqrt (s*a*(K:ℝ)*Bounds.rewardLog s a h K) + h/2 ≤
      rewardCoefficient s a h * Real.sqrt (K : ℝ) * (1 + Real.log (K : ℝ)) := by
  sorry

end

section
open Paper36 Asymptotics Filter

open Paper36.SourceScaling

/-- Complete declaration of `Paper36.SourceScaling.performance_upper_envelope_isBigO`; source support: S4.Thmtheorem2. -/
theorem performance_upper_envelope_isBigO : ∀ {s a h w Δ τ : ℝ}
    (hs : 1 ≤ s) (ha : 1 ≤ a) (hh : 1 ≤ h) (hw : 0 ≤ w) (hΔ : 0 < Δ) (hτ : 0 ≤ τ),
    (fun K : ℕ =>
      8*h*Real.sqrt h*Real.sqrt (s*a*(K:ℝ)*Bounds.rewardLog s a h K) + h/2 +
        h*((BankTarget.paperTarget s a h w K+τ)/Δ)) =O[atTop]
      (fun K : ℕ => Real.sqrt (K:ℝ)*(1+Real.log (K:ℝ))) := by
  sorry

end

section
open Paper36 Asymptotics Filter

open Paper36.SourceScaling

/-- Complete declaration of `Paper36.SourceScaling.residual_parameter_identity`; source support: S4.Thmtheorem2. -/
theorem residual_parameter_identity : ∀ {s a h w Δ : ℝ}
    (hs : 0 < s) (ha : 0 ≤ a) (hΔ : 0 < Δ),
    BankTarget.paperResidual s a h w Δ =
      16*s^2*a*w^2/Δ * (residualLogFactor s a h w Δ)^2 := by
  sorry

end

section
open Paper36 Asymptotics Filter

open Paper36.SourceScaling

/-- Complete declaration of `Paper36.SourceScaling.scale_sq`; source support: S4.Thmtheorem2. -/
theorem scale_sq : ∀ {s a w : ℝ} (hs : 0 ≤ s) (ha : 0 ≤ a),
    (Target.scale w s a)^2 = 32*w^2*s*a := by
  sorry

end

end P36Contract.SourceScaling

namespace P36Contract.Selection

section
open Set MeasureTheory Paper36.Regularity Paper36.Nested
universe u
variable {S A : Type u} [Fintype S] [Fintype A]

open Paper36.Selection

/-- Complete declaration of `Paper36.Selection.feasible_graph_closed`; source support: S4.Thmtheorem2. -/
theorem feasible_graph_closed : ∀ (α τ : ℝ) (c : ℕ → S → A → ℝ)
    (H : ℕ) (s₁ : S),
    IsClosed {p : Kernel S A × Policy S A | risk α c p.2 p.1 H 0 s₁ ≤ τ} := by
  sorry

end

section
open Set MeasureTheory Paper36.Regularity Paper36.Nested
universe u
variable {S A : Type u} [Fintype S] [Fintype A]

open Paper36.Selection

/-- Complete declaration of `Paper36.Selection.feasible_graph_measurable`; source support: S4.Thmtheorem2. -/
theorem feasible_graph_measurable : ∀ (α τ : ℝ) (c : ℕ → S → A → ℝ)
    (H : ℕ) (s₁ : S) (Q : Set (Kernel S A)) (hQ : IsClosed Q),
    MeasurableSet {p : Kernel S A × Policy S A | p.2 ∈ feasible α τ c H s₁ Q p.1} := by
  sorry

end

section
open Set MeasureTheory Paper36.Regularity Paper36.Nested
universe u
variable {S A : Type u} [Fintype S] [Fintype A]

open Paper36.Selection

/-- Complete declaration of `Paper36.Selection.feasible_section_compact`; source support: S4.Thmtheorem2. -/
theorem feasible_section_compact : ∀ (α τ : ℝ) (c : ℕ → S → A → ℝ)
    (H : ℕ) (s₁ : S) (Q : Set (Kernel S A)) (q : Kernel S A),
    IsCompact (feasible α τ c H s₁ Q q) := by
  sorry

end

section
open Set MeasureTheory Paper36.Regularity Paper36.Nested
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [instNonemptyA : Nonempty A]

open Paper36.Selection

/-- Complete declaration of `Paper36.Selection.exists_borel_calibration`; source support: S4.Thmtheorem1. -/
include instNonemptyA in
theorem exists_borel_calibration : ∀ (external : CompactSectionMaximum.{u})
    (α : ℝ) (c : ℕ → S → A → ℝ) (H : ℕ) (s₁ : S),
    ∃ σ : Kernel S A → Policy S A, Measurable σ ∧
      ∀ q, risk α c (σ q) q H 0 s₁ = minimumRisk α c H 0 s₁ q := by
  sorry

end

section
open Set MeasureTheory Paper36.Regularity Paper36.Nested
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [instNonemptyA : Nonempty A]

open Paper36.Selection

/-- Complete declaration of `Paper36.Selection.exists_borel_exploitation`; source support: S4.Thmtheorem2. -/
include instNonemptyA in
theorem exists_borel_exploitation : ∀ (external : CompactSectionMaximum.{u})
    (α τ : ℝ) (c r : ℕ → S → A → ℝ) (H : ℕ) (s₁ : S)
    (Q : Set (Kernel S A)) (hQ : IsClosed Q)
    (hstrict : ∀ q ∈ Q, minimumRisk α c H 0 s₁ q < τ),
    ∃ σ : Kernel S A → Policy S A, Measurable σ ∧
      ∀ q ∈ Q, risk α c (σ q) q H 0 s₁ ≤ τ ∧
        ∀ π, risk α c π q H 0 s₁ ≤ τ →
          reward r π q H 0 s₁ ≤ reward r (σ q) q H 0 s₁ := by
  sorry

end

section
open Set MeasureTheory Paper36.Regularity Paper36.Nested
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [instNonemptyA : Nonempty A]

open Paper36.Selection

/-- Complete declaration of `Paper36.Selection.exists_borel_oracles`; source support: S4.Thmtheorem2. -/
include instNonemptyA in
theorem exists_borel_oracles : ∀ (external : CompactSectionMaximum.{u})
    (α τ : ℝ) (c r : ℕ → S → A → ℝ) (H : ℕ) (s₁ : S)
    (Q : Set (Kernel S A)) (hQ : IsClosed Q)
    (hstrict : ∀ q ∈ Q, minimumRisk α c H 0 s₁ q < τ),
    Nonempty (BorelAlgorithm.BorelOracles α c r H s₁ τ Q) := by
  sorry

end

end P36Contract.Selection

namespace P36Contract.FiniteStages

section
open Paper36.Simulation
variable {S A : Type*} [Fintype S] [Fintype A]

open Paper36.FiniteStages

/-- Complete declaration of `Paper36.FiniteStages.finite_mass_representation`; source support: A2.Thmtheorem3. -/
theorem finite_mass_representation : ∀ {H : ℕ} (a : Fin H → ℝ)
    (ha : ∀ i, 0 < a i ∧ a i ≤ 1),
    (∀ j, 0 < extend a j ∧ extend a j ≤ 1) ∧
    ∀ (b : ℕ → ℝ), (∀ j (hj : 1 ≤ j ∧ j ≤ H), b j = a ⟨j-1, by omega⟩) →
      ∀ (c : ℕ → S → A → ℝ) (π : Policy S A) (p : Kernel S A) (s : S),
        StageRisk.risk b c π p H 0 s = StageRisk.risk (extend a) c π p H 0 s := by
  sorry

end

section
open Paper36.Simulation
variable {S A : Type*} [Fintype S] [Fintype A]

open Paper36.FiniteStages

/-- Complete declaration of `Paper36.FiniteStages.finite_weight_representation`; source support: A2.Thmtheorem3. -/
theorem finite_weight_representation : ∀ {H : ℕ} (a : Fin H → ℝ) (b : ℕ → ℝ)
    (hb : ∀ j (hj : 1 ≤ j ∧ j ≤ H), b j = a ⟨j-1, by omega⟩),
    Weights.stageWsq b H = Weights.stageWsq (extend a) H ∧
    Weights.stagew b H = Weights.stagew (extend a) H := by
  sorry

end

end P36Contract.FiniteStages

namespace P36Contract.StageMain

section
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested Paper36.StageAlgorithm
  Paper36.StatisticalCounts Paper36.Statistical
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {Ω Info Model Hist : Type*} [MeasurableSpace Ω] [MeasurableSpace Info]
  [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model] [MeasurableSpace Hist]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℕ} {s₀ : S}
variable {E : EpisodeSystem μ Info S A (H+1) s₀}
  (P : PosteriorSystem (Model := Model) (Hist := Hist) E)

open Paper36.StageMain

/-- Complete declaration of `Paper36.StageMain.theorem_4_2`; source support: A2.Thmtheorem3, S4.Thmtheorem2. -/
theorem theorem_4_2 : ∀ (external : RowTapes.ExternalCategoricalConcentration (S := S))
    (β : ℕ → ℝ) (τ : ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1) (hτ : 0 ≤ τ)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (hstrict : ∀ q ∈ support P, ∃ π : Simulation.Policy S A,
      StageRisk.risk β c π (RiskBridge.ofKernel q) (H+1) 0 s₀ < τ)
    (O : StageAlgorithm.BorelOracles β c r (H+1) s₀ τ (support P))
    (hrun : ∀ n ω, policy P n ω = StageAlgorithm.selected O.toOracles
      (target (S := S) (A := A) (H := H) β) (samples P) n ω),
    ∀ K, 1 ≤ K →
    ((∫ ω, Assembly.total (fun n ω => trueRisk P β c n ω - τ) K ω ∂μ) ≤
      riskEnvelope (S := S) (A := A) (H := H) β (delta P β τ c)) ∧
    ((∫ ω, Assembly.total (fun n ω => optimum P β τ c r ω - trueReward P r n ω) K ω ∂μ) ≤
      rewardAllowance (S := S) (A := A) (H := H) K + (H+1 : ℝ) *
        ((target (S := S) (A := A) (H := H) β K + τ) / delta P β τ c)) ∧
    ((∫ ω, Assembly.countRV (target (S := S) (A := A) (H := H) β) (deposit P β τ c) K ω ∂μ) ≤
      min (K : ℝ) ((target (S := S) (A := A) (H := H) β K + τ) / delta P β τ c)) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested Paper36.StageAlgorithm
  Paper36.StatisticalCounts Paper36.Statistical
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {Ω Info Model Hist : Type*} [MeasurableSpace Ω] [MeasurableSpace Info]
  [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model] [MeasurableSpace Hist]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℕ} {s₀ : S}
variable {E : EpisodeSystem μ Info S A (H+1) s₀}
  (P : PosteriorSystem (Model := Model) (Hist := Hist) E)

open Paper36.StageMain

/-- Complete declaration of `Paper36.StageMain.certified_performance`; source support: A2.Thmtheorem3, A2.Thmtheorem1. -/
theorem certified_performance : ∀ (external : RowTapes.ExternalCategoricalConcentration (S := S))
    (β : ℕ → ℝ) (τ : ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1) (hτ : 0 ≤ τ)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (hstrict : ∀ q ∈ support P, ∃ π : Simulation.Policy S A,
      StageRisk.risk β c π (RiskBridge.ofKernel q) (H+1) 0 s₀ < τ)
    (O : StageAlgorithm.BorelOracles β c r (H+1) s₀ τ (support P))
    (ε ζ : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hζ : ∀ n, 0 ≤ ζ n)
    (hriskOracle : ∀ᵐ ω ∂μ, ∀ n,
      (Bank.calibrates (target (S := S) (A := A) (H := H) β) (fun j => deposit P β τ c j ω) n →
        sampledRisk P β c n ω = τ - deposit P β τ c (n+1) ω) ∧
      (¬Bank.calibrates (target (S := S) (A := A) (H := H) β) (fun j => deposit P β τ c j ω) n →
        sampledRisk P β c n ω ≤ τ + ε n))
    (hrewardOracle : ∀ᵐ ω ∂μ, ∀ n,
      (Bank.calibrates (target (S := S) (A := A) (H := H) β) (fun j => deposit P β τ c j ω) n →
        sampledOptimum P β τ c r n ω - sampledReward P r n ω ≤ (H+1 : ℝ)) ∧
      (¬Bank.calibrates (target (S := S) (A := A) (H := H) β) (fun j => deposit P β τ c j ω) n →
        sampledOptimum P β τ c r n ω - sampledReward P r n ω ≤ ζ n))
    {K : ℕ} (hK : 1 ≤ K),
    ((∫ ω, Assembly.total (fun n ω => trueRisk P β c n ω - τ) K ω ∂μ) ≤
      riskEnvelope (S := S) (A := A) (H := H) β (delta P β τ c) + ∑ n ∈ Finset.range K, ε n) ∧
    ((∫ ω, Assembly.total (fun n ω => optimum P β τ c r ω - trueReward P r n ω) K ω ∂μ) ≤
      rewardAllowance (S := S) (A := A) (H := H) K + (H+1 : ℝ) *
        ((target (S := S) (A := A) (H := H) β K + τ) / delta P β τ c) + ∑ n ∈ Finset.range K, ζ n) ∧
    ((∫ ω, Assembly.countRV (target (S := S) (A := A) (H := H) β) (deposit P β τ c) K ω ∂μ) ≤
      min (K : ℝ) ((target (S := S) (A := A) (H := H) β K + τ) / delta P β τ c)) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested Paper36.StageAlgorithm
  Paper36.StatisticalCounts Paper36.Statistical
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {Ω Info Model Hist : Type*} [MeasurableSpace Ω] [MeasurableSpace Info]
  [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model] [MeasurableSpace Hist]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℕ} {s₀ : S}
variable {E : EpisodeSystem μ Info S A (H+1) s₀}
  (P : PosteriorSystem (Model := Model) (Hist := Hist) E)

open Paper36.StageMain

/-- Complete declaration of `Paper36.StageMain.corollary_B_1`; source support: A2.Thmtheorem3, A2.Thmtheorem1. -/
theorem corollary_B_1 : ∀ (external : RowTapes.ExternalCategoricalConcentration (S := S))
    (β : ℕ → ℝ) (τ : ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1) (hτ : 0 ≤ τ)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (hstrict : ∀ q ∈ support P, ∃ π : Simulation.Policy S A,
      StageRisk.risk β c π (RiskBridge.ofKernel q) (H+1) 0 s₀ < τ)
    (O : StageAlgorithm.BorelOracles β c r (H+1) s₀ τ (support P))
    (ε ζ : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hζ : ∀ n, 0 ≤ ζ n)
    (O' : StageApproximation.Oracles β c r (H+1) s₀ τ (support P) ε ζ)
    (hrun : ∀ n ω, policy P n ω = StageApproximation.selected O'
      (target (S := S) (A := A) (H := H) β) (samples P) n ω),
    ∀ K, 1 ≤ K →
    ((∫ ω, Assembly.total (fun n ω => trueRisk P β c n ω - τ) K ω ∂μ) ≤
      riskEnvelope (S := S) (A := A) (H := H) β (delta P β τ c) + ∑ n ∈ Finset.range K, ε n) ∧
    ((∫ ω, Assembly.total (fun n ω => optimum P β τ c r ω - trueReward P r n ω) K ω ∂μ) ≤
      rewardAllowance (S := S) (A := A) (H := H) K + (H+1 : ℝ) *
        ((target (S := S) (A := A) (H := H) β K + τ) / delta P β τ c) + ∑ n ∈ Finset.range K, ζ n) ∧
    ((∫ ω, Assembly.countRV (target (S := S) (A := A) (H := H) β) (deposit P β τ c) K ω ∂μ) ≤
      min (K : ℝ) ((target (S := S) (A := A) (H := H) β K + τ) / delta P β τ c)) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested Paper36.StageAlgorithm
  Paper36.StatisticalCounts Paper36.Statistical
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {Ω Info Model Hist : Type*} [MeasurableSpace Ω] [MeasurableSpace Info]
  [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model] [MeasurableSpace Hist]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℕ} {s₀ : S}
variable {E : EpisodeSystem μ Info S A (H+1) s₀}
  (P : PosteriorSystem (Model := Model) (Hist := Hist) E)

open Paper36.StageMain

/-- Complete declaration of `Paper36.StageMain.risk_bank_certificate`; source support: A2.Thmtheorem3, S5.Thmtheorem6. -/
theorem risk_bank_certificate : ∀ (external : RowTapes.ExternalCategoricalConcentration (S := S))
    (β : ℕ → ℝ) (τ : ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (O : StageAlgorithm.BorelOracles β c r (H+1) s₀ τ (support P))
    (hrun : ∀ n ω, policy P n ω = StageAlgorithm.selected O.toOracles
      (target (S := S) (A := A) (H := H) β) (samples P) n ω)
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (hinfo : ∀ k, MeasurableSpace.comap (E.info k) inferInstance = ℱ k)
    (hpath : ∀ k, Measurable[ℱ (k+1), inferInstance] (E.path k))
    {K : ℕ} (hK : 1 ≤ K) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1),
    μ.real {ω | Bounds.certificate (Fintype.card S) (Fintype.card A) (H+1)
        (Real.sqrt (Weights.stageWsq β (H+1))) (Weights.stagew β (H+1)) δ K -
          Bank.bank (target (S := S) (A := A) (H := H) β) (fun j => deposit P β τ c j ω) K <
        Assembly.total (fun n ω => trueRisk P β c n ω - τ) K ω} ≤ δ := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested Paper36.StageAlgorithm
  Paper36.StatisticalCounts Paper36.Statistical
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {Ω Info Model Hist : Type*} [MeasurableSpace Ω] [MeasurableSpace Info]
  [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model] [MeasurableSpace Hist]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℕ} {s₀ : S}
variable {E : EpisodeSystem μ Info S A (H+1) s₀}
  (P : PosteriorSystem (Model := Model) (Hist := Hist) E)

open Paper36.StageMain

/-- Complete declaration of `Paper36.StageMain.pathwise_calibration`; source support: A2.Thmtheorem3, S4.Thmtheorem2. -/
theorem pathwise_calibration : ∀ (β : ℕ → ℝ) (τ : ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1) (hτ : 0 ≤ τ)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hstrict : ∀ q ∈ support P, ∃ π : Simulation.Policy S A,
      StageRisk.risk β c π (RiskBridge.ofKernel q) (H+1) 0 s₀ < τ),
    0 < delta P β τ c ∧
    ∀ᵐ ω ∂μ,
      (∀ K, (Bank.count (target (S := S) (A := A) (H := H) β)
        (fun j => deposit P β τ c j ω) K : ℝ) ≤
        min (K : ℝ) ((target (S := S) (A := A) (H := H) β K + τ) / delta P β τ c)) ∧
      Filter.Tendsto (fun K : ℕ =>
        (Bank.count (target (S := S) (A := A) (H := H) β)
          (fun j => deposit P β τ c j ω) K : ℝ) / (K : ℝ)) Filter.atTop (nhds 0) := by
  sorry

end

section
open Paper36.Regularity Paper36.Nested Paper36.StageAlgorithm
variable {S A Ω : Type*} [Fintype S] [Fintype A] [Nonempty A]

open Paper36.StageApproximation

/-- Complete declaration of `Paper36.StageApproximation.sampled_bank_cancellation`; source support: A2.Thmtheorem3, A2.Thmtheorem1. -/
theorem sampled_bank_cancellation : ∀ {β : ℕ → ℝ} {τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} {ε ζ : ℕ → ℝ} (O : Oracles β c r H s₁ τ Q ε ζ)
    (hε : ∀ n, 0 ≤ ε n) (T : ℕ → ℝ) (sample : ℕ → Ω → Kernel S A)
    (ω : Ω) (hs : ∀ n, sample n ω ∈ Q) (K : ℕ),
    (∑ n ∈ Finset.range K, (risk β c (selected O T sample n ω) (sample n ω) H 0 s₁ - τ)) ≤
      (∑ n ∈ Finset.range K, ε n) -
        Bank.bank T (fun j => StageAlgorithm.deposits β τ c H s₁ sample j ω) K := by
  sorry

end

section
open Paper36.Regularity Paper36.Nested Paper36.StageAlgorithm
variable {S A Ω : Type*} [Fintype S] [Fintype A] [Nonempty A]

open Paper36.StageApproximation

/-- Complete declaration of `Paper36.StageApproximation.sampled_reward_total`; source support: A2.Thmtheorem3, A2.Thmtheorem1. -/
theorem sampled_reward_total : ∀ {β : ℕ → ℝ} {τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} {ε ζ : ℕ → ℝ} (O : Oracles β c r H s₁ τ Q ε ζ)
    (exact : StageAlgorithm.Oracles β c r H s₁ τ Q) (hζ : ∀ n, 0 ≤ ζ n)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (T : ℕ → ℝ) (sample : ℕ → Ω → Kernel S A) (ω : Ω)
    (hs : ∀ n, sample n ω ∈ Q) (K : ℕ),
    (∑ n ∈ Finset.range K, (constrainedValue β c r H s₁ τ (sample n ω) -
      reward r (selected O T sample n ω) (sample n ω) H 0 s₁)) ≤
      H * (Bank.count T (fun j => StageAlgorithm.deposits β τ c H s₁ sample j ω) K : ℝ) +
        ∑ n ∈ Finset.range K, ζ n := by
  sorry

end

end P36Contract.StageMain

namespace P36Contract.AdaptiveKernel

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories Paper36.AdaptiveTapes
open scoped ENNReal
variable {S Row Hist : Type*} [Fintype S] [Fintype Row] [DecidableEq Row]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace Row] [DiscreteMeasurableSpace Row] [MeasurableSpace Hist]

open Paper36.AdaptiveKernel

/-- Complete declaration of `Paper36.AdaptiveKernel.adaptive_kernel_coupling`; source support: S5.Thmtheorem5. -/
theorem adaptive_kernel_coupling : ∀ (P : Row → Law S)
    (choose : ProbabilityTheory.Kernel Hist (Row × Hist)) [IsSFiniteKernel choose]
    (update : Hist × (Row × S) → Hist) (hupdate : Measurable update)
    (payoff : Hist → ℝ≥0∞) (hpayoff : Measurable payoff) (n : ℕ) (h : Hist),
    (∫⁻ tape, tapedLValue choose update payoff n h tape ∂lawMeasure (stackLaw P n)) =
      onlineLValue P choose update payoff n h := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories Paper36.AdaptiveTapes
open scoped ENNReal
variable {S Row Hist : Type*} [Fintype S] [Fintype Row] [DecidableEq Row]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace Row] [DiscreteMeasurableSpace Row] [MeasurableSpace Hist]

open Paper36.AdaptiveKernel

/-- Complete declaration of `Paper36.AdaptiveKernel.adaptive_kernel_unused_independent`; source support: S5.Thmtheorem5. -/
theorem adaptive_kernel_unused_independent : ∀ (P : Row → Law S)
    (choose : ProbabilityTheory.Kernel Hist (Row × Hist)) [IsSFiniteKernel choose]
    (update : Hist × (Row × S) → Hist) (hupdate : Measurable update)
    (L : ℕ) (payoff : Hist × Stack Row S L → ℝ≥0∞) (hpayoff : Measurable payoff) (n : ℕ) (h : Hist),
    (∫⁻ tape, residualLValue choose update L payoff n h tape ∂lawMeasure (stackLaw P (L+n))) =
      onlineLValue P choose update (fun h => ∫⁻ tape, payoff (h,tape) ∂lawMeasure (stackLaw P L)) n h := by
  sorry

end

end P36Contract.AdaptiveKernel

namespace P36Contract.AdaptiveKernelLaw

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories Paper36.AdaptiveTapes
open scoped ENNReal
variable {S Row Hist : Type*} [Fintype S] [Fintype Row] [DecidableEq Row]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace Row] [DiscreteMeasurableSpace Row] [MeasurableSpace Hist]

open Paper36.AdaptiveKernel

/-- Complete declaration of `Paper36.AdaptiveKernel.rawExecution_tape`; source support: S5.Thmtheorem5. -/
theorem rawExecution_tape : ∀ (P : Row → Law S) (choose : ProbabilityTheory.Kernel Hist (Row × Hist))
    [IsMarkovKernel choose] (update : Hist × (Row × S) → Hist) (hupdate : Measurable update)
    (L n : ℕ) (h : Hist),
    (rawExecution P choose update hupdate L n h).map Prod.fst = lawMeasure (stackLaw P (L+n)) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories Paper36.AdaptiveTapes
open scoped ENNReal
variable {S Row Hist : Type*} [Fintype S] [Fintype Row] [DecidableEq Row]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace Row] [DiscreteMeasurableSpace Row] [MeasurableSpace Hist]

open Paper36.AdaptiveKernel

/-- Complete declaration of `Paper36.AdaptiveKernel.rawExecution_joint`; source support: S5.Thmtheorem5. -/
theorem rawExecution_joint : ∀ (P : Row → Law S) (choose : ProbabilityTheory.Kernel Hist (Row × Hist))
    [IsMarkovKernel choose] (update : Hist × (Row × S) → Hist) (hupdate : Measurable update)
    (L n : ℕ) (h : Hist),
    (rawExecution P choose update hupdate L n h).map Prod.snd =
      (onlineKernel P choose update n h).prod (lawMeasure (stackLaw P L)) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories Paper36.AdaptiveTapes
open scoped ENNReal
variable {S Row Hist : Type*} [Fintype S] [Fintype Row] [DecidableEq Row]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace Row] [DiscreteMeasurableSpace Row] [MeasurableSpace Hist]

open Paper36.AdaptiveKernel

/-- Complete declaration of `Paper36.AdaptiveKernel.rawExecution_history`; source support: S5.Thmtheorem5. -/
theorem rawExecution_history : ∀ (P : Row → Law S) (choose : ProbabilityTheory.Kernel Hist (Row × Hist))
    [IsMarkovKernel choose] (update : Hist × (Row × S) → Hist) (hupdate : Measurable update)
    (L n : ℕ) (h : Hist),
    (rawExecution P choose update hupdate L n h).map (fun z => z.2.1) = onlineKernel P choose update n h := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories Paper36.AdaptiveTapes
open scoped ENNReal
variable {S Row Hist : Type*} [Fintype S] [Fintype Row] [DecidableEq Row]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace Row] [DiscreteMeasurableSpace Row] [MeasurableSpace Hist]

open Paper36.AdaptiveKernel

/-- Complete declaration of `Paper36.AdaptiveKernel.rawExecution_unused_condDistrib`; source support: S5.Thmtheorem5. -/
theorem rawExecution_unused_condDistrib : ∀ [Nonempty S]
    (P : Row → Law S) (choose : ProbabilityTheory.Kernel Hist (Row × Hist)) [IsMarkovKernel choose]
    (update : Hist × (Row × S) → Hist) (hupdate : Measurable update) (L n : ℕ) (h : Hist),
    condDistrib (fun z : Stack Row S (L+n) × (Hist × Stack Row S L) => z.2.2)
      (fun z => z.2.1) (rawExecution P choose update hupdate L n h) =ᵐ[onlineKernel P choose update n h]
        Kernel.const Hist (lawMeasure (stackLaw P L)) := by
  sorry

end

end P36Contract.AdaptiveKernelLaw

namespace P36Contract.InfiniteExecution

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories Paper36.AdaptiveTapes
open scoped ENNReal
variable {S Row Hist : Type*} [Fintype S] [Fintype Row] [DecidableEq Row]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace Row] [DiscreteMeasurableSpace Row] [MeasurableSpace Hist]

open Paper36.AdaptiveKernel

/-- Complete declaration of `Paper36.AdaptiveKernel.infiniteExecution_tape`; source support: S5.Thmtheorem5. -/
theorem infiniteExecution_tape : ∀ (P : Row → Law S) (choose : ProbabilityTheory.Kernel Hist (Row × Hist))
    [IsMarkovKernel choose] (update : Hist × (Row × S) → Hist) (hupdate : Measurable update)
    (L n : ℕ) (h : Hist),
    (infiniteExecution P choose update hupdate L n h).map Prod.fst =
      InfiniteTapes.infiniteLaw (fun c : Row × ℕ => P c.1) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories Paper36.AdaptiveTapes
open scoped ENNReal
variable {S Row Hist : Type*} [Fintype S] [Fintype Row] [DecidableEq Row]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace Row] [DiscreteMeasurableSpace Row] [MeasurableSpace Hist]

open Paper36.AdaptiveKernel

/-- Complete declaration of `Paper36.AdaptiveKernel.infiniteExecution_joint`; source support: S5.Thmtheorem5. -/
theorem infiniteExecution_joint : ∀ (P : Row → Law S) (choose : ProbabilityTheory.Kernel Hist (Row × Hist))
    [IsMarkovKernel choose] (update : Hist × (Row × S) → Hist) (hupdate : Measurable update)
    (L n : ℕ) (h : Hist),
    (infiniteExecution P choose update hupdate L n h).map Prod.snd =
      (onlineKernel P choose update n h).prod (lawMeasure (stackLaw P L)) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories
open scoped ENNReal
variable {M Row S Aux : Type*} [MeasurableSpace M] [Fintype S] [Nonempty S]
  [MeasurableSpace S] [DiscreteMeasurableSpace S] [MeasurableSpace Aux]

open Paper36.InfiniteTapes

/-- Complete declaration of `Paper36.InfiniteTapes.priorTapes_prefix_after_extension`; source support: S5.Thmtheorem5. -/
theorem priorTapes_prefix_after_extension : ∀ (ν : Measure M) [IsProbabilityMeasure ν] (P : M → Row → Law S)
    (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (κ : ProbabilityTheory.Kernel (M × (Row × ℕ → S)) Aux) [IsMarkovKernel κ]
    (r : Row) (n : ℕ),
    condDistrib (fun x : (M × (Row × ℕ → S)) × Aux => tapePrefix r n x.1.2)
      (fun x => x.1.1) (priorTapes ν P hP ⊗ₘ κ) =ᵐ[ν]
        Paper36.RowTapes.iidKernel (fun m => P m r) (hP r) n := by
  sorry

end

end P36Contract.InfiniteExecution

namespace P36Contract.Scope

section
open Paper36.Regularity Paper36.Nested Paper36.CVaR Paper36.Trajectories

open Paper36.Scope

/-- Complete declaration of `Paper36.Scope.realized_cost_not_pathwise_controlled`; source support: S2.Thmtheorem2, S5.Thmtheorem7. -/
theorem realized_cost_not_pathwise_controlled : ∀ (G : ℝ),
    (∀ K, (∑ _n ∈ Finset.range K,
      (Nested.risk 1 Endpoints.exampleCost policy Endpoints.exampleKernel 1 0 () - (1:ℝ)/2)) = 0) ∧
    ∃ K, ∃ paths : Fin K → Trajectory Unit Bool 1,
      0 < (episodes K).mass paths ∧ G < realizedDebt paths := by
  sorry

end

section
open Paper36.Regularity Paper36.Nested Paper36.CVaR Paper36.Trajectories

open Paper36.Scope

/-- Complete declaration of `Paper36.Scope.fixed_certificate_does_not_certify_realized_cost`; source support: S2.Thmtheorem2, S5.Thmtheorem7. -/
theorem fixed_certificate_does_not_certify_realized_cost : Nested.risk 1 Endpoints.exampleCost policy Endpoints.exampleKernel 1 0 () - (1:ℝ)/2 = 0 ∧
    trajectoryLaw.mass highPath = (1:ℝ)/2 ∧
    Bounds.certificate 1 2 1 (Weights.W 1 1) (Weights.w 1 1) ((1:ℝ)/4) 1 <
      Endpoints.exampleCost 0 () highPath.2.1 - (1:ℝ)/2 := by
  sorry

end

end P36Contract.Scope

namespace P36Contract.StageSelection

section
open Set MeasureTheory Paper36.Regularity Paper36.Nested
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [instNonemptyA : Nonempty A]
variable (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
  (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1) (H : ℕ) (s₁ : S)

open Paper36.StageSelection

/-- Complete declaration of `Paper36.StageSelection.feasible_graph_closed`; source support: A2.Thmtheorem3. -/
include hβ hc in
theorem feasible_graph_closed : ∀ (τ : ℝ),
    IsClosed {p : Kernel S A × Policy S A | StageAlgorithm.risk β c p.2 p.1 H 0 s₁ ≤ τ} := by
  sorry

end

section
open Set MeasureTheory Paper36.Regularity Paper36.Nested
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [instNonemptyA : Nonempty A]
variable (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
  (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1) (H : ℕ) (s₁ : S)

open Paper36.StageSelection

/-- Complete declaration of `Paper36.StageSelection.feasible_section_compact`; source support: A2.Thmtheorem3. -/
include hβ hc in
theorem feasible_section_compact : ∀ (τ : ℝ) (Q : Set (Kernel S A)) (q : Kernel S A),
    IsCompact (feasible β τ c H s₁ Q q) := by
  sorry

end

section
open Set MeasureTheory Paper36.Regularity Paper36.Nested
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [instNonemptyA : Nonempty A]
variable (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
  (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1) (H : ℕ) (s₁ : S)

open Paper36.StageSelection

/-- Complete declaration of `Paper36.StageSelection.exists_borel_calibration`; source support: A2.Thmtheorem3. -/
include hβ hc in
theorem exists_borel_calibration : ∀ (external : Selection.CompactSectionMaximum.{u}),
    ∃ σ : Kernel S A → Policy S A, Measurable σ ∧ ∀ q,
      StageAlgorithm.risk β c (σ q) q H 0 s₁ = StageAlgorithm.minimumRisk β c H s₁ q ∧
      StageCalibration.Deterministic (RiskBridge.ofPolicy (σ q)) := by
  sorry

end

section
open Set MeasureTheory Paper36.Regularity Paper36.Nested
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [instNonemptyA : Nonempty A]
variable (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
  (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1) (H : ℕ) (s₁ : S)

open Paper36.StageSelection

/-- Complete declaration of `Paper36.StageSelection.exists_borel_exploitation`; source support: A2.Thmtheorem3. -/
include hβ hc instNonemptyA in
theorem exists_borel_exploitation : ∀ (external : Selection.CompactSectionMaximum.{u})
    (τ : ℝ) (r : ℕ → S → A → ℝ) (Q : Set (Kernel S A)) (hQ : IsClosed Q)
    (hstrict : ∀ q ∈ Q, ∃ π : Simulation.Policy S A,
      StageRisk.risk β c π (RiskBridge.ofKernel q) H 0 s₁ < τ),
    ∃ σ : Kernel S A → Policy S A, Measurable σ ∧ ∀ q ∈ Q,
      StageAlgorithm.risk β c (σ q) q H 0 s₁ ≤ τ ∧ ∀ π,
        StageAlgorithm.risk β c π q H 0 s₁ ≤ τ →
          Nested.reward r π q H 0 s₁ ≤ Nested.reward r (σ q) q H 0 s₁ := by
  sorry

end

section
open Set MeasureTheory Paper36.Regularity Paper36.Nested
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [instNonemptyA : Nonempty A]
variable (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
  (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1) (H : ℕ) (s₁ : S)

open Paper36.StageSelection

/-- Complete declaration of `Paper36.StageSelection.exists_borel_oracles`; source support: A2.Thmtheorem3. -/
include hβ hc in
theorem exists_borel_oracles : ∀ (external : Selection.CompactSectionMaximum.{u})
    (τ : ℝ) (r : ℕ → S → A → ℝ) (Q : Set (Kernel S A)) (hQ : IsClosed Q)
    (hstrict : ∀ q ∈ Q, ∃ π : Simulation.Policy S A,
      StageRisk.risk β c π (RiskBridge.ofKernel q) H 0 s₁ < τ),
    Nonempty (StageAlgorithm.BorelOracles β c r H s₁ τ Q) := by
  sorry

end

end P36Contract.StageSelection

namespace P36Contract.StageEndpoints

section
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested Paper36.StageAlgorithm
  Paper36.StatisticalCounts Paper36.Statistical
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {Ω Info Model Hist : Type*} [MeasurableSpace Ω] [MeasurableSpace Info]
  [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model] [MeasurableSpace Hist]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {s₀ : S}
variable {E : EpisodeSystem μ Info S A 1 s₀}
  (P : PosteriorSystem (Model := Model) (Hist := Hist) E)

open Paper36.StageMain

/-- Complete declaration of `Paper36.StageMain.theorem_4_2_horizon_one`; source support: A2.Thmtheorem3, S4.Thmtheorem2. -/
theorem theorem_4_2_horizon_one : ∀ (β : ℕ → ℝ) (τ : ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (O : StageAlgorithm.BorelOracles β c r 1 s₀ τ (support P))
    (hrun : ∀ n ω, policy P n ω = StageAlgorithm.selected O.toOracles
      (target (S := S) (A := A) (H := 0) β) (samples P) n ω) (K : ℕ),
    ((∫ ω, Assembly.total (fun n ω => trueRisk P β c n ω - τ) K ω ∂μ) ≤ 0) ∧
    ((∫ ω, Assembly.total (fun n ω => optimum P β τ c r ω - trueReward P r n ω) K ω ∂μ) = 0) ∧
    (∀ ω, Bank.bank (target (S := S) (A := A) (H := 0) β) (fun j => deposit P β τ c j ω) K = 0 ∧
      Bank.count (target (S := S) (A := A) (H := 0) β) (fun j => deposit P β τ c j ω) K = 0) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested Paper36.StageAlgorithm
  Paper36.StatisticalCounts Paper36.Statistical
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {Ω Info Model Hist : Type*} [MeasurableSpace Ω] [MeasurableSpace Info]
  [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model] [MeasurableSpace Hist]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {s₀ : S}
variable {E : EpisodeSystem μ Info S A 1 s₀}
  (P : PosteriorSystem (Model := Model) (Hist := Hist) E)

open Paper36.StageMain

/-- Complete declaration of `Paper36.StageMain.corollary_B_1_horizon_one`; source support: A2.Thmtheorem3, A2.Thmtheorem1. -/
theorem corollary_B_1_horizon_one : ∀ (β : ℕ → ℝ) (τ : ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (O : StageAlgorithm.BorelOracles β c r 1 s₀ τ (support P))
    (ε ζ : ℕ → ℝ)
    (O' : StageApproximation.Oracles β c r 1 s₀ τ (support P) ε ζ)
    (hrun : ∀ n ω, policy P n ω = StageApproximation.selected O'
      (target (S := S) (A := A) (H := 0) β) (samples P) n ω) (K : ℕ),
    ((∫ ω, Assembly.total (fun n ω => trueRisk P β c n ω - τ) K ω ∂μ) ≤ ∑ n ∈ Finset.range K, ε n) ∧
    ((∫ ω, Assembly.total (fun n ω => optimum P β τ c r ω - trueReward P r n ω) K ω ∂μ) ≤
      ∑ n ∈ Finset.range K, ζ n) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested Paper36.StageAlgorithm
  Paper36.StatisticalCounts Paper36.Statistical
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {Ω Info Model Hist : Type*} [MeasurableSpace Ω] [MeasurableSpace Info]
  [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model] [MeasurableSpace Hist]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {s₀ : S}
variable {E : EpisodeSystem μ Info S A 1 s₀}
  (P : PosteriorSystem (Model := Model) (Hist := Hist) E)

open Paper36.StageMain

/-- Complete declaration of `Paper36.StageMain.risk_bank_certificate_horizon_one`; source support: A2.Thmtheorem3, S5.Thmtheorem6. -/
theorem risk_bank_certificate_horizon_one : ∀ (β : ℕ → ℝ) (τ : ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (O : StageAlgorithm.BorelOracles β c r 1 s₀ τ (support P))
    (hrun : ∀ n ω, policy P n ω = StageAlgorithm.selected O.toOracles
      (target (S := S) (A := A) (H := 0) β) (samples P) n ω) (δ : ℝ) (K : ℕ),
    μ.real {ω | Bounds.certificate (Fintype.card S) (Fintype.card A) 1
        (Real.sqrt (Weights.stageWsq β 1)) (Weights.stagew β 1) δ K -
          Bank.bank (target (S := S) (A := A) (H := 0) β) (fun j => deposit P β τ c j ω) K <
        Assembly.total (fun n ω => trueRisk P β c n ω - τ) K ω} = 0 := by
  sorry

end

section
open MeasureTheory Paper36.Regularity Paper36.Nested Paper36.StageAlgorithm
variable {S A Ω : Type*} [Fintype S] [Fintype A] [Nonempty A]

open Paper36.StageEndpoints

/-- Complete declaration of `Paper36.StageEndpoints.horizon_one_any_prior`; source support: A2.Thmtheorem3, S4.Thmtheorem2. -/
theorem horizon_one_any_prior : ∀ [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {β : ℕ → ℝ} (hβ : ∀ j, 0 < β j ∧ β j ≤ 1) {τ : ℝ}
    {c r : ℕ → S → A → ℝ} (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    {s₁ : S} {Q : Set (Kernel S A)} (O : Oracles β c r 1 s₁ τ Q)
    (sample : ℕ → Ω → Kernel S A) (latent : Ω → Kernel S A)
    (hsupport : ∀ᵐ ω ∂μ, latent ω ∈ Q ∧ ∀ n, sample n ω ∈ Q) (K : ℕ),
    ((∫ ω, ∑ n ∈ Finset.range K,
      (risk β c (selected O (StageCharging.stageTarget (S := S) (A := A) β 1) sample n ω)
        (latent ω) 1 0 s₁ - τ) ∂μ) ≤ 0) ∧
    ((∫ ω, ∑ n ∈ Finset.range K,
      (constrainedValue β c r 1 s₁ τ (latent ω) -
        reward r (selected O (StageCharging.stageTarget (S := S) (A := A) β 1) sample n ω)
          (latent ω) 1 0 s₁) ∂μ) = 0) ∧
    (∀ ω, Bank.bank (StageCharging.stageTarget (S := S) (A := A) β 1)
      (fun j => deposits β τ c 1 s₁ sample j ω) K = 0 ∧
      Bank.count (StageCharging.stageTarget (S := S) (A := A) β 1)
        (fun j => deposits β τ c 1 s₁ sample j ω) K = 0) := by
  sorry

end

end P36Contract.StageEndpoints

namespace P36Contract.MainRealized

section
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested Paper36.Algorithm
  Paper36.StatisticalCounts Paper36.Statistical
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {Ω Info Model Hist : Type*} [MeasurableSpace Ω] [MeasurableSpace Info]
  [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model] [MeasurableSpace Hist]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℕ} {s₀ : S}
variable {E : EpisodeSystem μ Info S A (H+1) s₀}
  (P : PosteriorSystem (Model := Model) (Hist := Hist) E)

open Paper36.Main

/-- Complete declaration of `Paper36.Main.corollary_B_1_realized_calls`; source support: A2.Thmtheorem1. -/
theorem corollary_B_1_realized_calls : ∀ (external : RowTapes.ExternalCategoricalConcentration (S := S))
    (α τ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hτ : 0 ≤ τ)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (hstrict : ∀ q ∈ support P, minimumRisk α c (H+1) 0 s₀ q < τ)
    (O : BorelAlgorithm.BorelOracles α c r (H+1) s₀ τ (support P))
    (ε ζ : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hζ : ∀ n, 0 ≤ ζ n)
    (hcert : ∀ᵐ ω ∂μ, RealizedCertificates P α τ c r ε ζ ω),
    ∀ K, 1 ≤ K →
    ((∫ ω, Assembly.total (fun n ω => trueRisk P α c n ω - τ) K ω ∂μ) ≤
      SourceBank.riskEnvelope (S := S) (A := A) α (delta P α τ c) (H+1) + ∑ n ∈ Finset.range K, ε n) ∧
    ((∫ ω, Assembly.total (fun n ω => optimum P α τ c r ω - trueReward P r n ω) K ω ∂μ) ≤
      rewardAllowance (S := S) (A := A) (H := H) K + (H+1 : ℝ) *
        ((target (S := S) (A := A) (H := H) α K + τ) / delta P α τ c) + ∑ n ∈ Finset.range K, ζ n) ∧
    ((∫ ω, Assembly.countRV (target (S := S) (A := A) (H := H) α) (deposit P α τ c) K ω ∂μ) ≤
      min (K : ℝ) ((target (S := S) (A := A) (H := H) α K + τ) / delta P α τ c)) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested Paper36.Algorithm
  Paper36.StatisticalCounts Paper36.Statistical
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {Ω Info Model Hist : Type*} [MeasurableSpace Ω] [MeasurableSpace Info]
  [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model] [MeasurableSpace Hist]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {s₀ : S}
variable {E : EpisodeSystem μ Info S A 1 s₀}
  (P : PosteriorSystem (Model := Model) (Hist := Hist) E)

open Paper36.Main

/-- Complete declaration of `Paper36.Main.corollary_B_1_horizon_one_realized_calls`; source support: A2.Thmtheorem1. -/
theorem corollary_B_1_horizon_one_realized_calls : ∀ (α τ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (O : BorelAlgorithm.BorelOracles α c r 1 s₀ τ (support P))
    (ε ζ : ℕ → ℝ) (hcert : ∀ᵐ ω ∂μ, RealizedCertificates P α τ c r ε ζ ω) (K : ℕ),
    ((∫ ω, Assembly.total (fun n ω => trueRisk P α c n ω - τ) K ω ∂μ) ≤ ∑ n ∈ Finset.range K, ε n) ∧
    ((∫ ω, Assembly.total (fun n ω => optimum P α τ c r ω - trueReward P r n ω) K ω ∂μ) ≤
      ∑ n ∈ Finset.range K, ζ n) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested Paper36.Algorithm
  Paper36.StatisticalCounts Paper36.Statistical
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {Ω Info Model Hist : Type*} [MeasurableSpace Ω] [MeasurableSpace Info]
  [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model] [MeasurableSpace Hist]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {s₀ : S}
variable {E : EpisodeSystem μ Info S A 1 s₀}
  (P : PosteriorSystem (Model := Model) (Hist := Hist) E)

open Paper36.Main

/-- Complete declaration of `Paper36.Main.theorem_4_2_horizon_one_realized_calls`; source support: S4.Thmtheorem2. -/
theorem theorem_4_2_horizon_one_realized_calls : ∀ (α τ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (O : BorelAlgorithm.BorelOracles α c r 1 s₀ τ (support P))
    (hcert : ∀ᵐ ω ∂μ, RealizedCertificates P α τ c r (fun _ => 0) (fun _ => 0) ω) (K : ℕ),
    ((∫ ω, Assembly.total (fun n ω => trueRisk P α c n ω - τ) K ω ∂μ) ≤ 0) ∧
    ((∫ ω, Assembly.total (fun n ω => optimum P α τ c r ω - trueReward P r n ω) K ω ∂μ) = 0) ∧
    (∀ ω, Bank.bank (target (S := S) (A := A) (H := 0) α) (fun j => deposit P α τ c j ω) K = 0 ∧
      Bank.count (target (S := S) (A := A) (H := 0) α) (fun j => deposit P α τ c j ω) K = 0) := by
  sorry

end

end P36Contract.MainRealized

namespace P36Contract.ComplexityEncoding

section
open Paper36.Complexity MvPolynomial

open Paper36.ComplexityEncoding

/-- Complete declaration of `Paper36.ComplexityEncoding.rep_of_input_bits`; source support: S6.Thmtheorem1, S6.Thmtheorem2. -/
theorem rep_of_input_bits : ∀ (q : ℚ) {b : ℕ}
    (hn : Nat.size q.num.natAbs ≤ b) (hd : Nat.size q.den ≤ b),
    HasRep q b := by
  sorry

end

section
open Paper36.Complexity MvPolynomial

open Paper36.ComplexityEncoding

/-- Complete declaration of `Paper36.ComplexityEncoding.positive_pair_payload`; source support: S6.Thmtheorem2. -/
theorem positive_pair_payload : ∀ {q : ℚ} {b : ℕ} (hq : HasRep q b),
    ∃ n : ℤ, ∃ d : ℕ, 0 < d ∧ q = (n : ℚ)/(d : ℚ) ∧
      Nat.size n.natAbs + Nat.size d + 2 ≤ 2*b+4 := by
  sorry

end

section
open Paper36.Complexity MvPolynomial

open Paper36.ComplexityEncoding

/-- Complete declaration of `Paper36.ComplexityEncoding.clear_finite_denominators`; source support: S6.Thmtheorem2. -/
theorem clear_finite_denominators : ∀ {I : Type*} [Fintype I] {b : ℕ}
    (q : I → ℚ) (hq : ∀ i, HasRep (q i) b),
    ∃ D : ℕ, ∃ N : I → ℤ, 0 < D ∧ D ≤ 2^(b*(Fintype.card I+1)) ∧
      ∀ i, q i = (N i:ℚ)/(D:ℚ) ∧ (N i).natAbs ≤ 2^(b*(Fintype.card I+1)) := by
  sorry

end

section
open Paper36.Complexity MvPolynomial

open Paper36.ComplexityEncoding

/-- Complete declaration of `Paper36.ComplexityEncoding.one_state_LP_coefficients_rep`; source support: S6.Thmtheorem2. -/
theorem one_state_LP_coefficients_rep : ∀ {H b : ℕ} {α τ target : ℚ}
    {c₀ c₁ r₀ r₁ : Fin H → ℚ} (input : LPInputBound α τ target c₀ c₁ r₀ r₁ b)
    (ha : α ≠ 0) (piece : Fin H → Bool),
    (∀ k j, HasRep (oneStateLinearCoefficients α c₀ c₁ r₀ r₁ piece k j) ((H+1)*(4*b+3))) ∧
    (∀ k, HasRep (oneStateLinearBound α τ target c₀ c₁ r₀ r₁ piece k) ((H+1)*(4*b+3))) := by
  sorry

end

section
open Paper36.Complexity MvPolynomial

open Paper36.ComplexityEncoding

/-- Complete declaration of `Paper36.ComplexityEncoding.one_state_LP_total_payload`; source support: S6.Thmtheorem2. -/
theorem one_state_LP_total_payload : ∀ {H b : ℕ} {α τ target : ℚ}
    {c₀ c₁ r₀ r₁ : Fin H → ℚ} (input : LPInputBound α τ target c₀ c₁ r₀ r₁ b)
    (ha : α ≠ 0) (piece : Fin H → Bool),
    let q : OneStateLinearAtom H × Option (Fin H) → ℚ := fun x =>
      x.2.elim (oneStateLinearBound α τ target c₀ c₁ r₀ r₁ piece x.1)
        (oneStateLinearCoefficients α c₀ c₁ r₀ r₁ piece x.1)
    ∃ n : OneStateLinearAtom H × Option (Fin H) → ℤ,
      ∃ d : OneStateLinearAtom H × Option (Fin H) → ℕ,
      (∀ x : OneStateLinearAtom H × Option (Fin H), 0 < d x ∧ q x = (n x:ℚ)/(d x:ℚ)) ∧
      (Finset.sum Finset.univ (fun x : OneStateLinearAtom H × Option (Fin H) => Nat.size ((n x).natAbs) + Nat.size (d x) + 2)) ≤
        ((3*H+2)*(H+1))*(2*((H+1)*(4*b+3))+4) := by
  sorry

end

section
open Paper36.Complexity MvPolynomial

open Paper36.ComplexityEncoding

/-- Complete declaration of `Paper36.ComplexityEncoding.planningTerm_sum`; source support: S6.Thmtheorem2. -/
theorem planningTerm_sum : ∀ {H : ℕ} {S A : Type*} [Fintype S] [Fintype A]
    (r c : Fin H → S → A → ℚ) (p : S → A → S → ℚ)
    (α τ target : ℚ) (s₀ : S) (k : PlanningConstraint H S A),
    (∑ j : TermIndex S A, (planningTerm r c p α τ target s₀ k j).polynomial) =
      planningPolynomial r c p α τ target s₀ k := by
  sorry

end

section
open Paper36.Complexity MvPolynomial

open Paper36.ComplexityEncoding

/-- Complete declaration of `Paper36.ComplexityEncoding.planningTerm_count`; source support: S6.Thmtheorem2. -/
theorem planningTerm_count : ∀ {S A : Type*} [Fintype S] [Fintype A],
    Fintype.card (TermIndex S A) = 4+Fintype.card A+Fintype.card A*Fintype.card S := by
  sorry

end

section
open Paper36.Complexity MvPolynomial

open Paper36.ComplexityEncoding

/-- Complete declaration of `Paper36.ComplexityEncoding.planningTerm_scalar_payload`; source support: S6.Thmtheorem2. -/
theorem planningTerm_scalar_payload : ∀ {H b : ℕ} {S A : Type*}
    {r c : Fin H → S → A → ℚ} {p : S → A → S → ℚ} {α τ target : ℚ}
    (input : ETRInputBound r c p α τ target b) (ha : α ≠ 0) (s₀ : S)
    (k : PlanningConstraint H S A) (j : TermIndex S A),
    ∃ n : ℤ, ∃ d : ℕ, 0 < d ∧
      (planningTerm r c p α τ target s₀ k j).coefficient = (n:ℚ)/(d:ℚ) ∧
        Nat.size n.natAbs + Nat.size d + 2 ≤ 4*b+4 := by
  sorry

end

section
open Paper36.Complexity MvPolynomial

open Paper36.ComplexityEncoding

/-- Complete declaration of `Paper36.ComplexityEncoding.planningTerm_integer_clear`; source support: S6.Thmtheorem2. -/
theorem planningTerm_integer_clear : ∀ {H b : ℕ} {S A : Type*} [Fintype S] [Fintype A]
    {r c : Fin H → S → A → ℚ} {p : S → A → S → ℚ} {α τ target : ℚ}
    (input : ETRInputBound r c p α τ target b) (ha : α ≠ 0) (s₀ : S)
    (k : PlanningConstraint H S A),
    ∃ D : ℕ, ∃ N : TermIndex S A → ℤ, 0 < D ∧
      D ≤ 2^(2*b*(5+Fintype.card A+Fintype.card A*Fintype.card S)) ∧
      ∀ j, (planningTerm r c p α τ target s₀ k j).coefficient = (N j:ℚ)/(D:ℚ) ∧
        (N j).natAbs ≤ 2^(2*b*(5+Fintype.card A+Fintype.card A*Fintype.card S)) := by
  sorry

end

section
open Paper36.Complexity MvPolynomial

open Paper36.ComplexityEncoding
open Paper36.ComplexityEncoding.Term

/-- Complete declaration of `Paper36.ComplexityEncoding.Term.variableBits_bound`; source support: S6.Thmtheorem2. -/
theorem Term__variableBits_bound : ∀ {V : Type*} [Fintype V] (t : Term V),
    t.variableBits ≤ 2*(Nat.size (Fintype.card V)+1) := by
  sorry

end

section
open Paper36.Complexity MvPolynomial

open Paper36.ComplexityEncoding

/-- Complete declaration of `Paper36.ComplexityEncoding.planningTerm_total_payload`; source support: S6.Thmtheorem2. -/
theorem planningTerm_total_payload : ∀ {H b : ℕ} {S A : Type*} [Fintype S] [Fintype A]
    {r c : Fin H → S → A → ℚ} {p : S → A → S → ℚ} {α τ target : ℚ}
    (input : ETRInputBound r c p α τ target b) (ha : α ≠ 0) (s₀ : S),
    ∃ n : PlanningConstraint H S A × TermIndex S A → ℤ,
      ∃ d : PlanningConstraint H S A × TermIndex S A → ℕ,
      (∀ x : PlanningConstraint H S A × TermIndex S A, 0 < d x ∧ (planningTerm r c p α τ target s₀ x.1 x.2).coefficient = (n x:ℚ)/(d x:ℚ)) ∧
      (Finset.sum Finset.univ (fun x : PlanningConstraint H S A × TermIndex S A =>
        Nat.size ((n x).natAbs) + Nat.size (d x) + 2 +
          (planningTerm r c p α τ target s₀ x.1 x.2).variableBits)) ≤
        Fintype.card (PlanningConstraint H S A)*(4+Fintype.card A+Fintype.card A*Fintype.card S)*
          (4*b+4+2*(Nat.size (Fintype.card (PlanningVar H S A))+1)) := by
  sorry

end

section
open Paper36.Complexity MvPolynomial

open Paper36.ComplexityEncoding

/-- Complete declaration of `Paper36.ComplexityEncoding.planning_dimensions_le_scalar_count`; source support: S6.Thmtheorem1, S6.Thmtheorem2. -/
theorem planning_dimensions_le_scalar_count : ∀ (H S A : ℕ) (hS : 0 < S) (hA : 0 < A),
    H ≤ 2*H*S*A+S*A*S+3 ∧ S ≤ 2*H*S*A+S*A*S+3 ∧ A ≤ 2*H*S*A+S*A*S+3 := by
  sorry

end

end P36Contract.ComplexityEncoding

namespace P36Contract.GapBounds

section
open Set MeasureTheory Paper36.Regularity Paper36.Nested
variable {S A : Type*} [Fintype S] [Fintype A] [instNonemptyA : Nonempty A]

open Paper36.Prior

/-- Complete declaration of `Paper36.Prior.max_minimumRisk_bounds`; source support: S2.Thmtheorem1, S4.Thmtheorem2. -/
include instNonemptyA in
theorem max_minimumRisk_bounds : ∀ (ν : Measure (Kernel S A)) [IsProbabilityMeasure ν]
    (α : ℝ) (hα : 0 ≤ α) (H : ℕ)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1) (s₀ : S),
    0 ≤ sSup (minimumRisk α c H 0 s₀ '' ν.support) ∧
      sSup (minimumRisk α c H 0 s₀ '' ν.support) ≤ H := by
  sorry

end

section
open Set MeasureTheory Paper36.Regularity Paper36.Nested
variable {S A : Type*} [Fintype S] [Fintype A] [instNonemptyA : Nonempty A]

open Paper36.Prior

/-- Complete declaration of `Paper36.Prior.induced_gap_budget_bounds`; source support: S2.Thmtheorem1, S4.Thmtheorem2. -/
include instNonemptyA in
theorem induced_gap_budget_bounds : ∀ (ν : Measure (Kernel S A)) [IsProbabilityMeasure ν]
    (α τ : ℝ) (hα : 0 ≤ α) (H : ℕ)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1) (s₀ : S),
    τ - (H:ℝ) ≤ τ - sSup (minimumRisk α c H 0 s₀ '' ν.support) ∧
    τ - sSup (minimumRisk α c H 0 s₀ '' ν.support) ≤ τ ∧
    τ ≤ (τ - sSup (minimumRisk α c H 0 s₀ '' ν.support)) + H := by
  sorry

end

end P36Contract.GapBounds

namespace P36Contract.PolylogScaling

section

open Paper36.PolylogScaling

/-- Complete declaration of `Paper36.PolylogScaling.normalized_parameters`; source support: S4.Thmtheorem2. -/
theorem normalized_parameters : ∀ {s a h : ℝ} (hs : 1 ≤ s) (ha : 1 ≤ a) (hh : 1 ≤ h),
    Target.A0 s a h / s ≤ B s a h ∧ Target.nu s / s ≤ 3 ∧
    Target.G₀ (Target.A0 s a h) (Target.M0 h) / Real.sqrt s ≤
      Real.sqrt (B s a h * Target.M0 h) ∧
    Target.gamma₀ (Target.A0 s a h) (Target.nu s) (Target.M0 h) / Real.sqrt s ≤ G s a h := by
  sorry

end

section

open Paper36.PolylogScaling

/-- Complete declaration of `Paper36.PolylogScaling.residual_uniform`; source support: S4.Thmtheorem2. -/
theorem residual_uniform : ∀ {s a h w Δ : ℝ} (hs : 1 ≤ s) (ha : 1 ≤ a)
    (hh : 1 ≤ h) (hw : 0 ≤ w) (hΔ : 0 < Δ),
    BankTarget.paperResidual s a h w Δ ≤ 16*s^2*a*w^2/Δ * (F s a h w Δ)^2 := by
  sorry

end

section

open Paper36.PolylogScaling

/-- Complete declaration of `Paper36.PolylogScaling.target_uniform`; source support: S4.Thmtheorem2. -/
theorem target_uniform : ∀ {s a h w : ℝ} (hs : 1 ≤ s) (ha : 1 ≤ a)
    (hh : 1 ≤ h) (hw : 0 ≤ w) {K : ℕ} (hK : 1 ≤ K),
    BankTarget.paperTarget s a h w K ≤ 4*Real.sqrt 2*w*s*Real.sqrt a*Real.sqrt (K:ℝ)*
      Real.sqrt ((B s a h+3*Real.log (K:ℝ))*(Target.M0 h+Real.log (K:ℝ))) := by
  sorry

end

section

open Paper36.PolylogScaling

/-- Complete declaration of `Paper36.PolylogScaling.reward_model_uniform`; source support: S4.Thmtheorem2. -/
theorem reward_model_uniform : ∀ {s a h : ℝ} (hs : 1 ≤ s) (ha : 1 ≤ a)
    (hh : 1 ≤ h) {K : ℕ} (hK : 1 ≤ K),
    8*h*Real.sqrt h*Real.sqrt (s*a*(K:ℝ)*Bounds.rewardLog s a h K) ≤
      8*s*Real.sqrt a*h*Real.sqrt h*Real.sqrt (K:ℝ)*
        Real.sqrt (Real.log 2+Real.log (8*s*a*h*(K:ℝ)^2)) := by
  sorry

end

section

open Paper36.PolylogScaling

/-- Complete declaration of `Paper36.PolylogScaling.horizon_le_stageW`; source support: A2.Thmtheorem3. -/
theorem horizon_le_stageW : ∀ (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    {H : ℕ} (hH : 2 ≤ H),
    (H : ℝ) ≤ Real.sqrt (Weights.stageWsq β H) := by
  sorry

end

section

open Paper36.PolylogScaling

/-- Complete declaration of `Paper36.PolylogScaling.reward_performance_uniform`; source support: S4.Thmtheorem2. -/
theorem reward_performance_uniform : ∀ {s a h w Δ τ : ℝ} (hs : 1 ≤ s) (ha : 1 ≤ a)
    (hh : 1 ≤ h) (hw : h ≤ w) (hΔ : 0 < Δ) (hτ : τ ≤ Δ+h)
    {K : ℕ} (hK : 1 ≤ K),
    8*h*Real.sqrt h*Real.sqrt (s*a*(K:ℝ)*Bounds.rewardLog s a h K)+h/2+
      h*((BankTarget.paperTarget s a h w K+τ)/Δ) ≤
      s*Real.sqrt a*(h*Real.sqrt h+h*w/Δ)*Real.sqrt (K:ℝ)*rewardPolylog s a h K := by
  sorry

end

end P36Contract.PolylogScaling

namespace P36Contract.MainParameters

section
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested Paper36.Algorithm
  Paper36.StatisticalCounts Paper36.Statistical
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {Ω Info Model Hist : Type*} [MeasurableSpace Ω] [MeasurableSpace Info]
  [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model] [MeasurableSpace Hist]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℕ} {s₀ : S}
variable {E : EpisodeSystem μ Info S A (H+1) s₀}
  (P : PosteriorSystem (Model := Model) (Hist := Hist) E)

open Paper36.Main

/-- Complete declaration of `Paper36.Main.actual_gap_budget_bound`; source support: S2.Thmtheorem1, S4.Thmtheorem2. -/
theorem actual_gap_budget_bound : ∀ (α τ : ℝ) (hα : 0 ≤ α)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1),
    τ ≤ delta P α τ c + (H+1 : ℝ) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested Paper36.Algorithm
  Paper36.StatisticalCounts Paper36.Statistical
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {Ω Info Model Hist : Type*} [MeasurableSpace Ω] [MeasurableSpace Info]
  [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model] [MeasurableSpace Hist]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℕ} {s₀ : S}
variable {E : EpisodeSystem μ Info S A (H+1) s₀}
  (P : PosteriorSystem (Model := Model) (Hist := Hist) E)

open Paper36.Main

/-- Complete declaration of `Paper36.Main.reward_parameter_bound`; source support: S4.Thmtheorem2. -/
theorem reward_parameter_bound : ∀ (external : RowTapes.ExternalCategoricalConcentration (S := S))
    (α τ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hτ : 0 ≤ τ)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (hstrict : ∀ q ∈ support P, minimumRisk α c (H+1) 0 s₀ q < τ)
    (O : BorelAlgorithm.BorelOracles α c r (H+1) s₀ τ (support P))
    (hrun : ∀ n ω, policy P n ω = Algorithm.selected O.toOracles
      (target (S := S) (A := A) (H := H) α) (samples P) n ω)
    (hH : 1 ≤ H) {K : ℕ} (hK : 1 ≤ K),
    (∫ ω, Assembly.total (fun n ω => optimum P α τ c r ω - trueReward P r n ω) K ω ∂μ) ≤
      (Fintype.card S : ℝ) * Real.sqrt (Fintype.card A) *
        (((H+1 : ℕ) : ℝ) * Real.sqrt (H+1) + ((H+1 : ℕ) : ℝ) * Weights.W α (H+1) / delta P α τ c) *
          Real.sqrt (K:ℝ) * PolylogScaling.rewardPolylog (Fintype.card S) (Fintype.card A) (H+1) K := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested Paper36.Algorithm
  Paper36.StatisticalCounts Paper36.Statistical
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {Ω Info Model Hist : Type*} [MeasurableSpace Ω] [MeasurableSpace Info]
  [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model] [MeasurableSpace Hist]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℕ} {s₀ : S}
variable {E : EpisodeSystem μ Info S A (H+1) s₀}
  (P : PosteriorSystem (Model := Model) (Hist := Hist) E)

open Paper36.Main

/-- Complete declaration of `Paper36.Main.risk_parameter_bound`; source support: S4.Thmtheorem2. -/
theorem risk_parameter_bound : ∀ (external : RowTapes.ExternalCategoricalConcentration (S := S))
    (α τ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hτ : 0 ≤ τ)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (hstrict : ∀ q ∈ support P, minimumRisk α c (H+1) 0 s₀ q < τ)
    (O : BorelAlgorithm.BorelOracles α c r (H+1) s₀ τ (support P))
    (hrun : ∀ n ω, policy P n ω = Algorithm.selected O.toOracles
      (target (S := S) (A := A) (H := H) α) (samples P) n ω)
    {K : ℕ} (hK : 1 ≤ K),
    (∫ ω, Assembly.total (fun n ω => trueRisk P α c n ω - τ) K ω ∂μ) ≤
      SourceBank.lowConstant (S := S) (A := A) α (H+1) +
      16 * (Fintype.card S : ℝ)^2 * (Fintype.card A : ℝ) * (Weights.W α (H+1))^2 / delta P α τ c *
        (PolylogScaling.F (Fintype.card S) (Fintype.card A) (H+1) (Weights.W α (H+1)) (delta P α τ c))^2 := by
  sorry

end

end P36Contract.MainParameters

namespace P36Contract.StageRealized

section
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested Paper36.StageAlgorithm
  Paper36.StatisticalCounts Paper36.Statistical
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {Ω Info Model Hist : Type*} [MeasurableSpace Ω] [MeasurableSpace Info]
  [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model] [MeasurableSpace Hist]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℕ} {s₀ : S}
variable {E : EpisodeSystem μ Info S A (H+1) s₀}
  (P : PosteriorSystem (Model := Model) (Hist := Hist) E)

open Paper36.StageMain

/-- Complete declaration of `Paper36.StageMain.corollary_B_1_realized_calls`; source support: A2.Thmtheorem3, A2.Thmtheorem1. -/
theorem corollary_B_1_realized_calls : ∀ (external : RowTapes.ExternalCategoricalConcentration (S := S))
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
        sampledOptimum P β τ c r n ω - sampledReward P r n ω ≤ ζ n),
    ∀ K, 1 ≤ K →
    ((∫ ω, Assembly.total (fun n ω => trueRisk P β c n ω - τ) K ω ∂μ) ≤
      riskEnvelope (S := S) (A := A) (H := H) β (delta P β τ c) + ∑ n ∈ Finset.range K, ε n) ∧
    ((∫ ω, Assembly.total (fun n ω => optimum P β τ c r ω - trueReward P r n ω) K ω ∂μ) ≤
      rewardAllowance (S := S) (A := A) (H := H) K + (H+1 : ℝ) *
        ((target (S := S) (A := A) (H := H) β K + τ) / delta P β τ c) + ∑ n ∈ Finset.range K, ζ n) ∧
    ((∫ ω, Assembly.countRV (target (S := S) (A := A) (H := H) β) (deposit P β τ c) K ω ∂μ) ≤
      min (K : ℝ) ((target (S := S) (A := A) (H := H) β K + τ) / delta P β τ c)) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested Paper36.StageAlgorithm
  Paper36.StatisticalCounts Paper36.Statistical
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {Ω Info Model Hist : Type*} [MeasurableSpace Ω] [MeasurableSpace Info]
  [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model] [MeasurableSpace Hist]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {s₀ : S}
variable {E₁ : EpisodeSystem μ Info S A 1 s₀}
  (P₁ : PosteriorSystem (Model := Model) (Hist := Hist) E₁)

open Paper36.StageMain

/-- Complete declaration of `Paper36.StageMain.corollary_B_1_horizon_one_realized_calls`; source support: A2.Thmtheorem3, A2.Thmtheorem1. -/
theorem corollary_B_1_horizon_one_realized_calls : ∀ (β : ℕ → ℝ) (τ : ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (O : StageAlgorithm.BorelOracles β c r 1 s₀ τ (support P₁))
    (ε ζ : ℕ → ℝ)
    (hexploit : ∀ᵐ ω ∂μ, ∀ n,
      ¬Bank.calibrates (target (S := S) (A := A) (H := 0) β)
        (fun j => deposit P₁ β τ c j ω) n →
      sampledRisk P₁ β c n ω ≤ τ + ε n ∧
        sampledOptimum P₁ β τ c r n ω - sampledReward P₁ r n ω ≤ ζ n) (K : ℕ),
    ((∫ ω, Assembly.total (fun n ω => trueRisk P₁ β c n ω - τ) K ω ∂μ) ≤
      ∑ n ∈ Finset.range K, ε n) ∧
    ((∫ ω, Assembly.total (fun n ω => optimum P₁ β τ c r ω - trueReward P₁ r n ω) K ω ∂μ) ≤
      ∑ n ∈ Finset.range K, ζ n) := by
  sorry

end

end P36Contract.StageRealized

namespace P36Contract.StageParameters

section
open Set MeasureTheory Paper36.Regularity Paper36.Nested
variable {S A : Type*} [Fintype S] [Fintype A] [instNonemptyA : Nonempty A]

open Paper36.StageCalibration

/-- Complete declaration of `Paper36.StageCalibration.max_minimumRisk_bounds`; source support: A2.Thmtheorem3. -/
include instNonemptyA in
theorem max_minimumRisk_bounds : ∀ (ν : Measure (Nested.Kernel S A)) [IsProbabilityMeasure ν]
    (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1) (H : ℕ)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1) (s₀ : S),
    0 ≤ sSup (minimumRisk β c H 0 s₀ '' ν.support) ∧
      sSup (minimumRisk β c H 0 s₀ '' ν.support) ≤ H := by
  sorry

end

section
open Set MeasureTheory Paper36.Regularity Paper36.Nested
variable {S A : Type*} [Fintype S] [Fintype A] [instNonemptyA : Nonempty A]

open Paper36.StageCalibration

/-- Complete declaration of `Paper36.StageCalibration.induced_gap_budget_bound`; source support: A2.Thmtheorem3. -/
include instNonemptyA in
theorem induced_gap_budget_bound : ∀ (ν : Measure (Nested.Kernel S A)) [IsProbabilityMeasure ν]
    (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1) (τ : ℝ) (H : ℕ)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1) (s₀ : S),
    τ ≤ uniformGap ν β c H s₀ τ + H := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested Paper36.StageAlgorithm
  Paper36.StatisticalCounts Paper36.Statistical
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {Ω Info Model Hist : Type*} [MeasurableSpace Ω] [MeasurableSpace Info]
  [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model] [MeasurableSpace Hist]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℕ} {s₀ : S}
variable {E : EpisodeSystem μ Info S A (H+1) s₀}
  (P : PosteriorSystem (Model := Model) (Hist := Hist) E)

open Paper36.StageMain

/-- Complete declaration of `Paper36.StageMain.actual_gap_budget_bound`; source support: A2.Thmtheorem3. -/
theorem actual_gap_budget_bound : ∀ (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (τ : ℝ) (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1),
    τ ≤ delta P β τ c + (H+1 : ℝ) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested Paper36.StageAlgorithm
  Paper36.StatisticalCounts Paper36.Statistical
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {Ω Info Model Hist : Type*} [MeasurableSpace Ω] [MeasurableSpace Info]
  [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model] [MeasurableSpace Hist]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℕ} {s₀ : S}
variable {E : EpisodeSystem μ Info S A (H+1) s₀}
  (P : PosteriorSystem (Model := Model) (Hist := Hist) E)

open Paper36.StageMain

/-- Complete declaration of `Paper36.StageMain.reward_parameter_bound`; source support: A2.Thmtheorem3. -/
theorem reward_parameter_bound : ∀ (external : RowTapes.ExternalCategoricalConcentration (S := S))
    (β : ℕ → ℝ) (τ : ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1) (hτ : 0 ≤ τ)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (hstrict : ∀ q ∈ support P, ∃ π : Simulation.Policy S A,
      StageRisk.risk β c π (RiskBridge.ofKernel q) (H+1) 0 s₀ < τ)
    (O : StageAlgorithm.BorelOracles β c r (H+1) s₀ τ (support P))
    (hrun : ∀ n ω, policy P n ω = StageAlgorithm.selected O.toOracles
      (target (S := S) (A := A) (H := H) β) (samples P) n ω)
    (hH : 1 ≤ H) {K : ℕ} (hK : 1 ≤ K),
    (∫ ω, Assembly.total (fun n ω => optimum P β τ c r ω-trueReward P r n ω) K ω ∂μ) ≤
      (Fintype.card S : ℝ)*Real.sqrt (Fintype.card A)*
        (((H+1:ℕ):ℝ)*Real.sqrt (H+1)+((H+1:ℕ):ℝ)*Real.sqrt (Weights.stageWsq β (H+1))/delta P β τ c)*
          Real.sqrt (K:ℝ)*PolylogScaling.rewardPolylog (Fintype.card S) (Fintype.card A) (H+1) K := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested Paper36.StageAlgorithm
  Paper36.StatisticalCounts Paper36.Statistical
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {Ω Info Model Hist : Type*} [MeasurableSpace Ω] [MeasurableSpace Info]
  [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model] [MeasurableSpace Hist]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℕ} {s₀ : S}
variable {E : EpisodeSystem μ Info S A (H+1) s₀}
  (P : PosteriorSystem (Model := Model) (Hist := Hist) E)

open Paper36.StageMain

/-- Complete declaration of `Paper36.StageMain.risk_parameter_bound`; source support: A2.Thmtheorem3. -/
theorem risk_parameter_bound : ∀ (external : RowTapes.ExternalCategoricalConcentration (S := S))
    (β : ℕ → ℝ) (τ : ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1) (hτ : 0 ≤ τ)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (hstrict : ∀ q ∈ support P, ∃ π : Simulation.Policy S A,
      StageRisk.risk β c π (RiskBridge.ofKernel q) (H+1) 0 s₀ < τ)
    (O : StageAlgorithm.BorelOracles β c r (H+1) s₀ τ (support P))
    (hrun : ∀ n ω, policy P n ω = StageAlgorithm.selected O.toOracles
      (target (S := S) (A := A) (H := H) β) (samples P) n ω)
    {K : ℕ} (hK : 1 ≤ K),
    (∫ ω, Assembly.total (fun n ω => trueRisk P β c n ω-τ) K ω ∂μ) ≤
      lowConstant (S:=S) (A:=A) (H:=H) β+
        16*(Fintype.card S:ℝ)^2*(Fintype.card A:ℝ)*(Real.sqrt (Weights.stageWsq β (H+1)))^2/delta P β τ c*
          (PolylogScaling.F (Fintype.card S) (Fintype.card A) (H+1)
            (Real.sqrt (Weights.stageWsq β (H+1))) (delta P β τ c))^2 := by
  sorry

end

end P36Contract.StageParameters

namespace P36Contract.FreshChoice

section
open MeasureTheory ProbabilityTheory
variable {Ω Info Aux Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Info] [MeasurableSpace Aux] [MeasurableSpace Y]

open Paper36.AdaptiveKernel

/-- Complete declaration of `Paper36.AdaptiveKernel.freshChoice_joint`; source support: S5.Thmtheorem5. -/
theorem freshChoice_joint : ∀ (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Info) (hX : Measurable X) (Z : Ω → Y) (hZ : Measurable Z)
    (fresh : ProbabilityTheory.Kernel Info Y) [IsMarkovKernel fresh]
    (choose : ProbabilityTheory.Kernel Info Aux) [IsMarkovKernel choose]
    (hjoint : μ.map (fun ω => (X ω,Z ω)) = μ.map X ⊗ₘ fresh),
    (choiceExtension μ X hX choose).map (fun z => ((X z.1,z.2),Z z.1)) =
      (μ.map X ⊗ₘ choose) ⊗ₘ fresh.prodMkRight Aux := by
  sorry

end

section
open MeasureTheory ProbabilityTheory
variable {Ω Info Aux Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Info] [MeasurableSpace Aux] [MeasurableSpace Y]

open Paper36.AdaptiveKernel

/-- Complete declaration of `Paper36.AdaptiveKernel.freshChoice_information`; source support: S5.Thmtheorem5. -/
theorem freshChoice_information : ∀ (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Info) (hX : Measurable X) (choose : ProbabilityTheory.Kernel Info Aux) [IsMarkovKernel choose],
    (choiceExtension μ X hX choose).map (fun z => (X z.1,z.2)) = μ.map X ⊗ₘ choose := by
  sorry

end

section
open MeasureTheory ProbabilityTheory
variable {Ω Info Aux Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Info] [MeasurableSpace Aux] [MeasurableSpace Y]

open Paper36.AdaptiveKernel

/-- Complete declaration of `Paper36.AdaptiveKernel.freshChoice_condDistrib`; source support: S5.Thmtheorem5. -/
theorem freshChoice_condDistrib : ∀ [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Info) (hX : Measurable X) (Z : Ω → Y) (hZ : Measurable Z)
    (fresh : ProbabilityTheory.Kernel Info Y) [IsMarkovKernel fresh]
    (choose : ProbabilityTheory.Kernel Info Aux) [IsMarkovKernel choose]
    (hfresh : condDistrib Z X μ =ᵐ[μ.map X] fresh),
    condDistrib (fun z : Ω × Aux => Z z.1) (fun z => (X z.1,z.2)) (choiceExtension μ X hX choose)
      =ᵐ[μ.map X ⊗ₘ choose] fresh.prodMkRight Aux := by
  sorry

end

end P36Contract.FreshChoice

namespace P36Contract.InfiniteProcess

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories Paper36.AdaptiveTapes
open scoped ENNReal
variable {S Row Hist : Type*} [Fintype S] [Fintype Row] [DecidableEq Row]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace Row] [DiscreteMeasurableSpace Row] [MeasurableSpace Hist]

open Paper36.AdaptiveKernel

/-- Complete declaration of `Paper36.AdaptiveKernel.stateWindow_consume`; source support: S5.Thmtheorem5. -/
theorem stateWindow_consume : ∀ (update : Hist × (Row × S) → Hist)
    (L : ℕ) (x : InfiniteState Row S Hist) (rh : Row × Hist),
    stateWindow L (persistentConsume update (x,rh)) =
      consume update L (stateWindow (L+1) x, rh) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories Paper36.AdaptiveTapes
open scoped ENNReal
variable {S Row Hist : Type*} [Fintype S] [Fintype Row] [DecidableEq Row]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace Row] [DiscreteMeasurableSpace Row] [MeasurableSpace Hist]

open Paper36.AdaptiveKernel

/-- Complete declaration of `Paper36.AdaptiveKernel.persistentKernel_window`; source support: S5.Thmtheorem5. -/
theorem persistentKernel_window : ∀ (choose : ProbabilityTheory.Kernel Hist (Row × Hist)) [IsMarkovKernel choose]
    (update : Hist × (Row × S) → Hist) (hupdate : Measurable update)
    (n L : ℕ) (x : InfiniteState Row S Hist),
    (persistentKernel choose update n x).map (stateWindow L) =
      residualKernel choose update hupdate L n (stateWindow (L+n) x) := by
  sorry

end

end P36Contract.InfiniteProcess

namespace P36Contract.InfiniteProcessLaw

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories Paper36.AdaptiveTapes
open scoped ENNReal
variable {S Row Hist : Type*} [Fintype S] [Fintype Row] [DecidableEq Row]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace Row] [DiscreteMeasurableSpace Row] [MeasurableSpace Hist]

open Paper36.AdaptiveKernel

/-- Complete declaration of `Paper36.AdaptiveKernel.persistentLaw_window`; source support: S5.Thmtheorem5. -/
theorem persistentLaw_window : ∀ (P : Row → Law S) (choose : ProbabilityTheory.Kernel Hist (Row × Hist))
    [IsMarkovKernel choose] (update : Hist × (Row × S) → Hist) (hupdate : Measurable update)
    (n L : ℕ) (h : Hist),
    (persistentLaw P choose update hupdate n h).map (stateWindow L) =
      (onlineKernel P choose update n h).prod (lawMeasure (stackLaw P L)) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories Paper36.AdaptiveTapes
open scoped ENNReal
variable {S Row Hist : Type*} [Fintype S] [Fintype Row] [DecidableEq Row]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace Row] [DiscreteMeasurableSpace Row] [MeasurableSpace Hist]

open Paper36.AdaptiveKernel

/-- Complete declaration of `Paper36.AdaptiveKernel.persistentLaw_history`; source support: S5.Thmtheorem5. -/
theorem persistentLaw_history : ∀ (P : Row → Law S) (choose : ProbabilityTheory.Kernel Hist (Row × Hist))
    [IsMarkovKernel choose] (update : Hist × (Row × S) → Hist) (hupdate : Measurable update)
    (n : ℕ) (h : Hist),
    (persistentLaw P choose update hupdate n h).map (fun x => x.2.2) = onlineKernel P choose update n h := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories Paper36.AdaptiveTapes
open scoped ENNReal
variable {S Row Hist : Type*} [Fintype S] [Fintype Row] [DecidableEq Row]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace Row] [DiscreteMeasurableSpace Row] [MeasurableSpace Hist]

open Paper36.AdaptiveKernel

/-- Complete declaration of `Paper36.AdaptiveKernel.persistentLaw_unused_condDistrib`; source support: S5.Thmtheorem5. -/
theorem persistentLaw_unused_condDistrib : ∀ [Nonempty S]
    (P : Row → Law S) (choose : ProbabilityTheory.Kernel Hist (Row × Hist)) [IsMarkovKernel choose]
    (update : Hist × (Row × S) → Hist) (hupdate : Measurable update) (n L : ℕ) (h : Hist),
    condDistrib (fun x : InfiniteState Row S Hist => (stateWindow L x).2) (fun x => x.2.2)
      (persistentLaw P choose update hupdate n h) =ᵐ[onlineKernel P choose update n h]
        Kernel.const Hist (lawMeasure (stackLaw P L)) := by
  sorry

end

end P36Contract.InfiniteProcessLaw

namespace P36Contract.MixedProcess

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories Paper36.AdaptiveTapes
open scoped ENNReal
variable {S Row Hist : Type*} [Fintype S] [Fintype Row] [DecidableEq Row]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace Row] [DiscreteMeasurableSpace Row] [MeasurableSpace Hist]
variable {M : Type*} [MeasurableSpace M]

open Paper36.AdaptiveKernel

/-- Complete declaration of `Paper36.AdaptiveKernel.processKernel_window`; source support: S5.Thmtheorem5. -/
theorem processKernel_window : ∀ (P : M → Row → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (choose : ProbabilityTheory.Kernel Hist (Row × Hist)) [IsMarkovKernel choose]
    (update : Hist × (Row × S) → Hist) (hupdate : Measurable update) (n L : ℕ) (h : Hist),
    (processKernel P hP choose update n h).map (stateWindow L) =
      historyKernel P hP choose update n h ⊗ₖ (freshKernel P hP L).prodMkRight Hist := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories Paper36.AdaptiveTapes
open scoped ENNReal
variable {S Row Hist : Type*} [Fintype S] [Fintype Row] [DecidableEq Row]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace Row] [DiscreteMeasurableSpace Row] [MeasurableSpace Hist]
variable {M : Type*} [MeasurableSpace M]

open Paper36.AdaptiveKernel

/-- Complete declaration of `Paper36.AdaptiveKernel.mixedLaw_joint`; source support: S5.Thmtheorem5. -/
theorem mixedLaw_joint : ∀ (ν : Measure M) [IsProbabilityMeasure ν]
    (P : M → Row → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (choose : ProbabilityTheory.Kernel Hist (Row × Hist)) [IsMarkovKernel choose]
    (update : Hist × (Row × S) → Hist) (hupdate : Measurable update) (n L : ℕ) (h : Hist),
    (mixedLaw ν P hP choose update hupdate n h).map (fun z => ((z.1,z.2.2.2),(stateWindow L z.2).2)) =
      (ν ⊗ₘ historyKernel P hP choose update n h) ⊗ₘ (freshKernel P hP L).prodMkRight Hist := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories Paper36.AdaptiveTapes
open scoped ENNReal
variable {S Row Hist : Type*} [Fintype S] [Fintype Row] [DecidableEq Row]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace Row] [DiscreteMeasurableSpace Row] [MeasurableSpace Hist]
variable {M : Type*} [MeasurableSpace M]

open Paper36.AdaptiveKernel

/-- Complete declaration of `Paper36.AdaptiveKernel.mixedLaw_unused_condDistrib`; source support: S5.Thmtheorem5. -/
theorem mixedLaw_unused_condDistrib : ∀ [Nonempty S]
    (ν : Measure M) [IsProbabilityMeasure ν]
    (P : M → Row → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (choose : ProbabilityTheory.Kernel Hist (Row × Hist)) [IsMarkovKernel choose]
    (update : Hist × (Row × S) → Hist) (hupdate : Measurable update) (n L : ℕ) (h : Hist),
    condDistrib (fun z : M × InfiniteState Row S Hist => (stateWindow L z.2).2)
      (fun z => (z.1,z.2.2.2)) (mixedLaw ν P hP choose update hupdate n h) =ᵐ[ν ⊗ₘ historyKernel P hP choose update n h]
        (freshKernel P hP L).prodMkRight Hist := by
  sorry

end

end P36Contract.MixedProcess

namespace P36Contract.SourceBlocks

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation Paper36.Trajectories Paper36.AdaptiveTapes
universe u
variable {S A X Y : Type u} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]

open Paper36.SourceBlocks

/-- Complete declaration of `Paper36.SourceBlocks.blockLaw_expect_average`; source support: S5.Thmtheorem5. -/
theorem blockLaw_expect_average : ∀ (π : Policy S A) (p : Simulation.Kernel S A)
    (L n h : ℕ) (s : S) (f : Trajectory S A n × Stack (S × A) S L → ℝ),
    expect (stackLaw (fun r : S × A => p r.1 r.2) (L+n)).mass
      (fun tape => expect (blockLaw π L n h s tape).mass f) =
    expect (trajectoryLaw π p n h s).mass
      (fun path => expect (stackLaw (fun r : S × A => p r.1 r.2) L).mass
        (fun tape => f (path,tape))) := by
  sorry

end

end P36Contract.SourceBlocks

namespace P36Contract.SourceReplay

section
open MeasureTheory Paper36.CVaR Paper36.Trajectories Paper36.AdaptiveTapes
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
variable {Meta : Type*}

open Paper36.SourceReplay

/-- Complete declaration of `Paper36.SourceReplay.episodeReplay_eq_episodeHistory`; source support: S5.Thmtheorem5. -/
theorem episodeReplay_eq_episodeHistory : ∀ (raw : RawTape S A) (s₀ : S) {T : ℕ}
    (draws : ℕ → Draw Meta A T) (k : ℕ),
    episodeReplay raw s₀ draws k = episodeHistory T (episodePath raw s₀ draws) k := by
  sorry

end

section
open MeasureTheory Paper36.CVaR Paper36.Trajectories Paper36.AdaptiveTapes
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
variable {Meta : Type*}

open Paper36.SourceReplay

/-- Complete declaration of `Paper36.SourceReplay.replayHistory_count_prefix`; source support: S5.Thmtheorem5. -/
theorem replayHistory_count_prefix : ∀ (raw : RawTape S A) (s₀ : S) {T : ℕ}
    (draws : ℕ → Draw Meta A T) (k : ℕ) (row : S × A),
    historyCount (replayHistory raw s₀ draws k) row =
      Counts.before (fun j => visitCount row T (episodePath raw s₀ draws j)) k := by
  sorry

end

section
open MeasureTheory Paper36.CVaR Paper36.Trajectories Paper36.AdaptiveTapes
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
variable {Meta : Type*}

open Paper36.SourceReplay

/-- Complete declaration of `Paper36.SourceReplay.replayHistory_observed_prefix`; source support: S5.Thmtheorem5. -/
theorem replayHistory_observed_prefix : ∀ (raw : RawTape S A) (s₀ : S) {T : ℕ}
    (draws : ℕ → Draw Meta A T) (k : ℕ) (row : S × A)
    (hn : 0 < historyCount (replayHistory raw s₀ draws k) row),
    historyObserved s₀ (replayHistory raw s₀ draws k) row =
      RowTapes.empirical hn (fun i => raw row i.val) := by
  sorry

end

section
open MeasureTheory Paper36.CVaR Paper36.Trajectories Paper36.AdaptiveTapes
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
variable {Meta : Type*}

open Paper36.SourceReplay

/-- Complete declaration of `Paper36.SourceReplay.finiteHistory_observed_prefix`; source support: S5.Thmtheorem5. -/
theorem finiteHistory_observed_prefix : ∀ (raw : RawTape S A) (s₀ : S) {T k : ℕ}
    (draws : Fin k → Draw Meta A T) (row : S × A)
    (hn : 0 < historyCount (finiteHistory raw s₀ draws) row),
    historyObserved s₀ (finiteHistory raw s₀ draws) row =
      RowTapes.empirical hn (fun i => raw row i.val) := by
  sorry

end

section
open MeasureTheory Paper36.CVaR Paper36.Trajectories Paper36.AdaptiveTapes
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
variable {Meta : Type*} [MeasurableSpace A] [DiscreteMeasurableSpace A] [MeasurableSpace Meta]

open Paper36.SourceReplay

/-- Complete declaration of `Paper36.SourceReplay.measurable_finiteHistory`; source support: S5.Thmtheorem5. -/
theorem measurable_finiteHistory : ∀ (raw : Ω → RawTape S A) (s₀ : S) {T k : ℕ}
    (draws : Ω → Fin k → Draw Meta A T) (hraw : Measurable raw) (hd : Measurable draws),
    Measurable (fun ω => finiteHistory (raw ω) s₀ (draws ω)) := by
  sorry

end

section
open MeasureTheory Paper36.CVaR Paper36.Trajectories Paper36.AdaptiveTapes
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
variable {Meta : Type*} [MeasurableSpace A] [DiscreteMeasurableSpace A] [MeasurableSpace Meta]

open Paper36.SourceReplay

/-- Complete declaration of `Paper36.SourceReplay.measurable_replayHistory`; source support: S5.Thmtheorem5. -/
theorem measurable_replayHistory : ∀ (raw : Ω → RawTape S A) (s₀ : S) {T : ℕ}
    (draws : Ω → ℕ → Draw Meta A T) (hraw : Measurable raw) (hd : Measurable draws) (k : ℕ),
    Measurable (fun ω => replayHistory (raw ω) s₀ (draws ω) k) := by
  sorry

end

end P36Contract.SourceReplay

namespace P36Contract.SourceExperiment

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]
variable {Base D : Type*} [MeasurableSpace Base] [MeasurableSpace D]
variable {M Row S : Type*} [MeasurableSpace M] [Fintype S] [Nonempty S] [MeasurableSpace S] [DiscreteMeasurableSpace S]

open Paper36.SourceExperiment

/-- Complete declaration of `Paper36.SourceExperiment.experiment_initial`; source support: S5.Thmtheorem5. -/
theorem experiment_initial : ∀ (ν : Measure X) [IsProbabilityMeasure ν]
    (κ : ProbabilityTheory.Kernel X X) [IsMarkovKernel κ],
    (experiment ν κ).map Prod.fst = ν := by
  sorry

end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]
variable {Base D : Type*} [MeasurableSpace Base] [MeasurableSpace D]
variable {M Row S : Type*} [MeasurableSpace M] [Fintype S] [Nonempty S] [MeasurableSpace S] [DiscreteMeasurableSpace S]

open Paper36.SourceExperiment

/-- Complete declaration of `Paper36.SourceExperiment.experiment_retains`; source support: S5.Thmtheorem5. -/
theorem experiment_retains : ∀ (ν : Measure X) [IsProbabilityMeasure ν]
    (κ : ProbabilityTheory.Kernel X X) [IsMarkovKernel κ]
    {Y : Type*} [MeasurableSpace Y] (f : X → Y) (hf : Measurable f),
    (experiment ν κ).map (fun z => f z.1) = ν.map f := by
  sorry

end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]
variable {Base D : Type*} [MeasurableSpace Base] [MeasurableSpace D]
variable {M Row S : Type*} [MeasurableSpace M] [Fintype S] [Nonempty S] [MeasurableSpace S] [DiscreteMeasurableSpace S]

open Paper36.SourceExperiment

/-- Complete declaration of `Paper36.SourceExperiment.drawExecutionKernel_prefix`; source support: S5.Thmtheorem5. -/
theorem drawExecutionKernel_prefix : ∀ (κ : (n : ℕ) → ProbabilityTheory.Kernel (Base × (Fin n → D)) D)
    [∀ n, IsMarkovKernel (κ n)] (dummy : D) (n : ℕ),
    (drawExecutionKernel κ dummy).map (fun d : ℕ → D => fun i : Fin n => d i.val) =
      ((ProbabilityTheory.Kernel.partialTraj (X := fun _ => Base × D)
        (drawHistoryKernel κ) 0 n).comap
          (fun base => seed (base,dummy)) (measurable_seed.comp (measurable_id.prodMk measurable_const))).map
            (previous n) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]
variable {Base D : Type*} [MeasurableSpace Base] [MeasurableSpace D]
variable {M Row S : Type*} [MeasurableSpace M] [Fintype S] [Nonempty S] [MeasurableSpace S] [DiscreteMeasurableSpace S]

open Paper36.SourceExperiment

/-- Complete declaration of `Paper36.SourceExperiment.source_latent_law`; source support: S5.Thmtheorem5. -/
theorem source_latent_law : ∀ (ν : Measure M) [IsProbabilityMeasure ν]
    (P : M → Row → Paper36.CVaR.Law S)
    (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (κ : (n : ℕ) → ProbabilityTheory.Kernel ((M × (Row × ℕ → S)) × (Fin n → D)) D)
    [∀ n, IsMarkovKernel (κ n)] (dummy : D),
    (source ν P hP κ dummy).map (fun ω => ω.1.1) = ν := by
  sorry

end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]
variable {Base D : Type*} [MeasurableSpace Base] [MeasurableSpace D]
variable {M Row S : Type*} [MeasurableSpace M] [Fintype S] [Nonempty S] [MeasurableSpace S] [DiscreteMeasurableSpace S]

open Paper36.SourceExperiment

/-- Complete declaration of `Paper36.SourceExperiment.source_tape_model`; source support: S5.Thmtheorem5. -/
theorem source_tape_model : ∀ (ν : Measure M) [IsProbabilityMeasure ν]
    (P : M → Row → Paper36.CVaR.Law S)
    (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (κ : (n : ℕ) → ProbabilityTheory.Kernel ((M × (Row × ℕ → S)) × (Fin n → D)) D)
    [∀ n, IsMarkovKernel (κ n)] (dummy : D) (r : Row) (n : ℕ),
    condDistrib (fun ω : (M × (Row × ℕ → S)) × (ℕ → D) =>
      fun i : Fin n => ω.1.2 (r,i.val)) (fun ω => ω.1.1) (source ν P hP κ dummy)
      =ᵐ[ν] Paper36.RowTapes.iidKernel (fun m => P m r) (hP r) n := by
  sorry

end

end P36Contract.SourceExperiment

namespace P36Contract.SourceConditional

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation Paper36.Trajectories Paper36.AdaptiveTapes Paper36.SourceBlocks
open scoped ENNReal
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
variable {Ω Info Raw Out : Type*} [MeasurableSpace Ω] [MeasurableSpace Info]
  [MeasurableSpace Raw] [StandardBorelSpace Raw] [Nonempty Raw]
  [MeasurableSpace Out] [StandardBorelSpace Out] [Nonempty Out]

open Paper36.SourceConditional

/-- Complete declaration of `Paper36.SourceConditional.averaged_blockLaw_eq`; source support: S5.Thmtheorem5. -/
theorem averaged_blockLaw_eq : ∀ (π : Policy S A) (p : Simulation.Kernel S A)
    (L T h : ℕ) (s₀ : S),
    bindLaw (stackLaw (fun r : S × A => p r.1 r.2) (L+T)) (blockLaw π L T h s₀) =
      joint (trajectoryLaw π p T h s₀) (fun _ => stackLaw (fun r : S × A => p r.1 r.2) L) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation Paper36.Trajectories Paper36.AdaptiveTapes Paper36.SourceBlocks
open scoped ENNReal
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
variable {Ω Info Raw Out : Type*} [MeasurableSpace Ω] [MeasurableSpace Info]
  [MeasurableSpace Raw] [StandardBorelSpace Raw] [Nonempty Raw]
  [MeasurableSpace Out] [StandardBorelSpace Out] [Nonempty Out]

open Paper36.SourceConditional

/-- Complete declaration of `Paper36.SourceConditional.conditional_two_stage`; source support: S5.Thmtheorem5. -/
theorem conditional_two_stage : ∀ (μ : Measure Ω) [IsProbabilityMeasure μ]
    (info : Ω → Info) (hinfo : Measurable info) (raw : Ω → Raw) (hraw : Measurable raw)
    (out : Ω → Out) (hout : Measurable out)
    (fresh : ProbabilityTheory.Kernel Info Raw) [IsMarkovKernel fresh]
    (execute : ProbabilityTheory.Kernel (Info × Raw) Out) [IsMarkovKernel execute]
    (hfresh : condDistrib raw info μ =ᵐ[μ.map info] fresh)
    (hexecute : condDistrib out (fun ω => (info ω,raw ω)) μ =ᵐ[μ.map (fun ω => (info ω,raw ω))] execute),
    condDistrib out info μ =ᵐ[μ.map info] (fresh ⊗ₖ execute).map Prod.snd := by
  sorry

end

end P36Contract.SourceConditional

namespace P36Contract.SourceProtocol

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation Paper36.Trajectories Paper36.AdaptiveTapes Paper36.SourceReplay
open scoped ENNReal
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  [MeasurableSpace S] [DiscreteMeasurableSpace S] [MeasurableSpace A] [DiscreteMeasurableSpace A]
  {Meta M : Type*} [MeasurableSpace Meta] [MeasurableSpace M] {T : ℕ}

open Paper36.SourceProtocol

/-- Complete declaration of `Paper36.SourceProtocol.actual_count_prefix`; source support: S5.Thmtheorem5. -/
theorem actual_count_prefix : ∀ (s₀ : S) (T k : ℕ) (ω : Sample M Meta S A T) (row : S × A),
    historyCount (history s₀ T k ω) row =
      Counts.before (fun j => visitCount row T (path s₀ T j ω)) k := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation Paper36.Trajectories Paper36.AdaptiveTapes Paper36.SourceReplay
open scoped ENNReal
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  [MeasurableSpace S] [DiscreteMeasurableSpace S] [MeasurableSpace A] [DiscreteMeasurableSpace A]
  {Meta M : Type*} [MeasurableSpace Meta] [MeasurableSpace M] {T : ℕ}

open Paper36.SourceProtocol

/-- Complete declaration of `Paper36.SourceProtocol.actual_observed_prefix`; source support: S5.Thmtheorem5. -/
theorem actual_observed_prefix : ∀ (s₀ : S) (T k : ℕ) (ω : Sample M Meta S A T) (row : S × A)
    (hn : 0 < historyCount (history s₀ T k ω) row),
    historyObserved s₀ (history s₀ T k ω) row =
      RowTapes.empirical hn (fun i => ω.1.2 (row,i.val)) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation Paper36.Trajectories Paper36.AdaptiveTapes Paper36.SourceReplay
open scoped ENNReal
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  [MeasurableSpace S] [DiscreteMeasurableSpace S] [MeasurableSpace A] [DiscreteMeasurableSpace A]
  {Meta M : Type*} [MeasurableSpace Meta] [MeasurableSpace M] {T : ℕ}

open Paper36.SourceProtocol

/-- Complete declaration of `Paper36.SourceProtocol.actual_tape_model`; source support: S5.Thmtheorem5. -/
theorem actual_tape_model : ∀ [Nonempty S] (ν : Measure M) [IsProbabilityMeasure ν]
    (P : M → S × A → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (π : Meta → Policy S A) (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (planner : ProbabilityTheory.Kernel (History Meta S A T) Meta) [IsMarkovKernel planner]
    (s₀ : S) (dummy : Draw Meta A T) (row : S × A) (n : ℕ),
    condDistrib (fun ω : Sample M Meta S A T => fun i : Fin n => ω.1.2 (row,i.val))
      (fun ω => ω.1.1) (measure ν P hP π hπ planner s₀ dummy) =ᵐ[ν]
      RowTapes.iidKernel (fun m => P m row) (hP row) n := by
  sorry

end

end P36Contract.SourceProtocol

namespace P36Contract.SourceMarginals

section
open MeasureTheory ProbabilityTheory Paper36.SourceExperiment
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]

open Paper36.SourceMarginals

/-- Complete declaration of `Paper36.SourceMarginals.partial_last`; source support: S5.Thmtheorem5. -/
theorem partial_last : ∀ (κ : Kernel X X) [IsMarkovKernel κ] (n : ℕ),
    (Kernel.partialTraj (X := fun _ => X) (historyKernel κ) 0 n).map (last n) =
      (iterateKernel κ n).comap (last 0) (measurable_last 0) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.SourceExperiment
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]

open Paper36.SourceMarginals

/-- Complete declaration of `Paper36.SourceMarginals.executionKernel_nth`; source support: S5.Thmtheorem5. -/
theorem executionKernel_nth : ∀ (κ : Kernel X X) [IsMarkovKernel κ] (n : ℕ),
    (executionKernel κ).map (fun x : ℕ → X => x n) = iterateKernel κ n := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.SourceExperiment
open scoped ENNReal
variable {Base D : Type*} [MeasurableSpace Base] [MeasurableSpace D]

open Paper36.SourceMarginals

/-- Complete declaration of `Paper36.SourceMarginals.prefixKernel_eq_actual`; source support: S5.Thmtheorem5. -/
theorem prefixKernel_eq_actual : ∀ [MeasurableSingletonClass Base]
    (κ : (n : ℕ) → Kernel (Base × (Fin n → D)) D) [∀ n, IsMarkovKernel (κ n)]
    (dummy : D) (n : ℕ),
    prefixKernel κ dummy n = Kernel.id ×ₖ
      (drawExecutionKernel κ dummy).map (fun d : ℕ → D => fun i : Fin n => d i.val) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.SourceExperiment
open scoped ENNReal
variable {Base D : Type*} [MeasurableSpace Base] [MeasurableSpace D]

open Paper36.SourceMarginals

/-- Complete declaration of `Paper36.SourceMarginals.actual_prefix_succ`; source support: S5.Thmtheorem5. -/
theorem actual_prefix_succ : ∀ [MeasurableSingletonClass Base]
    (ν : Measure Base) [IsProbabilityMeasure ν]
    (κ : (n : ℕ) → Kernel (Base × (Fin n → D)) D) [∀ n, IsMarkovKernel (κ n)]
    (dummy : D) (n : ℕ),
    (ν ⊗ₘ drawExecutionKernel κ dummy).map
      (fun z => (z.1, fun i : Fin (n+1) => z.2 i.val)) =
      stepDraw κ n ∘ₘ ((ν ⊗ₘ drawExecutionKernel κ dummy).map
        (fun z => (z.1, fun i : Fin n => z.2 i.val))) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.SourceExperiment
open scoped ENNReal
variable {Base D : Type*} [MeasurableSpace Base] [MeasurableSpace D]

open Paper36.SourceMarginals

/-- Complete declaration of `Paper36.SourceMarginals.actual_next_pair`; source support: S5.Thmtheorem5. -/
theorem actual_next_pair : ∀ [MeasurableSingletonClass Base]
    (ν : Measure Base) [IsProbabilityMeasure ν]
    (κ : (n : ℕ) → Kernel (Base × (Fin n → D)) D) [∀ n, IsMarkovKernel (κ n)]
    (dummy : D) (n : ℕ),
    (ν ⊗ₘ drawExecutionKernel κ dummy).map
      (fun z => ((z.1, fun i : Fin n => z.2 i.val), z.2 n)) =
      ((ν ⊗ₘ drawExecutionKernel κ dummy).map
        (fun z => (z.1, fun i : Fin n => z.2 i.val))) ⊗ₘ κ n := by
  sorry

end

end P36Contract.SourceMarginals

namespace P36Contract.FiniteData

section
open Paper36.Regularity Paper36.Nested
variable {S A : Type*} [Fintype S] [Fintype A]

open Paper36.FiniteData

/-- Complete declaration of `Paper36.FiniteData.finite_data_representation`; source support: S2.Thmtheorem1, S4.Thmtheorem2. -/
theorem finite_data_representation : ∀ {H : ℕ} (c r : Fin H → S → A → ℝ)
    (c' r' : ℕ → S → A → ℝ)
    (hc : ∀ h : Fin H, c' h.val = c h) (hr : ∀ h : Fin H, r' h.val = r h)
    (α : ℝ) (π : Policy S A) (q : Kernel S A) (s : S),
    risk α c' π q H 0 s = risk α (extend c) π q H 0 s ∧
      reward r' π q H 0 s = reward (extend r) π q H 0 s := by
  sorry

end

section
open Paper36.Regularity Paper36.Nested
variable {S A : Type*} [Fintype S] [Fintype A]

open Paper36.FiniteData

/-- Complete declaration of `Paper36.FiniteData.planning_data_congr`; source support: S6.Thmtheorem1, S6.Thmtheorem2. -/
theorem planning_data_congr : ∀ (α τ : ℝ) (c d r t : ℕ → S → A → ℝ)
    (H : ℕ) (s : S) (q : Kernel S A)
    (hcd : ∀ j, 0 ≤ j → j < 0+H → c j = d j)
    (hrt : ∀ j, 0 ≤ j → j < 0+H → r j = t j),
    minimumRisk α c H 0 s q = minimumRisk α d H 0 s q ∧
      Algorithm.constrainedValue α c r H s τ q = Algorithm.constrainedValue α d t H s τ q := by
  sorry

end

section
open Paper36.Regularity Paper36.Nested
variable {S A : Type*} [Fintype S] [Fintype A]

open Paper36.FiniteData

/-- Complete declaration of `Paper36.FiniteData.extend_valid`; source support: S4.Thmtheorem2. -/
theorem extend_valid : ∀ {H : ℕ} (f : Fin H → S → A → ℝ)
    (hf : ∀ h s a, f h s a ∈ Set.Icc 0 1),
    ∀ h s a, extend f h s a ∈ Set.Icc 0 1 := by
  sorry

end

section
open Paper36.Regularity Paper36.Nested
variable {S A : Type*} [Fintype S] [Fintype A]

open Paper36.FiniteData

/-- Complete declaration of `Paper36.FiniteData.stageRisk_data_congr`; source support: A2.Thmtheorem3. -/
theorem stageRisk_data_congr : ∀ (β : ℕ → ℝ) (c d : ℕ → S → A → ℝ)
    (π : Simulation.Policy S A) (q : Simulation.Kernel S A) (n h : ℕ) (s : S)
    (hcd : ∀ j, h ≤ j → j < h+n → c j = d j),
    StageRisk.risk β c π q n h s = StageRisk.risk β d π q n h s := by
  sorry

end

end P36Contract.FiniteData

namespace P36Contract.SourceHistory

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories Paper36.AdaptiveTapes Paper36.SourceReplay
open scoped ENNReal
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  [MeasurableSpace S] [DiscreteMeasurableSpace S] [MeasurableSpace A] [DiscreteMeasurableSpace A]
  {Meta : Type*} [MeasurableSpace Meta]

open Paper36.SourceHistory

/-- Complete declaration of `Paper36.SourceHistory.finiteHistory_append`; source support: S5.Thmtheorem5. -/
theorem finiteHistory_append : ∀ (raw : RawTape S A) (s₀ : S) (T k : ℕ)
    (d : Fin k → Draw Meta A T) (z : Draw Meta A T),
    finiteHistory raw s₀ (Fin.lastCases z d) =
      (⟨k+1, append T k (finiteHistory raw s₀ d).2
        (z.1,replayStep raw (historyCount (finiteHistory raw s₀ d)) T s₀ z.2)⟩ : History Meta S A T) := by
  sorry

end

end P36Contract.SourceHistory

namespace P36Contract.StageExactCalls

section
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested Paper36.StageAlgorithm
  Paper36.StatisticalCounts Paper36.Statistical
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {Ω Info Model Hist : Type*} [MeasurableSpace Ω] [MeasurableSpace Info]
  [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model] [MeasurableSpace Hist]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {s₀ : S}
variable {E : EpisodeSystem μ Info S A 1 s₀}
  (P : PosteriorSystem (Model := Model) (Hist := Hist) E)

open Paper36.StageMain

/-- Complete declaration of `Paper36.StageMain.theorem_4_2_horizon_one_realized_calls`; source support: A2.Thmtheorem3, S4.Thmtheorem2. -/
theorem theorem_4_2_horizon_one_realized_calls : ∀ (β : ℕ → ℝ) (τ : ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (O : StageAlgorithm.BorelOracles β c r 1 s₀ τ (support P))
    (hexploit : ∀ᵐ ω ∂μ, ∀ n,
      ¬Bank.calibrates (target (S := S) (A := A) (H := 0) β)
        (fun j => deposit P β τ c j ω) n →
      sampledRisk P β c n ω ≤ τ + 0 ∧
        sampledOptimum P β τ c r n ω - sampledReward P r n ω ≤ 0) (K : ℕ),
    ((∫ ω, Assembly.total (fun n ω => trueRisk P β c n ω - τ) K ω ∂μ) ≤ 0) ∧
    ((∫ ω, Assembly.total (fun n ω => optimum P β τ c r ω - trueReward P r n ω) K ω ∂μ) = 0) ∧
    (∀ ω, Bank.bank (target (S := S) (A := A) (H := 0) β) (fun j => deposit P β τ c j ω) K = 0 ∧
      Bank.count (target (S := S) (A := A) (H := 0) β) (fun j => deposit P β τ c j ω) K = 0) := by
  sorry

end

end P36Contract.StageExactCalls

namespace P36Contract.SourceBlockKernel

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation Paper36.Trajectories Paper36.AdaptiveTapes Paper36.SourceBlocks
open scoped ENNReal
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  [MeasurableSpace S] [DiscreteMeasurableSpace S] {Info : Type*} [MeasurableSpace Info]

open Paper36.SourceBlockKernel

/-- Complete declaration of `Paper36.SourceBlockKernel.averaged_blockKernel`; source support: S5.Thmtheorem5. -/
theorem averaged_blockKernel : ∀ (π : Info → Policy S A) (p : Info → Simulation.Kernel S A)
    (hπ : ∀ h s a, Measurable (fun i => (π i h s).mass a))
    (hp : ∀ s a t, Measurable (fun i => (p i s a).mass t)) (L T : ℕ) (s₀ : S),
    (AdaptiveKernel.freshKernel (fun i => fun r : S × A => p i r.1 r.2)
      (fun r t => hp r.1 r.2 t) (L+T) ⊗ₖ blockKernel π hπ L T s₀).map Prod.snd =
      trajectoryKernel π p hπ hp T s₀ ×ₖ
        AdaptiveKernel.freshKernel (fun i => fun r : S × A => p i r.1 r.2)
          (fun r t => hp r.1 r.2 t) L := by
  sorry

end

end P36Contract.SourceBlockKernel

namespace P36Contract.SourceBlockReplay

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation Paper36.Trajectories Paper36.AdaptiveTapes Paper36.SourceBlocks Paper36.SourceReplay
open scoped ENNReal
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  [MeasurableSpace S] [DiscreteMeasurableSpace S] [MeasurableSpace A] [DiscreteMeasurableSpace A]

open Paper36.SourceBlockReplay

/-- Complete declaration of `Paper36.SourceBlockReplay.blockLaw_expect_replay`; source support: S5.Thmtheorem5. -/
theorem blockLaw_expect_replay : ∀ (π : Policy S A) (raw : RawTape S A) (counts : S × A → ℕ)
    (L T h : ℕ) (s₀ : S) (f : Trajectory S A T × Stack (S × A) S L → ℝ),
    expect (blockLaw π L T h s₀ (window raw counts (L+T))).mass f =
      expect (tapedTrajectory π T h s₀ (window raw counts T)).mass
        (fun path => f (path,window raw (afterPath counts T path) L)) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation Paper36.Trajectories Paper36.AdaptiveTapes Paper36.SourceBlocks Paper36.SourceReplay
open scoped ENNReal
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  [MeasurableSpace S] [DiscreteMeasurableSpace S] [MeasurableSpace A] [DiscreteMeasurableSpace A]

open Paper36.SourceBlockReplay

/-- Complete declaration of `Paper36.SourceBlockReplay.replay_actionLaw_eq_blockLaw`; source support: S5.Thmtheorem5. -/
theorem replay_actionLaw_eq_blockLaw : ∀ (π : Policy S A) (raw : RawTape S A)
    (counts : S × A → ℕ) (L T : ℕ) (s₀ : S),
    pushLaw (SourceProtocol.actionLaw π T s₀ (window raw counts T))
      (fun actions => let path := replayStep raw counts T s₀ actions
        (path,window raw (afterPath counts T path) L)) =
      blockLaw π L T 0 s₀ (window raw counts (L+T)) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation Paper36.Trajectories Paper36.AdaptiveTapes Paper36.SourceBlocks Paper36.SourceReplay
open scoped ENNReal
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  [MeasurableSpace S] [DiscreteMeasurableSpace S] [MeasurableSpace A] [DiscreteMeasurableSpace A]

open Paper36.SourceBlockReplay

/-- Complete declaration of `Paper36.SourceBlockReplay.actionLaw_joint_replay`; source support: S5.Thmtheorem5. -/
theorem actionLaw_joint_replay : ∀ (π : Policy S A) (raw : RawTape S A)
    (counts : S × A → ℕ) (L T : ℕ) (s₀ : S),
    (lawMeasure (SourceProtocol.actionLaw π T s₀ (window raw counts T))).map
      (fun actions => let path := replayStep raw counts T s₀ actions
        (path,window raw (afterPath counts T path) L)) =
      lawMeasure (blockLaw π L T 0 s₀ (window raw counts (L+T))) := by
  sorry

end

end P36Contract.SourceBlockReplay

namespace P36Contract.SourceInduction

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {X Y H R O : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace H] [MeasurableSpace R] [MeasurableSpace O]
variable {State Obs : ℕ → Type*} {Raw : ℕ → Type*}
  [∀ k, MeasurableSpace (State k)] [∀ k, MeasurableSpace (Obs k)] [∀ L, MeasurableSpace (Raw L)]

open Paper36.SourceInduction

/-- Complete declaration of `Paper36.SourceInduction.transport_step`; source support: S5.Thmtheorem5. -/
theorem transport_step : ∀ (μ : Measure X) [SFinite μ]
    (step : Kernel X Y) [IsMarkovKernel step] (summary : X → H) (hs : Measurable summary)
    (output : Y → O) (ho : Measurable output) (block : Kernel H O) [IsMarkovKernel block]
    (hstep : ∀ x, (step x).map output = block (summary x)),
    (step ∘ₘ μ).map output = block ∘ₘ μ.map summary := by
  sorry

end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {X Y H R O : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace H] [MeasurableSpace R] [MeasurableSpace O]
variable {State Obs : ℕ → Type*} {Raw : ℕ → Type*}
  [∀ k, MeasurableSpace (State k)] [∀ k, MeasurableSpace (Obs k)] [∀ L, MeasurableSpace (Raw L)]

open Paper36.SourceInduction

/-- Complete declaration of `Paper36.SourceInduction.mix_transition_fresh`; source support: S5.Thmtheorem5. -/
theorem mix_transition_fresh : ∀ {N : Type*} [MeasurableSpace N]
    (ν : Measure H) [SFinite ν] (next : Kernel H N) [IsMarkovKernel next]
    (fresh : Kernel N R) [IsMarkovKernel fresh],
    (next ⊗ₖ fresh.prodMkLeft H) ∘ₘ ν = (next ∘ₘ ν) ⊗ₘ fresh := by
  sorry

end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {X Y H R O : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace H] [MeasurableSpace R] [MeasurableSpace O]
variable {State Obs : ℕ → Type*} {Raw : ℕ → Type*}
  [∀ k, MeasurableSpace (State k)] [∀ k, MeasurableSpace (Obs k)] [∀ L, MeasurableSpace (Raw L)]

open Paper36.SourceInduction

/-- Complete declaration of `Paper36.SourceInduction.propagate_fresh`; source support: S5.Thmtheorem5. -/
theorem propagate_fresh : ∀ (T : ℕ)
    (actual : (k : ℕ) → Measure (State k)) [∀ k, IsProbabilityMeasure (actual k)]
    (hist : (k : ℕ) → Measure (Obs k)) [∀ k, IsProbabilityMeasure (hist k)]
    (step : (k : ℕ) → Kernel (State k) (State (k+1))) [∀ k, IsMarkovKernel (step k)]
    (next : (k : ℕ) → Kernel (Obs k) (Obs (k+1))) [∀ k, IsMarkovKernel (next k)]
    (fresh : (k L : ℕ) → Kernel (Obs k) (Raw L)) [∀ k L, IsMarkovKernel (fresh k L)]
    (summary : (k L : ℕ) → State k → Obs k × Raw L)
    (hs : ∀ k L, Measurable (summary k L))
    (block : (k L : ℕ) → Kernel (Obs k × Raw (L+T)) (Obs (k+1) × Raw L))
    [∀ k L, IsMarkovKernel (block k L)]
    (hactual : ∀ k, actual (k+1) = step k ∘ₘ actual k)
    (hhist : ∀ k, hist (k+1) = next k ∘ₘ hist k)
    (hzero : ∀ L, (actual 0).map (summary 0 L) = hist 0 ⊗ₘ fresh 0 L)
    (hstep : ∀ k L x, (step k x).map (summary (k+1) L) = block k L (summary k (L+T) x))
    (hblock : ∀ k L, (fresh k (L+T) ⊗ₖ block k L).map Prod.snd =
      next k ⊗ₖ (fresh (k+1) L).prodMkLeft (Obs k)),
    ∀ k L, (actual k).map (summary k L) = hist k ⊗ₘ fresh k L := by
  sorry

end

end P36Contract.SourceInduction

namespace P36Contract.SourcePlanBlock

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation Paper36.Trajectories Paper36.AdaptiveTapes
open scoped ENNReal
variable {H Meta R O : Type*} [MeasurableSpace H] [MeasurableSpace Meta] [MeasurableSpace R] [MeasurableSpace O]

open Paper36.SourcePlanBlock

/-- Complete declaration of `Paper36.SourcePlanBlock.averaged_plannedKernel`; source support: S5.Thmtheorem5. -/
theorem averaged_plannedKernel : ∀ (fresh : ProbabilityTheory.Kernel H R) [IsMarkovKernel fresh]
    (planner : ProbabilityTheory.Kernel H Meta) [IsMarkovKernel planner]
    (block : ProbabilityTheory.Kernel ((H × Meta) × R) O) [IsMarkovKernel block]
    (average : ProbabilityTheory.Kernel (H × Meta) O) [IsMarkovKernel average]
    (haverage : (fresh.comap Prod.fst measurable_fst ⊗ₖ block).map Prod.snd = average),
    (fresh ⊗ₖ plannedKernel planner block).map Prod.snd = planner ⊗ₖ average := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation
  Paper36.Trajectories Paper36.AdaptiveTapes Paper36.SourceReplay
open scoped ENNReal
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  {M Meta : Type*} [MeasurableSpace M] [MeasurableSpace Meta] {T : ℕ}

open Paper36.SourcePlanBlock

/-- Complete declaration of `Paper36.SourcePlanBlock.local_factorization`; source support: S5.Thmtheorem5. -/
theorem local_factorization : ∀ (π : Meta → Policy S A) (P : M → S × A → Law S)
    (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (planner : ProbabilityTheory.Kernel (SourceReplay.History Meta S A T) Meta) [IsMarkovKernel planner]
    (s₀ : S) (k L : ℕ),
    (freshCtx P hP T k (L+T) ⊗ₖ localBlock π hπ planner s₀ k L).map Prod.snd =
      onlineNext π P hπ hP planner s₀ k ⊗ₖ
        (freshCtx P hP T (k+1) L).prodMkLeft (Ctx M Meta S A T k) := by
  sorry

end

end P36Contract.SourcePlanBlock

namespace P36Contract.SourceSummary

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation Paper36.Trajectories Paper36.AdaptiveTapes Paper36.SourceReplay Paper36.SourceProtocol Paper36.SourceHistory
open scoped ENNReal
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  [MeasurableSpace S] [DiscreteMeasurableSpace S] [MeasurableSpace A] [DiscreteMeasurableSpace A]
  {M Meta : Type*} [MeasurableSpace M] [MeasurableSpace Meta]

open Paper36.SourceSummary

/-- Complete declaration of `Paper36.SourceSummary.summary_append`; source support: S5.Thmtheorem5. -/
theorem summary_append : ∀ (T k L : ℕ) (s₀ : S) (x : Input M Meta S A T k) (d : Draw Meta A T),
    summary T (k+1) L s₀ (SourceMarginals.appendDraw k (x,d)) =
      let p := replayStep (fun row j => x.1.2 (row,j)) (historyCount (past T k s₀ x)) T s₀ d.2
      ((x.1.1,append T k (context T k s₀ x).2 (d.1,p)),
        window (fun row j => x.1.2 (row,j))
          (SourceBlockReplay.afterPath (historyCount (past T k s₀ x)) T p) L) := by
  sorry

end

end P36Contract.SourceSummary

namespace P36Contract.SourceStepReplay

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation
  Paper36.Trajectories Paper36.AdaptiveTapes Paper36.SourceReplay
open scoped ENNReal
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  {M Meta : Type*} [MeasurableSpace M] [MeasurableSpace Meta] {T : ℕ}
open Paper36.SourceProtocol Paper36.SourceSummary

open Paper36.SourceStepReplay

/-- Complete declaration of `Paper36.SourceStepReplay.step_summary`; source support: S5.Thmtheorem5. -/
theorem step_summary : ∀ (π : Meta → Policy S A) (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (planner : ProbabilityTheory.Kernel (History Meta S A T) Meta) [IsMarkovKernel planner]
    (s₀ : S) (k L : ℕ) (x : Input M Meta S A T k),
    (SourceMarginals.stepDraw (protocolKernel π hπ planner s₀) k x).map (summary T (k+1) L s₀) =
      SourcePlanBlock.localBlock π hπ planner s₀ k L (summary T k (L+T) s₀ x) := by
  sorry

end

end P36Contract.SourceStepReplay

namespace P36Contract.SourceFresh

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation
  Paper36.Trajectories Paper36.AdaptiveTapes Paper36.SourceReplay
open scoped ENNReal
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  {M Meta : Type*} [MeasurableSpace M] [MeasurableSpace Meta] {T : ℕ}
open Paper36.SourceProtocol Paper36.SourceSummary

open Paper36.SourceFresh

/-- Complete declaration of `Paper36.SourceFresh.initial_tape_joint`; source support: S5.Thmtheorem5. -/
theorem initial_tape_joint : ∀ (ν : Measure M) [IsProbabilityMeasure ν]
    (P : M → S × A → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (T L : ℕ),
    (InfiniteTapes.priorTapes ν P hP).map
      (fun x => (initial (Meta := Meta) T x.1,AdaptiveKernel.fullPrefix L x.2)) =
      ν.map (initial T) ⊗ₘ SourcePlanBlock.freshCtx P hP T 0 L := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation
  Paper36.Trajectories Paper36.AdaptiveTapes Paper36.SourceReplay
open scoped ENNReal
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  {M Meta : Type*} [MeasurableSpace M] [MeasurableSpace Meta] {T : ℕ}
open Paper36.SourceProtocol Paper36.SourceSummary
variable [Nonempty S] [MeasurableSingletonClass M]

open Paper36.SourceFresh

/-- Complete declaration of `Paper36.SourceFresh.actual_prefix_fresh`; source support: S5.Thmtheorem5. -/
theorem actual_prefix_fresh : ∀ (ν : Measure M) [IsProbabilityMeasure ν]
    (P : M → S × A → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (π : Meta → Policy S A) (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (planner : ProbabilityTheory.Kernel (History Meta S A T) Meta) [IsMarkovKernel planner]
    (s₀ : S) (dummy : Draw Meta A T) (k L : ℕ),
    (actualPrefix ν P hP π hπ planner s₀ dummy k).map (summary T k L s₀) =
      onlineHistory ν P hP π hπ planner s₀ k ⊗ₘ SourcePlanBlock.freshCtx P hP T k L := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation
  Paper36.Trajectories Paper36.AdaptiveTapes Paper36.SourceReplay
open scoped ENNReal
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  {M Meta : Type*} [MeasurableSpace M] [MeasurableSpace Meta] {T : ℕ}
open Paper36.SourceProtocol Paper36.SourceSummary
variable [Nonempty S] [MeasurableSingletonClass M]

open Paper36.SourceFresh

/-- Complete declaration of `Paper36.SourceFresh.actual_context_succ`; source support: S5.Thmtheorem5. -/
theorem actual_context_succ : ∀ (ν : Measure M) [IsProbabilityMeasure ν]
    (P : M → S × A → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (π : Meta → Policy S A) (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (planner : ProbabilityTheory.Kernel (History Meta S A T) Meta) [IsMarkovKernel planner]
    (s₀ : S) (dummy : Draw Meta A T) (k : ℕ),
    (SourceProtocol.measure ν P hP π hπ planner s₀ dummy).map (actualContext T (k+1) s₀) =
      SourcePlanBlock.onlineNext π P hπ hP planner s₀ k ∘ₘ
        (SourceProtocol.measure ν P hP π hπ planner s₀ dummy).map (actualContext T k s₀) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation
  Paper36.Trajectories Paper36.AdaptiveTapes Paper36.SourceReplay
open scoped ENNReal
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  {M Meta : Type*} [MeasurableSpace M] [MeasurableSpace Meta] {T : ℕ}
open Paper36.SourceProtocol Paper36.SourceSummary
variable [Nonempty S] [MeasurableSingletonClass M]

open Paper36.SourceFresh

/-- Complete declaration of `Paper36.SourceFresh.actual_fresh`; source support: S5.Thmtheorem5. -/
theorem actual_fresh : ∀ (ν : Measure M) [IsProbabilityMeasure ν]
    (P : M → S × A → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (π : Meta → Policy S A) (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (planner : ProbabilityTheory.Kernel (History Meta S A T) Meta) [IsMarkovKernel planner]
    (s₀ : S) (dummy : Draw Meta A T) (k L : ℕ),
    (SourceProtocol.measure ν P hP π hπ planner s₀ dummy).map
      (fun ω => (actualContext T k s₀ ω,actualWindow T k L s₀ ω)) =
      (SourceProtocol.measure ν P hP π hπ planner s₀ dummy).map (actualContext T k s₀) ⊗ₘ
        SourcePlanBlock.freshCtx P hP T k L := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation
  Paper36.Trajectories Paper36.AdaptiveTapes Paper36.SourceReplay
open scoped ENNReal
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  {M Meta : Type*} [MeasurableSpace M] [MeasurableSpace Meta] {T : ℕ}
open Paper36.SourceProtocol Paper36.SourceSummary
variable [Nonempty S] [MeasurableSingletonClass M]

open Paper36.SourceFresh

/-- Complete declaration of `Paper36.SourceFresh.actual_fresh_condDistrib`; source support: S5.Thmtheorem5. -/
theorem actual_fresh_condDistrib : ∀ (ν : Measure M) [IsProbabilityMeasure ν]
    (P : M → S × A → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (π : Meta → Policy S A) (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (planner : ProbabilityTheory.Kernel (History Meta S A T) Meta) [IsMarkovKernel planner]
    (s₀ : S) (dummy : Draw Meta A T) (k L : ℕ),
    condDistrib (actualWindow T k L s₀) (actualContext T k s₀)
      (SourceProtocol.measure ν P hP π hπ planner s₀ dummy) =ᵐ[
        (SourceProtocol.measure ν P hP π hπ planner s₀ dummy).map (actualContext T k s₀)]
      SourcePlanBlock.freshCtx P hP T k L := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation
  Paper36.Trajectories Paper36.AdaptiveTapes Paper36.SourceReplay
open scoped ENNReal
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  {M Meta : Type*} [MeasurableSpace M] [MeasurableSpace Meta] {T : ℕ}
open Paper36.SourceProtocol Paper36.SourceSummary
variable [Nonempty S] [MeasurableSingletonClass M]

open Paper36.SourceFresh

/-- Complete declaration of `Paper36.SourceFresh.actual_history_fresh`; source support: S5.Thmtheorem5. -/
theorem actual_history_fresh : ∀ (ν : Measure M) [IsProbabilityMeasure ν]
    (P : M → S × A → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (π : Meta → Policy S A) (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (planner : ProbabilityTheory.Kernel (History Meta S A T) Meta) [IsMarkovKernel planner]
    (s₀ : S) (dummy : Draw Meta A T) (k L : ℕ),
    (SourceProtocol.measure ν P hP π hπ planner s₀ dummy).map
      (fun ω => (historyInfo T k s₀ ω,actualWindow T k L s₀ ω)) =
      (SourceProtocol.measure ν P hP π hπ planner s₀ dummy).map (historyInfo T k s₀) ⊗ₘ
        freshHistory P hP T L := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation
  Paper36.Trajectories Paper36.AdaptiveTapes Paper36.SourceReplay
open scoped ENNReal
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  {M Meta : Type*} [MeasurableSpace M] [MeasurableSpace Meta] {T : ℕ}
open Paper36.SourceProtocol Paper36.SourceSummary
variable [Nonempty S] [MeasurableSingletonClass M]

open Paper36.SourceFresh

/-- Complete declaration of `Paper36.SourceFresh.actual_history_fresh_condDistrib`; source support: S5.Thmtheorem5. -/
theorem actual_history_fresh_condDistrib : ∀ (ν : Measure M) [IsProbabilityMeasure ν]
    (P : M → S × A → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (π : Meta → Policy S A) (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (planner : ProbabilityTheory.Kernel (History Meta S A T) Meta) [IsMarkovKernel planner]
    (s₀ : S) (dummy : Draw Meta A T) (k L : ℕ),
    condDistrib (actualWindow T k L s₀) (historyInfo T k s₀)
      (SourceProtocol.measure ν P hP π hπ planner s₀ dummy) =ᵐ[
        (SourceProtocol.measure ν P hP π hπ planner s₀ dummy).map (historyInfo T k s₀)]
      freshHistory P hP T L := by
  sorry

end

end P36Contract.SourceFresh

namespace P36Contract.SourceNativeConditional

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation
  Paper36.Trajectories Paper36.AdaptiveTapes Paper36.SourceReplay
open scoped ENNReal
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  {M Meta : Type*} [MeasurableSpace M] [MeasurableSpace Meta] {T : ℕ}
open Paper36.SourcePlanBlock
variable [Nonempty S] [Nonempty A]

open Paper36.SourceNativeConditional

/-- Complete declaration of `Paper36.SourceNativeConditional.actual_physicalLaw`; source support: S5.Thmtheorem5. -/
theorem actual_physicalLaw : ∀ [MeasurableSingletonClass M]
    (ν : Measure M) [IsProbabilityMeasure ν]
    (P : M → S × A → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (π : Meta → Policy S A) (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (planner : ProbabilityTheory.Kernel (History Meta S A T) Meta) [IsMarkovKernel planner]
    (s₀ : S) (dummy : Draw Meta A T) (k : ℕ),
    condDistrib (SourceProtocol.path (M := M) (Meta := Meta) s₀ T k) (actualInfo T k s₀)
      (SourceProtocol.measure ν P hP π hπ planner s₀ dummy) =ᵐ[
        (SourceProtocol.measure ν P hP π hπ planner s₀ dummy).map (actualInfo T k s₀)]
      trueInfoTrajectory π P hπ hP T s₀ := by
  sorry

end

end P36Contract.SourceNativeConditional

namespace P36Contract.SourceFiltration

section
open MeasureTheory ProbabilityTheory Paper36.Trajectories Paper36.SourceReplay
  Paper36.SourceProtocol Paper36.SourceSystem
universe u
variable {S A : Type u} [Fintype S] [Fintype A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  {M Code Meta : Type*} [MeasurableSpace M]
  [MeasurableSpace Code] [MeasurableSpace Meta] {T : ℕ}

open Paper36.SourceFiltration

/-- Complete declaration of `Paper36.SourceFiltration.info_comap_monotone`; source support: S5.Thmtheorem6. -/
theorem info_comap_monotone : ∀ (s₀ : S) (fallback : M × Code),
    Monotone (fun k => MeasurableSpace.comap
      (analystInfo (S := S) (A := A) (M := M) (Code := Code) T s₀ k) inferInstance) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.Trajectories Paper36.SourceReplay
  Paper36.SourceProtocol Paper36.SourceSystem
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  {M Code Meta : Type*} [MeasurableSpace M] [StandardBorelSpace M] [Nonempty M]
  [MeasurableSpace Code] [MeasurableSpace Meta] {T : ℕ}

open Paper36.SourceFiltration

/-- Complete declaration of `Paper36.SourceFiltration.info_comap`; source support: S5.Thmtheorem6. -/
theorem info_comap : ∀ (s₀ : S) (dummy : Draw (M × Code) A T) (k : ℕ),
    MeasurableSpace.comap (analystInfo (S := S) (A := A) (M := M) (Code := Code) T s₀ k) inferInstance =
      naturalFiltration s₀ dummy k := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.Trajectories Paper36.SourceReplay
  Paper36.SourceProtocol Paper36.SourceSystem
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  {M Code Meta : Type*} [MeasurableSpace M] [StandardBorelSpace M] [Nonempty M]
  [MeasurableSpace Code] [MeasurableSpace Meta] {T : ℕ}

open Paper36.SourceFiltration

/-- Complete declaration of `Paper36.SourceFiltration.path_measurable`; source support: S5.Thmtheorem6. -/
theorem path_measurable : ∀ (s₀ : S) (dummy : Draw (M × Code) A T) (k : ℕ),
    Measurable[naturalFiltration s₀ dummy (k+1),inferInstance]
      (SourceProtocol.path (S := S) (A := A) (M := M) (Meta := M × Code) s₀ T k) := by
  sorry

end

end P36Contract.SourceFiltration

namespace P36Contract.SourceTheorems

section
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested
  Paper36.Statistical Paper36.SourceReplay
open scoped BigOperators
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  {M Code : Type*} [MeasurableSpace M] [StandardBorelSpace M] [Nonempty M]
  [MeasurableSpace Code] {H : ℕ} (s₀ : S)
  (ν : Measure M) [IsProbabilityMeasure ν]
  (rows : M → S × A → Paper36.CVaR.Law S)
  (hrows : ∀ r t, Measurable (fun m => (rows m r).mass t))
  (π : Code → Paper36.Simulation.Policy S A)
  (hπ : ∀ h s a, Measurable (fun c => (π c h s).mass a))
  (planner : ProbabilityTheory.Kernel (History (M × Code) S A (H+1)) (M × Code))
  [IsMarkovKernel planner] (dummy : Draw (M × Code) A (H+1))
  (hBayes : Paper36.SourceSystem.BayesLaw (H+1) s₀ ν rows hrows π hπ planner dummy)

open Paper36.SourceTheorems

/-- Complete declaration of `Paper36.SourceTheorems.theorem_4_2`; source support: S4.Thmtheorem2. -/
theorem theorem_4_2 : ∀ (external : RowTapes.ExternalCategoricalConcentration (S:=S))
    (α τ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hτ : 0 ≤ τ)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1),
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
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested
  Paper36.Statistical Paper36.SourceReplay
open scoped BigOperators
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  {M Code : Type*} [MeasurableSpace M] [StandardBorelSpace M] [Nonempty M]
  [MeasurableSpace Code] {H : ℕ} (s₀ : S)
  (ν : Measure M) [IsProbabilityMeasure ν]
  (rows : M → S × A → Paper36.CVaR.Law S)
  (hrows : ∀ r t, Measurable (fun m => (rows m r).mass t))
  (π : Code → Paper36.Simulation.Policy S A)
  (hπ : ∀ h s a, Measurable (fun c => (π c h s).mass a))
  (planner : ProbabilityTheory.Kernel (History (M × Code) S A (H+1)) (M × Code))
  [IsMarkovKernel planner] (dummy : Draw (M × Code) A (H+1))
  (hBayes : Paper36.SourceSystem.BayesLaw (H+1) s₀ ν rows hrows π hπ planner dummy)

open Paper36.SourceTheorems

/-- Complete declaration of `Paper36.SourceTheorems.risk_bank_certificate`; source support: S5.Thmtheorem6. -/
theorem risk_bank_certificate : ∀ (external : RowTapes.ExternalCategoricalConcentration (S:=S))
    (α τ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    {K : ℕ} (hK : 1 ≤ K) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1),
    let P := SourceSystem.toPosteriorSystem (H+1) s₀ ν rows hrows π hπ planner dummy hBayes
    ∀ (O : BorelAlgorithm.BorelOracles α c r (H+1) s₀ τ (Main.support P))
      (hrun : ∀ n ω, Main.policy P n ω = Algorithm.selected O.toOracles
        (Main.target (S:=S) (A:=A) (H:=H) α) (Main.samples P) n ω),
    (SourceSystem.μ (H+1) s₀ ν rows hrows π hπ planner dummy).real {ω | Bounds.certificate (Fintype.card S) (Fintype.card A) (H+1) (Weights.W α (H+1)) (Weights.w α (H+1)) δ K -
      Bank.bank (Main.target (S:=S) (A:=A) (H:=H) α) (fun j => Main.deposit P α τ c j ω) K <
      Assembly.total (fun n ω => Main.trueRisk P α c n ω - τ) K ω} ≤ δ := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested
  Paper36.Statistical Paper36.SourceReplay
open scoped BigOperators
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  {M Code : Type*} [MeasurableSpace M] [StandardBorelSpace M] [Nonempty M]
  [MeasurableSpace Code] {H : ℕ} (s₀ : S)
  (ν : Measure M) [IsProbabilityMeasure ν]
  (rows : M → S × A → Paper36.CVaR.Law S)
  (hrows : ∀ r t, Measurable (fun m => (rows m r).mass t))
  (π : Code → Paper36.Simulation.Policy S A)
  (hπ : ∀ h s a, Measurable (fun c => (π c h s).mass a))
  (planner : ProbabilityTheory.Kernel (History (M × Code) S A (H+1)) (M × Code))
  [IsMarkovKernel planner] (dummy : Draw (M × Code) A (H+1))
  (hBayes : Paper36.SourceSystem.BayesLaw (H+1) s₀ ν rows hrows π hπ planner dummy)

open Paper36.SourceTheorems

/-- Complete declaration of `Paper36.SourceTheorems.stage_theorem_4_2`; source support: S4.Thmtheorem2, A2.Thmtheorem3. -/
theorem stage_theorem_4_2 : ∀ (external : RowTapes.ExternalCategoricalConcentration (S:=S))
    (β : ℕ → ℝ) (τ : ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1) (hτ : 0 ≤ τ)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1),
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
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested
  Paper36.Statistical Paper36.SourceReplay
open scoped BigOperators
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  {M Code : Type*} [MeasurableSpace M] [StandardBorelSpace M] [Nonempty M]
  [MeasurableSpace Code] {H : ℕ} (s₀ : S)
  (ν : Measure M) [IsProbabilityMeasure ν]
  (rows : M → S × A → Paper36.CVaR.Law S)
  (hrows : ∀ r t, Measurable (fun m => (rows m r).mass t))
  (π : Code → Paper36.Simulation.Policy S A)
  (hπ : ∀ h s a, Measurable (fun c => (π c h s).mass a))
  (planner : ProbabilityTheory.Kernel (History (M × Code) S A (H+1)) (M × Code))
  [IsMarkovKernel planner] (dummy : Draw (M × Code) A (H+1))
  (hBayes : Paper36.SourceSystem.BayesLaw (H+1) s₀ ν rows hrows π hπ planner dummy)

open Paper36.SourceTheorems

/-- Complete declaration of `Paper36.SourceTheorems.stage_risk_bank_certificate`; source support: S5.Thmtheorem6, A2.Thmtheorem3. -/
theorem stage_risk_bank_certificate : ∀ (external : RowTapes.ExternalCategoricalConcentration (S:=S))
    (β : ℕ → ℝ) (τ : ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    {K : ℕ} (hK : 1 ≤ K) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1),
    let P := SourceSystem.toPosteriorSystem (H+1) s₀ ν rows hrows π hπ planner dummy hBayes
    ∀ (O : StageAlgorithm.BorelOracles β c r (H+1) s₀ τ (StageMain.support P))
      (hrun : ∀ n ω, StageMain.policy P n ω = StageAlgorithm.selected O.toOracles
        (StageMain.target (S:=S) (A:=A) (H:=H) β) (StageMain.samples P) n ω),
    (SourceSystem.μ (H+1) s₀ ν rows hrows π hπ planner dummy).real {ω | Bounds.certificate (Fintype.card S) (Fintype.card A) (H+1) (Real.sqrt (Weights.stageWsq β (H+1))) (Weights.stagew β (H+1)) δ K -
      Bank.bank (StageMain.target (S:=S) (A:=A) (H:=H) β) (fun j => StageMain.deposit P β τ c j ω) K <
      Assembly.total (fun n ω => StageMain.trueRisk P β c n ω - τ) K ω} ≤ δ := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested
  Paper36.Statistical Paper36.SourceReplay
open scoped BigOperators
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  {M Code : Type*} [MeasurableSpace M] [StandardBorelSpace M] [Nonempty M]
  [MeasurableSpace Code] {H : ℕ} (s₀ : S)
  (ν : Measure M) [IsProbabilityMeasure ν]
  (rows : M → S × A → Paper36.CVaR.Law S)
  (hrows : ∀ r t, Measurable (fun m => (rows m r).mass t))
  (π : Code → Paper36.Simulation.Policy S A)
  (hπ : ∀ h s a, Measurable (fun c => (π c h s).mass a))
  (planner : ProbabilityTheory.Kernel (History (M × Code) S A (H+1)) (M × Code))
  [IsMarkovKernel planner] (dummy : Draw (M × Code) A (H+1))
  (hBayes : Paper36.SourceSystem.BayesLaw (H+1) s₀ ν rows hrows π hπ planner dummy)

open Paper36.SourceTheorems

/-- Complete declaration of `Paper36.SourceTheorems.corollary_B_1`; source support: A2.Thmtheorem1. -/
theorem corollary_B_1 : ∀ (external : RowTapes.ExternalCategoricalConcentration (S:=S))
    (α τ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hτ : 0 ≤ τ)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (ε ζ : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hζ : ∀ n, 0 ≤ ζ n),
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
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested
  Paper36.Statistical Paper36.SourceReplay
open scoped BigOperators
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  {M Code : Type*} [MeasurableSpace M] [StandardBorelSpace M] [Nonempty M]
  [MeasurableSpace Code] {H : ℕ} (s₀ : S)
  (ν : Measure M) [IsProbabilityMeasure ν]
  (rows : M → S × A → Paper36.CVaR.Law S)
  (hrows : ∀ r t, Measurable (fun m => (rows m r).mass t))
  (π : Code → Paper36.Simulation.Policy S A)
  (hπ : ∀ h s a, Measurable (fun c => (π c h s).mass a))
  (planner : ProbabilityTheory.Kernel (History (M × Code) S A (H+1)) (M × Code))
  [IsMarkovKernel planner] (dummy : Draw (M × Code) A (H+1))
  (hBayes : Paper36.SourceSystem.BayesLaw (H+1) s₀ ν rows hrows π hπ planner dummy)

open Paper36.SourceTheorems

/-- Complete declaration of `Paper36.SourceTheorems.stage_corollary_B_1`; source support: A2.Thmtheorem1, A2.Thmtheorem3. -/
theorem stage_corollary_B_1 : ∀ (external : RowTapes.ExternalCategoricalConcentration (S:=S))
    (β : ℕ → ℝ) (τ : ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1) (hτ : 0 ≤ τ)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (ε ζ : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hζ : ∀ n, 0 ≤ ζ n),
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
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested
  Paper36.Statistical Paper36.SourceReplay
open scoped BigOperators
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  {M Code : Type*} [MeasurableSpace M] [StandardBorelSpace M] [Nonempty M]
  [MeasurableSpace Code] {H : ℕ} (s₀ : S)
  (ν : Measure M) [IsProbabilityMeasure ν]
  (rows : M → S × A → Paper36.CVaR.Law S)
  (hrows : ∀ r t, Measurable (fun m => (rows m r).mass t))
  (π : Code → Paper36.Simulation.Policy S A)
  (hπ : ∀ h s a, Measurable (fun c => (π c h s).mass a))
  (planner : ProbabilityTheory.Kernel (History (M × Code) S A (H+1)) (M × Code))
  [IsMarkovKernel planner] (dummy : Draw (M × Code) A (H+1))
  (hBayes : Paper36.SourceSystem.BayesLaw (H+1) s₀ ν rows hrows π hπ planner dummy)

open Paper36.SourceTheorems

/-- Complete declaration of `Paper36.SourceTheorems.pathwise_calibration`; source support: S4.Thmtheorem2. -/
theorem pathwise_calibration : ∀ (α τ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hτ : 0 ≤ τ)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1),
    let P := SourceSystem.toPosteriorSystem (H+1) s₀ ν rows hrows π hπ planner dummy hBayes
    ∀ (hstrict : ∀ q ∈ Main.support P, minimumRisk α c (H+1) 0 s₀ q < τ),
    0 < Main.delta P α τ c ∧ ∀ᵐ ω ∂SourceSystem.μ (H+1) s₀ ν rows hrows π hπ planner dummy,
      (∀ K, (Bank.count (Main.target (S:=S) (A:=A) (H:=H) α) (fun j => Main.deposit P α τ c j ω) K : ℝ) ≤
        min (K:ℝ) ((Main.target (S:=S) (A:=A) (H:=H) α K + τ) / Main.delta P α τ c)) ∧
      Filter.Tendsto (fun K : ℕ => (Bank.count (Main.target (S:=S) (A:=A) (H:=H) α)
        (fun j => Main.deposit P α τ c j ω) K : ℝ) / (K:ℝ)) Filter.atTop (nhds 0) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested
  Paper36.Statistical Paper36.SourceReplay
open scoped BigOperators
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  {M Code : Type*} [MeasurableSpace M] [StandardBorelSpace M] [Nonempty M]
  [MeasurableSpace Code] {H : ℕ} (s₀ : S)
  (ν : Measure M) [IsProbabilityMeasure ν]
  (rows : M → S × A → Paper36.CVaR.Law S)
  (hrows : ∀ r t, Measurable (fun m => (rows m r).mass t))
  (π : Code → Paper36.Simulation.Policy S A)
  (hπ : ∀ h s a, Measurable (fun c => (π c h s).mass a))
  (planner : ProbabilityTheory.Kernel (History (M × Code) S A (H+1)) (M × Code))
  [IsMarkovKernel planner] (dummy : Draw (M × Code) A (H+1))
  (hBayes : Paper36.SourceSystem.BayesLaw (H+1) s₀ ν rows hrows π hπ planner dummy)

open Paper36.SourceTheorems

/-- Complete declaration of `Paper36.SourceTheorems.stage_pathwise_calibration`; source support: S4.Thmtheorem2, A2.Thmtheorem3. -/
theorem stage_pathwise_calibration : ∀ (β : ℕ → ℝ) (τ : ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1) (hτ : 0 ≤ τ)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1),
    let P := SourceSystem.toPosteriorSystem (H+1) s₀ ν rows hrows π hπ planner dummy hBayes
    ∀ (hstrict : ∀ q ∈ StageMain.support P, ∃ ρ : Simulation.Policy S A,
      StageRisk.risk β c ρ (RiskBridge.ofKernel q) (H+1) 0 s₀ < τ),
    0 < StageMain.delta P β τ c ∧ ∀ᵐ ω ∂SourceSystem.μ (H+1) s₀ ν rows hrows π hπ planner dummy,
      (∀ K, (Bank.count (StageMain.target (S:=S) (A:=A) (H:=H) β) (fun j => StageMain.deposit P β τ c j ω) K : ℝ) ≤
        min (K:ℝ) ((StageMain.target (S:=S) (A:=A) (H:=H) β K + τ) / StageMain.delta P β τ c)) ∧
      Filter.Tendsto (fun K : ℕ => (Bank.count (StageMain.target (S:=S) (A:=A) (H:=H) β)
        (fun j => StageMain.deposit P β τ c j ω) K : ℝ) / (K:ℝ)) Filter.atTop (nhds 0) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested
  Paper36.Statistical Paper36.SourceReplay
open scoped BigOperators
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  {M Code : Type*} [MeasurableSpace M] [StandardBorelSpace M] [Nonempty M]
  [MeasurableSpace Code] {H : ℕ} (s₀ : S)
  (ν : Measure M) [IsProbabilityMeasure ν]
  (rows : M → S × A → Paper36.CVaR.Law S)
  (hrows : ∀ r t, Measurable (fun m => (rows m r).mass t))
  (π : Code → Paper36.Simulation.Policy S A)
  (hπ : ∀ h s a, Measurable (fun c => (π c h s).mass a))
  (planner : ProbabilityTheory.Kernel (History (M × Code) S A (H+1)) (M × Code))
  [IsMarkovKernel planner] (dummy : Draw (M × Code) A (H+1))
  (hBayes : Paper36.SourceSystem.BayesLaw (H+1) s₀ ν rows hrows π hπ planner dummy)

open Paper36.SourceTheorems

/-- Complete declaration of `Paper36.SourceTheorems.actual_prior`; source support: S4.Thmtheorem2, S5.Thmtheorem5. -/
theorem actual_prior : let P := SourceSystem.toPosteriorSystem (H+1) s₀ ν rows hrows π hπ planner dummy hBayes
    PosteriorAlgorithm.prior (μ := SourceSystem.μ (H+1) s₀ ν rows hrows π hπ planner dummy) (Main.decode P) P.latent =
      ν.map (fun m => Measurability.regularKernel (fun s a => rows m (s,a))) := by
  sorry

end

end P36Contract.SourceTheorems

namespace P36Contract.SourceSystem

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation
  Paper36.Trajectories Paper36.AdaptiveTapes Paper36.SourceReplay
  Paper36.SourceProtocol Paper36.StatisticalCounts
open scoped ENNReal
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  {M Code : Type*} [MeasurableSpace M] [StandardBorelSpace M] [Nonempty M]
  [MeasurableSpace Code]
variable (T : ℕ) (s₀ : S)
variable (ν : Measure M) [IsProbabilityMeasure ν]
  (P : M → S × A → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
  (π : Code → Policy S A) (hπ : ∀ h s a, Measurable (fun c => (π c h s).mass a))
  (planner : ProbabilityTheory.Kernel (History (M × Code) S A T) (M × Code))
  [IsMarkovKernel planner] (dummy : Draw (M × Code) A T)

open Paper36.SourceSystem

/-- Complete declaration of `Paper36.SourceSystem.physicalLaw`; source support: S5.Thmtheorem5. -/
theorem physicalLaw : PhysicalLaw T s₀ ν P hP π hπ planner dummy := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation
  Paper36.Trajectories Paper36.AdaptiveTapes Paper36.SourceReplay
  Paper36.SourceProtocol Paper36.StatisticalCounts
open scoped ENNReal
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  {M Code : Type*} [MeasurableSpace M] [StandardBorelSpace M] [Nonempty M]
  [MeasurableSpace Code]
variable (T : ℕ) (s₀ : S)
variable (ν : Measure M) [IsProbabilityMeasure ν]
  (P : M → S × A → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
  (π : Code → Policy S A) (hπ : ∀ h s a, Measurable (fun c => (π c h s).mass a))
  (planner : ProbabilityTheory.Kernel (History (M × Code) S A T) (M × Code))
  [IsMarkovKernel planner] (dummy : Draw (M × Code) A T)

open Paper36.SourceSystem

/-- Complete declaration of `Paper36.SourceSystem.prior_law`; source support: S4.Thmtheorem2, S5.Thmtheorem5. -/
theorem prior_law : (μ T s₀ ν P hP π hπ planner dummy).map
      (fun ω : Sample M (M × Code) S A T => ω.1.1) = ν := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation
  Paper36.Trajectories Paper36.AdaptiveTapes Paper36.SourceReplay
  Paper36.SourceProtocol Paper36.StatisticalCounts
open scoped ENNReal
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  {M Code : Type*} [MeasurableSpace M] [StandardBorelSpace M] [Nonempty M]
  [MeasurableSpace Code]
variable (T : ℕ) (s₀ : S)
variable (ν : Measure M) [IsProbabilityMeasure ν]
  (P : M → S × A → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
  (π : Code → Policy S A) (hπ : ∀ h s a, Measurable (fun c => (π c h s).mass a))
  (planner : ProbabilityTheory.Kernel (History (M × Code) S A T) (M × Code))
  [IsMarkovKernel planner] (dummy : Draw (M × Code) A T)

open Paper36.SourceSystem

/-- Complete declaration of `Paper36.SourceSystem.exists_posteriorSystem`; source support: S4.Thmtheorem2, S5.Thmtheorem5. -/
theorem exists_posteriorSystem : ∀ (hBayes : BayesLaw T s₀ ν P hP π hπ planner dummy),
    ∃ Q : Statistical.PosteriorSystem (Model := M) (Hist := History (M × Code) S A T)
        (episodeSystem T s₀ ν P hP π hπ planner dummy),
      Q.latent = (fun ω => ω.1.1) ∧
      Q.tape = (fun ω row n => ω.1.2 (row,n)) ∧
      (∀ k ω, (episodeSystem T s₀ ν P hP π hπ planner dummy).path k ω =
        SourceProtocol.path s₀ T k ω) ∧
      (μ T s₀ ν P hP π hπ planner dummy).map Q.latent = ν := by
  sorry

end

end P36Contract.SourceSystem

namespace P36Contract.SourceEndpointTheorems

section
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested
  Paper36.Statistical Paper36.SourceReplay
open scoped BigOperators
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  {M Code : Type*} [MeasurableSpace M] [StandardBorelSpace M] [Nonempty M]
  [MeasurableSpace Code] (s₀ : S)
  (ν : Measure M) [IsProbabilityMeasure ν]
  (rows : M → S × A → Paper36.CVaR.Law S)
  (hrows : ∀ r t, Measurable (fun m => (rows m r).mass t))
  (π : Code → Paper36.Simulation.Policy S A)
  (hπ : ∀ h s a, Measurable (fun c => (π c h s).mass a))
  (planner : ProbabilityTheory.Kernel (History (M × Code) S A 1) (M × Code))
  [IsMarkovKernel planner] (dummy : Draw (M × Code) A 1)
  (hBayes : Paper36.SourceSystem.BayesLaw 1 s₀ ν rows hrows π hπ planner dummy)

open Paper36.SourceEndpointTheorems

/-- Complete declaration of `Paper36.SourceEndpointTheorems.corollary_B_1_horizon_one`; source support: A2.Thmtheorem1. -/
theorem corollary_B_1_horizon_one : ∀ (α τ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (ε ζ : ℕ → ℝ),
    let P := SourceSystem.toPosteriorSystem 1 s₀ ν rows hrows π hπ planner dummy hBayes
    ∀ (O : BorelAlgorithm.BorelOracles α c r 1 s₀ τ (Main.support P))
      (hcert : ∀ᵐ ω ∂SourceSystem.μ 1 s₀ ν rows hrows π hπ planner dummy, Main.RealizedCertificates P α τ c r ε ζ ω) (K : ℕ),
    (∫ ω, Assembly.total (fun n ω => Main.trueRisk P α c n ω - τ) K ω ∂SourceSystem.μ 1 s₀ ν rows hrows π hπ planner dummy) ≤ ∑ n ∈ Finset.range K, ε n ∧
    (∫ ω, Assembly.total (fun n ω => Main.optimum P α τ c r ω - Main.trueReward P r n ω) K ω ∂SourceSystem.μ 1 s₀ ν rows hrows π hπ planner dummy) ≤ ∑ n ∈ Finset.range K, ζ n := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested
  Paper36.Statistical Paper36.SourceReplay
open scoped BigOperators
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  {M Code : Type*} [MeasurableSpace M] [StandardBorelSpace M] [Nonempty M]
  [MeasurableSpace Code] (s₀ : S)
  (ν : Measure M) [IsProbabilityMeasure ν]
  (rows : M → S × A → Paper36.CVaR.Law S)
  (hrows : ∀ r t, Measurable (fun m => (rows m r).mass t))
  (π : Code → Paper36.Simulation.Policy S A)
  (hπ : ∀ h s a, Measurable (fun c => (π c h s).mass a))
  (planner : ProbabilityTheory.Kernel (History (M × Code) S A 1) (M × Code))
  [IsMarkovKernel planner] (dummy : Draw (M × Code) A 1)
  (hBayes : Paper36.SourceSystem.BayesLaw 1 s₀ ν rows hrows π hπ planner dummy)

open Paper36.SourceEndpointTheorems

/-- Complete declaration of `Paper36.SourceEndpointTheorems.theorem_4_2_horizon_one`; source support: S4.Thmtheorem2. -/
theorem theorem_4_2_horizon_one : ∀ (α τ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1),
    let P := SourceSystem.toPosteriorSystem 1 s₀ ν rows hrows π hπ planner dummy hBayes
    ∀ (O : BorelAlgorithm.BorelOracles α c r 1 s₀ τ (Main.support P))
      (hcert : ∀ᵐ ω ∂SourceSystem.μ 1 s₀ ν rows hrows π hπ planner dummy, Main.RealizedCertificates P α τ c r (fun _ => 0) (fun _ => 0) ω) (K : ℕ),
    (∫ ω, Assembly.total (fun n ω => Main.trueRisk P α c n ω - τ) K ω ∂SourceSystem.μ 1 s₀ ν rows hrows π hπ planner dummy) ≤ 0 ∧
    (∫ ω, Assembly.total (fun n ω => Main.optimum P α τ c r ω - Main.trueReward P r n ω) K ω ∂SourceSystem.μ 1 s₀ ν rows hrows π hπ planner dummy) = 0 ∧
    (∀ ω, Bank.bank (Main.target (S:=S) (A:=A) (H:=0) α)
      (fun j => Main.deposit P α τ c j ω) K = 0 ∧
      Bank.count (Main.target (S:=S) (A:=A) (H:=0) α)
        (fun j => Main.deposit P α τ c j ω) K = 0) := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested
  Paper36.Statistical Paper36.SourceReplay
open scoped BigOperators
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  {M Code : Type*} [MeasurableSpace M] [StandardBorelSpace M] [Nonempty M]
  [MeasurableSpace Code] (s₀ : S)
  (ν : Measure M) [IsProbabilityMeasure ν]
  (rows : M → S × A → Paper36.CVaR.Law S)
  (hrows : ∀ r t, Measurable (fun m => (rows m r).mass t))
  (π : Code → Paper36.Simulation.Policy S A)
  (hπ : ∀ h s a, Measurable (fun c => (π c h s).mass a))
  (planner : ProbabilityTheory.Kernel (History (M × Code) S A 1) (M × Code))
  [IsMarkovKernel planner] (dummy : Draw (M × Code) A 1)
  (hBayes : Paper36.SourceSystem.BayesLaw 1 s₀ ν rows hrows π hπ planner dummy)

open Paper36.SourceEndpointTheorems

/-- Complete declaration of `Paper36.SourceEndpointTheorems.stage_corollary_B_1_horizon_one`; source support: A2.Thmtheorem1, A2.Thmtheorem3. -/
theorem stage_corollary_B_1_horizon_one : ∀ (β : ℕ → ℝ) (τ : ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (ε ζ : ℕ → ℝ),
    let P := SourceSystem.toPosteriorSystem 1 s₀ ν rows hrows π hπ planner dummy hBayes
    ∀ (O : StageAlgorithm.BorelOracles β c r 1 s₀ τ (StageMain.support P))
      (hcert : ∀ᵐ ω ∂SourceSystem.μ 1 s₀ ν rows hrows π hπ planner dummy, ∀ n,
      ¬Bank.calibrates (StageMain.target (S:=S) (A:=A) (H:=0) β)
        (fun j => StageMain.deposit P β τ c j ω) n →
      StageMain.sampledRisk P β c n ω ≤ τ + ε n ∧
        StageMain.sampledOptimum P β τ c r n ω - StageMain.sampledReward P r n ω ≤ ζ n) (K : ℕ),
    (∫ ω, Assembly.total (fun n ω => StageMain.trueRisk P β c n ω - τ) K ω ∂SourceSystem.μ 1 s₀ ν rows hrows π hπ planner dummy) ≤ ∑ n ∈ Finset.range K, ε n ∧
    (∫ ω, Assembly.total (fun n ω => StageMain.optimum P β τ c r ω - StageMain.trueReward P r n ω) K ω ∂SourceSystem.μ 1 s₀ ν rows hrows π hπ planner dummy) ≤ ∑ n ∈ Finset.range K, ζ n := by
  sorry

end

section
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested
  Paper36.Statistical Paper36.SourceReplay
open scoped BigOperators
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  {M Code : Type*} [MeasurableSpace M] [StandardBorelSpace M] [Nonempty M]
  [MeasurableSpace Code] (s₀ : S)
  (ν : Measure M) [IsProbabilityMeasure ν]
  (rows : M → S × A → Paper36.CVaR.Law S)
  (hrows : ∀ r t, Measurable (fun m => (rows m r).mass t))
  (π : Code → Paper36.Simulation.Policy S A)
  (hπ : ∀ h s a, Measurable (fun c => (π c h s).mass a))
  (planner : ProbabilityTheory.Kernel (History (M × Code) S A 1) (M × Code))
  [IsMarkovKernel planner] (dummy : Draw (M × Code) A 1)
  (hBayes : Paper36.SourceSystem.BayesLaw 1 s₀ ν rows hrows π hπ planner dummy)

open Paper36.SourceEndpointTheorems

/-- Complete declaration of `Paper36.SourceEndpointTheorems.stage_theorem_4_2_horizon_one`; source support: S4.Thmtheorem2, A2.Thmtheorem3. -/
theorem stage_theorem_4_2_horizon_one : ∀ (β : ℕ → ℝ) (τ : ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1),
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
  sorry

end

end P36Contract.SourceEndpointTheorems
