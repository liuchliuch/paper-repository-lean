import Paper36.Statistical
import Paper36.PosteriorAlgorithm
import Paper36.SourceBank
import Paper36.Approximation
import Paper36.Endpoints

/-! The source main theorem on the actual posterior experiment. The only
statistical external input is the two published categorical concentration
inequalities. The model error and posterior comparator symmetry are proved
inside this module's dependency closure, rather than being theorem premises. -/
namespace Paper36.Main
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested Paper36.Algorithm
  Paper36.StatisticalCounts Paper36.Statistical
open scoped BigOperators
noncomputable section
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {Ω Info Model Hist : Type*} [MeasurableSpace Ω] [MeasurableSpace Info]
  [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model] [MeasurableSpace Hist]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℕ} {s₀ : S}
  {E : EpisodeSystem μ Info S A (H+1) s₀}
  (P : PosteriorSystem (Model := Model) (Hist := Hist) E)

abbrev decode (m : Model) : Nested.Kernel S A := Measurability.regularKernel (P.decode m)
abbrev samples (k : ℕ) (ω : Ω) : Nested.Kernel S A := decode P (P.sampled k ω)
abbrev truth (ω : Ω) : Nested.Kernel S A := decode P (P.latent ω)
abbrev policy (k : ℕ) (ω : Ω) : Nested.Policy S A := Measurability.regularPolicy (P.policies ω k)
abbrev support : Set (Nested.Kernel S A) := (PosteriorAlgorithm.prior (μ := μ) (decode P) P.latent).support
abbrev delta (α τ : ℝ) (c : ℕ → S → A → ℝ) : ℝ :=
  PosteriorAlgorithm.gap (μ := μ) (decode P) P.latent α τ c (H+1) s₀
abbrev target (α : ℝ) : ℕ → ℝ := SourceBank.target (S := S) (A := A) α (H+1)
abbrev deposit (α τ : ℝ) (c : ℕ → S → A → ℝ) :=
  Algorithm.deposits α τ c (H+1) s₀ (samples P)
abbrev trueRisk (α : ℝ) (c : ℕ → S → A → ℝ) (k : ℕ) (ω : Ω) :=
  Nested.risk α c (policy P k ω) (truth P ω) (H+1) 0 s₀
abbrev sampledRisk (α : ℝ) (c : ℕ → S → A → ℝ) (k : ℕ) (ω : Ω) :=
  Nested.risk α c (policy P k ω) (samples P k ω) (H+1) 0 s₀
abbrev trueReward (r : ℕ → S → A → ℝ) (k : ℕ) (ω : Ω) :=
  Nested.reward r (policy P k ω) (truth P ω) (H+1) 0 s₀
abbrev sampledReward (r : ℕ → S → A → ℝ) (k : ℕ) (ω : Ω) :=
  Nested.reward r (policy P k ω) (samples P k ω) (H+1) 0 s₀
abbrev optimum (α τ : ℝ) (c r : ℕ → S → A → ℝ) (ω : Ω) :=
  constrainedValue α c r (H+1) s₀ τ (truth P ω)
abbrev sampledOptimum (α τ : ℝ) (c r : ℕ → S → A → ℝ) (k : ℕ) (ω : Ω) :=
  constrainedValue α c r (H+1) s₀ τ (samples P k ω)

def rewardAllowance (K : ℕ) : ℝ :=
  8 * (H+1) * Real.sqrt (H+1) * Real.sqrt
    ((Fintype.card S : ℝ) * (Fintype.card A : ℝ) * (K : ℝ) *
      Bounds.rewardLog (Fintype.card S) (Fintype.card A) (H+1) K) + (H+1 : ℝ)/2

lemma decode_measurable : Measurable (decode P) := Measurability.measurable_regularKernel P.decode P.decode_meas
lemma samples_measurable (k : ℕ) : Measurable (samples P k) := (decode_measurable P).comp (P.sampled_meas k)
lemma truth_measurable : Measurable (truth P) := (decode_measurable P).comp P.latent_meas

lemma support_ae : ∀ᵐ ω ∂μ, truth P ω ∈ support P ∧ ∀ k, samples P k ω ∈ support P :=
  PosteriorAlgorithm.posterior_support _ (decode_measurable P) _ P.latent_meas _ P.sampled_meas
    _ P.history_meas P.posterior

lemma riskError_eq (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1) (k : ℕ) (ω : Ω) :
    P.riskError α c k ω = trueRisk P α c k ω - sampledRisk P α c k ω := by
  unfold PosteriorSystem.riskError
  rw [Measurability.envelope_risk_eq_nested α hα hα1 c hc,
    Measurability.envelope_risk_eq_nested α hα hα1 c hc, P.latent_match]
  rfl

lemma reward_bridge (r : ℕ → S → A → ℝ) (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (π : Simulation.Policy S A) (q : Simulation.Kernel S A) (n h : ℕ) (s : S) :
    HybridCharging.ordinaryReward r π q n h s =
      Nested.reward r (Measurability.regularPolicy π) (Measurability.regularKernel q) n h s := by
  unfold HybridCharging.ordinaryReward
  rw [Measurability.envelope_risk_eq_nested 1 (by norm_num) le_rfl r hr,
    Endpoints.nested_one_eq_expected_cost r hr]

lemma rewardError_eq (r : ℕ → S → A → ℝ) (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (k : ℕ) (ω : Ω) : P.rewardError r k ω = sampledReward P r k ω - trueReward P r k ω := by
  unfold PosteriorSystem.rewardError
  rw [reward_bridge r hr, reward_bridge r hr, P.latent_match]
  rfl

lemma trueRisk_integrable (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1) (k : ℕ) :
    Integrable (trueRisk P α c k) μ := by
  have hi := Measurability.integrable_risk μ α hα hα1 c hc (fun ω => P.policies ω k)
    E.latent (P.policy_mass_measurable k) P.true_mass_measurable (H+1) 0 s₀
  exact hi.congr (ae_of_all _ (fun ω => by
    change Simulation.risk α c (P.policies ω k) (E.latent ω) (H+1) 0 s₀ = _
    rw [Measurability.envelope_risk_eq_nested α hα hα1 c hc, P.latent_match]))

lemma sampledRisk_integrable (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1) (k : ℕ) :
    Integrable (sampledRisk P α c k) μ := by
  have hi := Measurability.integrable_risk μ α hα hα1 c hc (fun ω => P.policies ω k)
    (fun ω => P.sampledKernels ω k) (P.policy_mass_measurable k) (P.sampled_mass_measurable k) (H+1) 0 s₀
  exact hi.congr (ae_of_all _ (fun ω => Measurability.envelope_risk_eq_nested α hα hα1 c hc _ _ _ _ _))

lemma trueReward_integrable (r : ℕ → S → A → ℝ) (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (k : ℕ) :
    Integrable (trueReward P r k) μ := by
  have hi := Measurability.integrable_reward μ r hr (fun ω => P.policies ω k) E.latent
    (P.policy_mass_measurable k) P.true_mass_measurable (H+1) 0 s₀
  exact hi.congr (ae_of_all _ (fun ω => by simp only [Measurability.reward, P.latent_match]))

lemma sampledReward_integrable (r : ℕ → S → A → ℝ) (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (k : ℕ) :
    Integrable (sampledReward P r k) μ :=
  Measurability.integrable_reward μ r hr (fun ω => P.policies ω k) (fun ω => P.sampledKernels ω k)
    (P.policy_mass_measurable k) (P.sampled_mass_measurable k) (H+1) 0 s₀

lemma optimum_integrable {α τ : ℝ} {c r : ℕ → S → A → ℝ}
    (O : BorelAlgorithm.BorelOracles α c r (H+1) s₀ τ (support P))
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) : Integrable (optimum P α τ c r) μ := by
  apply (BorelAlgorithm.integrable_comparator μ O hr (truth P) (truth_measurable P)).congr
  filter_upwards [support_ae P] with ω hω
  exact BorelAlgorithm.comparator_eq_source O hω.1

lemma sampledOptimum_integrable {α τ : ℝ} {c r : ℕ → S → A → ℝ}
    (O : BorelAlgorithm.BorelOracles α c r (H+1) s₀ τ (support P))
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (k : ℕ) :
    Integrable (sampledOptimum P α τ c r k) μ := by
  apply (BorelAlgorithm.integrable_comparator μ O hr (samples P k) (samples_measurable P k)).congr
  filter_upwards [support_ae P] with ω hω
  exact BorelAlgorithm.comparator_eq_source O (hω.2 k)

/-- Equation (5.18) for the actual constrained optimum, without a symmetry premise. -/
lemma comparator_symmetry {α τ : ℝ} {c r : ℕ → S → A → ℝ}
    (O : BorelAlgorithm.BorelOracles α c r (H+1) s₀ τ (support P))
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (K : ℕ) :
    (∫ ω, Assembly.total (fun k ω => optimum P α τ c r ω - sampledOptimum P α τ c r k ω) K ω ∂μ) = 0 := by
  rw [show (∫ ω, Assembly.total (fun k ω => optimum P α τ c r ω - sampledOptimum P α τ c r k ω) K ω ∂μ) =
      ∑ k ∈ Finset.range K, ∫ ω, optimum P α τ c r ω - sampledOptimum P α τ c r k ω ∂μ from
    integral_finset_sum _ (fun k _ => (optimum_integrable P O hr).sub (sampledOptimum_integrable P O hr k))]
  apply Finset.sum_eq_zero
  intro k _
  exact PosteriorAlgorithm.comparator_symmetry _ (decode_measurable P) _ _ P.latent_meas
    (P.sampled_meas k) _ (P.history_meas k) (P.posterior k) O hr
    (by filter_upwards [support_ae P] with ω hω; exact ⟨hω.1, hω.2 k⟩)

/-- The actual statistical theorem supplies the expectation input to the bank proof. -/
lemma modelRisk_bound (external : RowTapes.ExternalCategoricalConcentration (S := S))
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (c : ℕ → S → A → ℝ)
    (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1) {K : ℕ} (hK : 1 ≤ K) :
    (∫ ω, Assembly.total (fun k ω => trueRisk P α c k ω - sampledRisk P α c k ω) K ω ∂μ) ≤
      Target.confidence (Target.scale (Weights.W α (H+1)) (Fintype.card S) (Fintype.card A))
        (Fintype.card S) (Fintype.card A) (H+1) K * Real.sqrt (K : ℝ) +
          SourceBank.lowConstant (S := S) (A := A) α (H+1) := by
  have hs := PosteriorSystem.lemma_5_5 E P external α hα hα1 c hc hK
  rw [show (∫ ω, Assembly.total (fun k ω => trueRisk P α c k ω - sampledRisk P α c k ω) K ω ∂μ) =
      ∑ k ∈ Finset.range K, ∫ ω, P.riskError α c k ω ∂μ from by
    simp_rw [← riskError_eq P α hα hα1 c hc]
    exact integral_finset_sum _ (fun k _ => P.riskError_integrable α hα hα1 c hc k)]
  simpa only [SourceBank.lowConstant, Nat.cast_add, Nat.cast_one] using hs

lemma modelReward_bound (external : RowTapes.ExternalCategoricalConcentration (S := S))
    (r : ℕ → S → A → ℝ) (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) {K : ℕ} (hK : 1 ≤ K) :
    (∫ ω, Assembly.total (fun k ω => sampledReward P r k ω - trueReward P r k ω) K ω ∂μ) ≤
      rewardAllowance (S := S) (A := A) (H := H) K := by
  have hs := PosteriorSystem.lemma_5_8 E P external r hr hK
  rw [show (∫ ω, Assembly.total (fun k ω => sampledReward P r k ω - trueReward P r k ω) K ω ∂μ) =
      ∑ k ∈ Finset.range K, ∫ ω, P.rewardError r k ω ∂μ from by
    simp_rw [← rewardError_eq P r hr]
    exact integral_finset_sum _ (fun k _ => P.rewardError_integrable r hr k)]
  exact hs

/-- Main statistical/bank assembly for certified realized oracle calls. Only
one-call feasibility/optimality specifications are inputs; the cumulative
probabilistic conclusions are all derived. This also proves Corollary B.1. -/
theorem certified_performance
    (external : RowTapes.ExternalCategoricalConcentration (S := S))
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
    {K : ℕ} (hK : 1 ≤ K) :
    ((∫ ω, Assembly.total (fun n ω => trueRisk P α c n ω - τ) K ω ∂μ) ≤
      SourceBank.riskEnvelope (S := S) (A := A) α (delta P α τ c) (H+1) + ∑ n ∈ Finset.range K, ε n) ∧
    ((∫ ω, Assembly.total (fun n ω => optimum P α τ c r ω - trueReward P r n ω) K ω ∂μ) ≤
      rewardAllowance (S := S) (A := A) (H := H) K + (H+1 : ℝ) *
        ((target (S := S) (A := A) (H := H) α K + τ) / delta P α τ c) + ∑ n ∈ Finset.range K, ζ n) ∧
    ((∫ ω, Assembly.countRV (target (S := S) (A := A) (H := H) α) (deposit P α τ c) K ω ∂μ) ≤
      min (K : ℝ) ((target (S := S) (A := A) (H := H) α K + τ) / delta P α τ c)) := by
  have hg := PosteriorAlgorithm.gap_positive _ (decode_measurable P) _ P.latent_meas
    α τ hα hα1 (H+1) c hc s₀ hstrict
  have hdim := SourceBank.dimensions (A := A) s₀ (show 1 ≤ H+1 by omega)
  have hd := BorelAlgorithm.measurable_deposits α τ c (H+1) s₀ (samples P) (samples_measurable P)
  have hdep : ∀ᵐ ω ∂μ, Assembly.DepositBounds (target (S := S) (A := A) (H := H) α)
      (deposit P α τ c) (delta P α τ c) τ ω := by
    filter_upwards [support_ae P] with ω hω
    have hh := Algorithm.actual_deposit_bounds α τ (delta P α τ c) hα.le c hc (H+1) s₀
      (support P) hg.2 (samples P) ω hω.2
    exact fun n _ => hh n
  simpa only [SourceBank.riskEnvelope, SourceBank.residual, target, SourceBank.target, Nat.cast_add, Nat.cast_one] using
    Assembly.conditional_main_bounds (D := SourceBank.lowConstant (S := S) (A := A) α (H+1))
      (Q := rewardAllowance (S := S) (A := A) (H := H) K) (deposit P α τ c) (trueRisk P α c) (sampledRisk P α c)
    (fun _ => optimum P α τ c r) (sampledOptimum P α τ c r) (trueReward P r) (sampledReward P r)
    ε ζ K hK hdim.1 hdim.2.1 hdim.2.2 (Weights.W_nonneg α (H+1)) hg.1 hτ hd hdep
    (trueRisk_integrable P α hα hα1 c hc) (sampledRisk_integrable P α hα hα1 c hc)
    (fun _ => optimum_integrable P O hr) (sampledOptimum_integrable P O hr)
    (trueReward_integrable P r hr) (sampledReward_integrable P r hr) hε hζ hriskOracle (by simpa only [target, SourceBank.target, Nat.cast_add, Nat.cast_one] using hrewardOracle)
    (by simpa only [Nat.cast_add, Nat.cast_one] using modelRisk_bound P external α hα hα1 c hc hK)
    (modelReward_bound P external r hr hK)
    (comparator_symmetry P O hr K)

/-- Theorem 4.2, (4.10)--(4.11), for actual Algorithm 1. The induced gap is a
function of the original arbitrary prior. The execution rule itself has no K or
gap argument. The exact H=1 strengthening is in SourceEndpoints. -/
theorem theorem_4_2
    (external : RowTapes.ExternalCategoricalConcentration (S := S))
    (α τ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hτ : 0 ≤ τ)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (hstrict : ∀ q ∈ support P, minimumRisk α c (H+1) 0 s₀ q < τ)
    (O : BorelAlgorithm.BorelOracles α c r (H+1) s₀ τ (support P))
    (hrun : ∀ n ω, policy P n ω = Algorithm.selected O.toOracles
      (target (S := S) (A := A) (H := H) α) (samples P) n ω) :
    ∀ K, 1 ≤ K →
    ((∫ ω, Assembly.total (fun n ω => trueRisk P α c n ω - τ) K ω ∂μ) ≤
      SourceBank.riskEnvelope (S := S) (A := A) α (delta P α τ c) (H+1)) ∧
    ((∫ ω, Assembly.total (fun n ω => optimum P α τ c r ω - trueReward P r n ω) K ω ∂μ) ≤
      rewardAllowance (S := S) (A := A) (H := H) K + (H+1 : ℝ) *
        ((target (S := S) (A := A) (H := H) α K + τ) / delta P α τ c)) ∧
    ((∫ ω, Assembly.countRV (target (S := S) (A := A) (H := H) α) (deposit P α τ c) K ω ∂μ) ≤
      min (K : ℝ) ((target (S := S) (A := A) (H := H) α K + τ) / delta P α τ c)) := by
  intro K hK
  have hro : ∀ᵐ ω ∂μ, ∀ n,
      (Bank.calibrates (target (S := S) (A := A) (H := H) α) (fun j => deposit P α τ c j ω) n →
        sampledRisk P α c n ω = τ - deposit P α τ c (n+1) ω) ∧
      (¬Bank.calibrates (target (S := S) (A := A) (H := H) α) (fun j => deposit P α τ c j ω) n →
        sampledRisk P α c n ω ≤ τ + 0) := by
    filter_upwards [support_ae P] with ω hω
    intro n
    have hh := Algorithm.selected_sampled_risk O.toOracles
      (target (S := S) (A := A) (H := H) α) (samples P) n ω (hω.2 n)
    simpa only [sampledRisk, hrun, add_zero] using hh
  have hwo : ∀ᵐ ω ∂μ, ∀ n,
      (Bank.calibrates (target (S := S) (A := A) (H := H) α) (fun j => deposit P α τ c j ω) n →
        sampledOptimum P α τ c r n ω - sampledReward P r n ω ≤ (H+1 : ℝ)) ∧
      (¬Bank.calibrates (target (S := S) (A := A) (H := H) α) (fun j => deposit P α τ c j ω) n →
        sampledOptimum P α τ c r n ω - sampledReward P r n ω ≤ 0) := by
    filter_upwards [support_ae P] with ω hω
    intro n
    have hh := Algorithm.selected_sampled_reward O.toOracles hr
      (target (S := S) (A := A) (H := H) α) (samples P) n ω (hω.2 n)
    simp only [sampledOptimum, sampledReward, hrun]
    exact ⟨by simpa only [Nat.cast_add, Nat.cast_one] using hh.1, fun hn => (hh.2 hn).le⟩
  simpa only [Finset.sum_const_zero, add_zero] using
    certified_performance P external α τ hα hα1 hτ c r hc hr hstrict O
      (fun _ => 0) (fun _ => 0) (fun _ => le_rfl) (fun _ => le_rfl) hro hwo hK

end
end Paper36.Main
