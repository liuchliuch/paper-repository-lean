import Paper36.Main
import Paper36.StageAlgorithm
import Paper36.StageStatistical

/-! The source main theorem on the actual posterior experiment. The only
statistical external input is the two published categorical concentration
inequalities. The model error and posterior comparator symmetry are proved
inside this module's dependency closure, rather than being theorem premises. -/
namespace Paper36.StageApproximation
open Paper36.Regularity Paper36.Nested Paper36.StageAlgorithm
open scoped BigOperators
noncomputable section
variable {S A Ω : Type*} [Fintype S] [Fintype A] [Nonempty A]

structure Oracles (β : ℕ → ℝ) (c r : ℕ → S → A → ℝ) (H : ℕ) (s₁ : S)
    (τ : ℝ) (Q : Set (Kernel S A)) (ε ζ : ℕ → ℝ) where
  calibration : Kernel S A → Policy S A
  exploitation : ℕ → Kernel S A → Policy S A
  cal_exact : ∀ q ∈ Q, risk β c (calibration q) q H 0 s₁ = StageAlgorithm.minimumRisk β c H s₁ q
  exp_risk : ∀ n q, q ∈ Q → risk β c (exploitation n q) q H 0 s₁ ≤ τ + ε n
  exp_reward : ∀ n q, q ∈ Q → constrainedValue β c r H s₁ τ q ≤
    reward r (exploitation n q) q H 0 s₁ + ζ n

def selected {β : ℕ → ℝ} {τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} {ε ζ : ℕ → ℝ} (O : Oracles β c r H s₁ τ Q ε ζ)
    (T : ℕ → ℝ) (sample : ℕ → Ω → Kernel S A) (n : ℕ) (ω : Ω) : Policy S A :=
  if Bank.calibrates T (fun j => StageAlgorithm.deposits β τ c H s₁ sample j ω) n
  then O.calibration (sample n ω) else O.exploitation n (sample n ω)

lemma sampled_risk {β : ℕ → ℝ} {τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} {ε ζ : ℕ → ℝ} (O : Oracles β c r H s₁ τ Q ε ζ)
    (T : ℕ → ℝ) (sample : ℕ → Ω → Kernel S A) (n : ℕ) (ω : Ω) (hs : sample n ω ∈ Q) :
    (Bank.calibrates T (fun j => StageAlgorithm.deposits β τ c H s₁ sample j ω) n →
      risk β c (selected O T sample n ω) (sample n ω) H 0 s₁ =
        τ - StageAlgorithm.deposits β τ c H s₁ sample (n+1) ω) ∧
    (¬ Bank.calibrates T (fun j => StageAlgorithm.deposits β τ c H s₁ sample j ω) n →
      risk β c (selected O T sample n ω) (sample n ω) H 0 s₁ ≤ τ + ε n) := by
  constructor
  · intro hn
    rw [selected, if_pos hn, O.cal_exact _ hs]
    simp only [StageAlgorithm.deposits]
    ring
  · intro hn
    rw [selected, if_neg hn]
    exact O.exp_risk n _ hs

lemma sampled_reward {β : ℕ → ℝ} {τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} {ε ζ : ℕ → ℝ} (O : Oracles β c r H s₁ τ Q ε ζ)
    (exact : StageAlgorithm.Oracles β c r H s₁ τ Q)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (T : ℕ → ℝ) (sample : ℕ → Ω → Kernel S A) (n : ℕ) (ω : Ω) (hs : sample n ω ∈ Q) :
    (Bank.calibrates T (fun j => StageAlgorithm.deposits β τ c H s₁ sample j ω) n →
      constrainedValue β c r H s₁ τ (sample n ω) -
        reward r (selected O T sample n ω) (sample n ω) H 0 s₁ ≤ H) ∧
    (¬ Bank.calibrates T (fun j => StageAlgorithm.deposits β τ c H s₁ sample j ω) n →
      constrainedValue β c r H s₁ τ (sample n ω) -
        reward r (selected O T sample n ω) (sample n ω) H 0 s₁ ≤ ζ n) := by
  constructor
  · intro hn
    rw [selected, if_pos hn, constrainedValue_eq exact hs]
    have hu := (Algorithm.reward_bounds r hr (exact.exploitation (sample n ω)) (sample n ω) H 0 s₁).2
    have hl := (Algorithm.reward_bounds r hr (O.calibration (sample n ω)) (sample n ω) H 0 s₁).1
    linarith
  · intro hn
    rw [selected, if_neg hn]
    have hh := O.exp_reward n _ hs
    linarith

/-- The accumulated feasibility error is added once; exact calibration still cancels its slack. -/
theorem sampled_bank_cancellation {β : ℕ → ℝ} {τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} {ε ζ : ℕ → ℝ} (O : Oracles β c r H s₁ τ Q ε ζ)
    (hε : ∀ n, 0 ≤ ε n) (T : ℕ → ℝ) (sample : ℕ → Ω → Kernel S A)
    (ω : Ω) (hs : ∀ n, sample n ω ∈ Q) (K : ℕ) :
    (∑ n ∈ Finset.range K, (risk β c (selected O T sample n ω) (sample n ω) H 0 s₁ - τ)) ≤
      (∑ n ∈ Finset.range K, ε n) -
        Bank.bank T (fun j => StageAlgorithm.deposits β τ c H s₁ sample j ω) K := by
  apply Bank.sampled_debt_cancellation _ _ _ _ hε
  · intro n hn
    have hh := (sampled_risk O T sample n ω (hs n)).1 hn
    linarith
  · intro n hn
    have hh := (sampled_risk O T sample n ω (hs n)).2 hn
    linarith

/-- Certified optimization error is additive to the actual calibration episode cost. -/
theorem sampled_reward_total {β : ℕ → ℝ} {τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} {ε ζ : ℕ → ℝ} (O : Oracles β c r H s₁ τ Q ε ζ)
    (exact : StageAlgorithm.Oracles β c r H s₁ τ Q) (hζ : ∀ n, 0 ≤ ζ n)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (T : ℕ → ℝ) (sample : ℕ → Ω → Kernel S A) (ω : Ω)
    (hs : ∀ n, sample n ω ∈ Q) (K : ℕ) :
    (∑ n ∈ Finset.range K, (constrainedValue β c r H s₁ τ (sample n ω) -
      reward r (selected O T sample n ω) (sample n ω) H 0 s₁)) ≤
      H * (Bank.count T (fun j => StageAlgorithm.deposits β τ c H s₁ sample j ω) K : ℝ) +
        ∑ n ∈ Finset.range K, ζ n := by
  apply Bank.sampled_reward_shortfall _ _ _ _ _ hζ
  · intro n hn
    exact (sampled_reward O exact hr T sample n ω (hs n)).1 hn
  · intro n hn
    exact (sampled_reward O exact hr T sample n ω (hs n)).2 hn

end
end Paper36.StageApproximation

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

abbrev decode (m : Model) : Nested.Kernel S A := Measurability.regularKernel (P.decode m)
abbrev samples (k : ℕ) (ω : Ω) : Nested.Kernel S A := decode P (P.sampled k ω)
abbrev truth (ω : Ω) : Nested.Kernel S A := decode P (P.latent ω)
abbrev policy (k : ℕ) (ω : Ω) : Nested.Policy S A := Measurability.regularPolicy (P.policies ω k)
abbrev support : Set (Nested.Kernel S A) := (PosteriorAlgorithm.prior (μ := μ) (decode P) P.latent).support
abbrev actualPrior : Measure (Nested.Kernel S A) := PosteriorAlgorithm.prior (μ := μ) (decode P) P.latent
abbrev delta (β : ℕ → ℝ) (τ : ℝ) (c : ℕ → S → A → ℝ) : ℝ :=
  StageCalibration.uniformGap (actualPrior P) β c (H+1) s₀ τ
abbrev target (β : ℕ → ℝ) : ℕ → ℝ := StageCharging.stageTarget (S := S) (A := A) β (H+1)
abbrev deposit (β : ℕ → ℝ) (τ : ℝ) (c : ℕ → S → A → ℝ) :=
  StageAlgorithm.deposits β τ c (H+1) s₀ (samples P)
abbrev trueRisk (β : ℕ → ℝ) (c : ℕ → S → A → ℝ) (k : ℕ) (ω : Ω) :=
  StageAlgorithm.risk β c (policy P k ω) (truth P ω) (H+1) 0 s₀
abbrev sampledRisk (β : ℕ → ℝ) (c : ℕ → S → A → ℝ) (k : ℕ) (ω : Ω) :=
  StageAlgorithm.risk β c (policy P k ω) (samples P k ω) (H+1) 0 s₀
abbrev trueReward (r : ℕ → S → A → ℝ) (k : ℕ) (ω : Ω) :=
  Nested.reward r (policy P k ω) (truth P ω) (H+1) 0 s₀
abbrev sampledReward (r : ℕ → S → A → ℝ) (k : ℕ) (ω : Ω) :=
  Nested.reward r (policy P k ω) (samples P k ω) (H+1) 0 s₀
abbrev optimum (β : ℕ → ℝ) (τ : ℝ) (c r : ℕ → S → A → ℝ) (ω : Ω) :=
  constrainedValue β c r (H+1) s₀ τ (truth P ω)
abbrev sampledOptimum (β : ℕ → ℝ) (τ : ℝ) (c r : ℕ → S → A → ℝ) (k : ℕ) (ω : Ω) :=
  constrainedValue β c r (H+1) s₀ τ (samples P k ω)

def lowConstant (β : ℕ → ℝ) : ℝ :=
  2 * (Fintype.card S : ℝ) * (Fintype.card A : ℝ) * (H+1) * Weights.stagew β (H+1) + (H+1 : ℝ)/2

def riskEnvelope (β : ℕ → ℝ) (Δ : ℝ) : ℝ :=
  lowConstant (S := S) (A := A) (H := H) β + StageCharging.stageResidual (S := S) (A := A) β (H+1) Δ

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

lemma riskError_eq (β : ℕ → ℝ) (c : ℕ → S → A → ℝ) (k : ℕ) (ω : Ω) :
    P.stageRiskError β c k ω = trueRisk P β c k ω - sampledRisk P β c k ω := by
  simp only [PosteriorSystem.stageRiskError, trueRisk, sampledRisk, policy, truth, samples,
    decode, PosteriorSystem.sampledKernels, StageAlgorithm.risk, Measurability.of_regularPolicy, Measurability.of_regularKernel,
    P.latent_match]

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

lemma trueRisk_integrable (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1) (k : ℕ) :
    Integrable (trueRisk P β c k) μ := by
  have hi := Statistical.integrable_stageRisk (μ := μ) β hβ c hc (fun ω => P.policies ω k)
    E.latent (P.policy_mass_measurable k) P.true_mass_measurable (H+1) 0 s₀
  exact hi.congr (ae_of_all _ fun ω => by
    simp only [trueRisk, policy, truth, decode, PosteriorSystem.sampledKernels, StageAlgorithm.risk, Measurability.of_regularPolicy,
      Measurability.of_regularKernel, P.latent_match])

lemma sampledRisk_integrable (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1) (k : ℕ) :
    Integrable (sampledRisk P β c k) μ := by
  have hi := Statistical.integrable_stageRisk (μ := μ) β hβ c hc (fun ω => P.policies ω k)
    (fun ω => P.sampledKernels ω k) (P.policy_mass_measurable k)
    (P.sampled_mass_measurable k) (H+1) 0 s₀
  exact hi.congr (ae_of_all _ fun ω => by
    simp only [sampledRisk, policy, samples, decode, PosteriorSystem.sampledKernels,
      StageAlgorithm.risk, Measurability.of_regularPolicy, Measurability.of_regularKernel])

lemma trueReward_integrable (r : ℕ → S → A → ℝ) (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (k : ℕ) :
    Integrable (trueReward P r k) μ := by
  have hi := Measurability.integrable_reward μ r hr (fun ω => P.policies ω k) E.latent
    (P.policy_mass_measurable k) P.true_mass_measurable (H+1) 0 s₀
  exact hi.congr (ae_of_all _ (fun ω => by simp only [Measurability.reward, P.latent_match]))

lemma sampledReward_integrable (r : ℕ → S → A → ℝ) (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (k : ℕ) :
    Integrable (sampledReward P r k) μ :=
  Measurability.integrable_reward μ r hr (fun ω => P.policies ω k) (fun ω => P.sampledKernels ω k)
    (P.policy_mass_measurable k) (P.sampled_mass_measurable k) (H+1) 0 s₀

lemma optimum_integrable {β : ℕ → ℝ} {τ : ℝ} {c r : ℕ → S → A → ℝ}
    (O : StageAlgorithm.BorelOracles β c r (H+1) s₀ τ (support P))
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) : Integrable (optimum P β τ c r) μ := by
  apply (StageAlgorithm.integrable_comparator μ O hr (truth P) (truth_measurable P)).congr
  filter_upwards [support_ae P] with ω hω
  exact StageAlgorithm.comparator_eq_source O hω.1

lemma sampledOptimum_integrable {β : ℕ → ℝ} {τ : ℝ} {c r : ℕ → S → A → ℝ}
    (O : StageAlgorithm.BorelOracles β c r (H+1) s₀ τ (support P))
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (k : ℕ) :
    Integrable (sampledOptimum P β τ c r k) μ := by
  apply (StageAlgorithm.integrable_comparator μ O hr (samples P k) (samples_measurable P k)).congr
  filter_upwards [support_ae P] with ω hω
  exact StageAlgorithm.comparator_eq_source O (hω.2 k)

/-- Equation (5.18) for the actual constrained optimum, without a symmetry premise. -/
lemma comparator_symmetry {β : ℕ → ℝ} {τ : ℝ} {c r : ℕ → S → A → ℝ}
    (O : StageAlgorithm.BorelOracles β c r (H+1) s₀ τ (support P))
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (K : ℕ) :
    (∫ ω, Assembly.total (fun k ω => optimum P β τ c r ω - sampledOptimum P β τ c r k ω) K ω ∂μ) = 0 := by
  rw [show (∫ ω, Assembly.total (fun k ω => optimum P β τ c r ω - sampledOptimum P β τ c r k ω) K ω ∂μ) =
      ∑ k ∈ Finset.range K, ∫ ω, optimum P β τ c r ω - sampledOptimum P β τ c r k ω ∂μ from
    integral_finset_sum _ (fun k _ => (optimum_integrable P O hr).sub (sampledOptimum_integrable P O hr k))]
  apply Finset.sum_eq_zero
  intro k _
  exact StageAlgorithm.comparator_symmetry _ (decode_measurable P) _ _ P.latent_meas
    (P.sampled_meas k) _ (P.history_meas k) (P.posterior k) O hr
    (by filter_upwards [support_ae P] with ω hω; exact ⟨hω.1, hω.2 k⟩)

/-- The actual statistical theorem supplies the expectation input to the bank proof. -/
lemma modelRisk_bound (external : RowTapes.ExternalCategoricalConcentration (S := S))
    (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1) (c : ℕ → S → A → ℝ)
    (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1) {K : ℕ} (hK : 1 ≤ K) :
    (∫ ω, Assembly.total (fun k ω => trueRisk P β c k ω - sampledRisk P β c k ω) K ω ∂μ) ≤
      Target.confidence (Target.scale (Real.sqrt (Weights.stageWsq β (H+1))) (Fintype.card S) (Fintype.card A))
        (Fintype.card S) (Fintype.card A) (H+1) K * Real.sqrt (K : ℝ) +
          lowConstant (S := S) (A := A) (H := H) β := by
  have hs := PosteriorSystem.stage_lemma_5_5 E P external β hβ c hc hK
  rw [show (∫ ω, Assembly.total (fun k ω => trueRisk P β c k ω - sampledRisk P β c k ω) K ω ∂μ) =
      ∑ k ∈ Finset.range K, ∫ ω, P.stageRiskError β c k ω ∂μ from by
    simp_rw [← riskError_eq P β c]
    exact integral_finset_sum _ (fun k _ => P.stageRiskError_integrable β hβ c hc k)]
  simpa only [lowConstant, Nat.cast_add, Nat.cast_one] using hs

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
    {K : ℕ} (hK : 1 ≤ K) :
    ((∫ ω, Assembly.total (fun n ω => trueRisk P β c n ω - τ) K ω ∂μ) ≤
      riskEnvelope (S := S) (A := A) (H := H) β (delta P β τ c) + ∑ n ∈ Finset.range K, ε n) ∧
    ((∫ ω, Assembly.total (fun n ω => optimum P β τ c r ω - trueReward P r n ω) K ω ∂μ) ≤
      rewardAllowance (S := S) (A := A) (H := H) K + (H+1 : ℝ) *
        ((target (S := S) (A := A) (H := H) β K + τ) / delta P β τ c) + ∑ n ∈ Finset.range K, ζ n) ∧
    ((∫ ω, Assembly.countRV (target (S := S) (A := A) (H := H) β) (deposit P β τ c) K ω ∂μ) ≤
      min (K : ℝ) ((target (S := S) (A := A) (H := H) β K + τ) / delta P β τ c)) := by
  letI : IsProbabilityMeasure (actualPrior P) :=
    Measure.isProbabilityMeasure_map ((decode_measurable P).comp P.latent_meas).aemeasurable
  have hg := StageAlgorithm.induced_gap_parameters (actualPrior P) β hβ τ c hc (H+1) s₀ hstrict
  have hdim := SourceBank.dimensions (A := A) s₀ (show 1 ≤ H+1 by omega)
  have hd := StageAlgorithm.measurable_deposits β hβ τ c hc (H+1) s₀ (samples P) (samples_measurable P)
  have hdep : ∀ᵐ ω ∂μ, Assembly.DepositBounds (target (S := S) (A := A) (H := H) β)
      (deposit P β τ c) (delta P β τ c) τ ω := by
    filter_upwards [support_ae P] with ω hω
    exact fun n _ => StageAlgorithm.actual_deposit_bounds (actualPrior P) β hβ τ c hc
      (H+1) s₀ hstrict (samples P) ω hω.2 n
  simpa only [riskEnvelope, StageCharging.stageResidual, target, StageCharging.stageTarget, Nat.cast_add, Nat.cast_one] using
    Assembly.conditional_main_bounds (D := lowConstant (S := S) (A := A) (H := H) β)
      (Q := rewardAllowance (S := S) (A := A) (H := H) K) (deposit P β τ c) (trueRisk P β c) (sampledRisk P β c)
    (fun _ => optimum P β τ c r) (sampledOptimum P β τ c r) (trueReward P r) (sampledReward P r)
    ε ζ K hK hdim.1 hdim.2.1 hdim.2.2 (Real.sqrt_nonneg (Weights.stageWsq β (H+1))) hg.1 hg.2 hd hdep
    (trueRisk_integrable P β hβ c hc) (sampledRisk_integrable P β hβ c hc)
    (fun _ => optimum_integrable P O hr) (sampledOptimum_integrable P O hr)
    (trueReward_integrable P r hr) (sampledReward_integrable P r hr) hε hζ hriskOracle (by simpa only [target, StageCharging.stageTarget, Nat.cast_add, Nat.cast_one] using hrewardOracle)
    (by simpa only [Nat.cast_add, Nat.cast_one] using modelRisk_bound P external β hβ c hc hK)
    (modelReward_bound P external r hr hK)
    (comparator_symmetry P O hr K)

/-- Theorem 4.2, (4.10)--(4.11), for actual Algorithm 1. The induced gap is a
function of the original arbitrary prior. The execution rule itself has no K or
gap argument. The exact H=1 strengthening is in SourceEndpoints. -/
theorem theorem_4_2
    (external : RowTapes.ExternalCategoricalConcentration (S := S))
    (β : ℕ → ℝ) (τ : ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1) (hτ : 0 ≤ τ)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (hstrict : ∀ q ∈ support P, ∃ π : Simulation.Policy S A,
      StageRisk.risk β c π (RiskBridge.ofKernel q) (H+1) 0 s₀ < τ)
    (O : StageAlgorithm.BorelOracles β c r (H+1) s₀ τ (support P))
    (hrun : ∀ n ω, policy P n ω = StageAlgorithm.selected O.toOracles
      (target (S := S) (A := A) (H := H) β) (samples P) n ω) :
    ∀ K, 1 ≤ K →
    ((∫ ω, Assembly.total (fun n ω => trueRisk P β c n ω - τ) K ω ∂μ) ≤
      riskEnvelope (S := S) (A := A) (H := H) β (delta P β τ c)) ∧
    ((∫ ω, Assembly.total (fun n ω => optimum P β τ c r ω - trueReward P r n ω) K ω ∂μ) ≤
      rewardAllowance (S := S) (A := A) (H := H) K + (H+1 : ℝ) *
        ((target (S := S) (A := A) (H := H) β K + τ) / delta P β τ c)) ∧
    ((∫ ω, Assembly.countRV (target (S := S) (A := A) (H := H) β) (deposit P β τ c) K ω ∂μ) ≤
      min (K : ℝ) ((target (S := S) (A := A) (H := H) β K + τ) / delta P β τ c)) := by
  intro K hK
  have hro : ∀ᵐ ω ∂μ, ∀ n,
      (Bank.calibrates (target (S := S) (A := A) (H := H) β) (fun j => deposit P β τ c j ω) n →
        sampledRisk P β c n ω = τ - deposit P β τ c (n+1) ω) ∧
      (¬Bank.calibrates (target (S := S) (A := A) (H := H) β) (fun j => deposit P β τ c j ω) n →
        sampledRisk P β c n ω ≤ τ + 0) := by
    filter_upwards [support_ae P] with ω hω
    intro n
    have hh := StageAlgorithm.selected_sampled_risk O.toOracles
      (target (S := S) (A := A) (H := H) β) (samples P) n ω (hω.2 n)
    simpa only [sampledRisk, hrun, add_zero] using hh
  have hwo : ∀ᵐ ω ∂μ, ∀ n,
      (Bank.calibrates (target (S := S) (A := A) (H := H) β) (fun j => deposit P β τ c j ω) n →
        sampledOptimum P β τ c r n ω - sampledReward P r n ω ≤ (H+1 : ℝ)) ∧
      (¬Bank.calibrates (target (S := S) (A := A) (H := H) β) (fun j => deposit P β τ c j ω) n →
        sampledOptimum P β τ c r n ω - sampledReward P r n ω ≤ 0) := by
    filter_upwards [support_ae P] with ω hω
    intro n
    have hh := StageAlgorithm.selected_sampled_reward O.toOracles hr
      (target (S := S) (A := A) (H := H) β) (samples P) n ω (hω.2 n)
    simp only [sampledOptimum, sampledReward, hrun]
    exact ⟨by simpa only [Nat.cast_add, Nat.cast_one] using hh.1, fun hn => (hh.2 hn).le⟩
  simpa only [Finset.sum_const_zero, add_zero] using
    certified_performance P external β τ hβ hτ c r hc hr hstrict O
      (fun _ => 0) (fun _ => 0) (fun _ => le_rfl) (fun _ => le_rfl) hro hwo hK

/-- (4.12) and almost-sure sparsity on one common event, simultaneously for all K. -/
theorem pathwise_calibration
    (β : ℕ → ℝ) (τ : ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1) (hτ : 0 ≤ τ)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hstrict : ∀ q ∈ support P, ∃ π : Simulation.Policy S A,
      StageRisk.risk β c π (RiskBridge.ofKernel q) (H+1) 0 s₀ < τ) :
    0 < delta P β τ c ∧
    ∀ᵐ ω ∂μ,
      (∀ K, (Bank.count (target (S := S) (A := A) (H := H) β)
        (fun j => deposit P β τ c j ω) K : ℝ) ≤
        min (K : ℝ) ((target (S := S) (A := A) (H := H) β K + τ) / delta P β τ c)) ∧
      Filter.Tendsto (fun K : ℕ =>
        (Bank.count (target (S := S) (A := A) (H := H) β)
          (fun j => deposit P β τ c j ω) K : ℝ) / (K : ℝ)) Filter.atTop (nhds 0) := by
  letI : IsProbabilityMeasure (actualPrior P) :=
    Measure.isProbabilityMeasure_map ((decode_measurable P).comp P.latent_meas).aemeasurable
  have hg := StageAlgorithm.induced_gap_parameters (actualPrior P) β hβ τ c hc (H+1) s₀ hstrict
  refine ⟨hg.1, ?_⟩
  filter_upwards [support_ae P] with ω hω
  exact ⟨fun K => StageAlgorithm.calibration_count (actualPrior P) β hβ τ c hc
      (H+1) s₀ hstrict (by omega) (samples P) ω hω.2 K,
    StageAlgorithm.calibration_sparse (actualPrior P) β hβ τ c hc
      (H+1) s₀ hstrict (by omega) (samples P) ω hω.2⟩

/-- Equation (5.12) with exactly the fixed (K,delta) probability from (5.11).
The event concerns the same true nested-risk values and actual observed bank. -/
theorem risk_bank_certificate
    (external : RowTapes.ExternalCategoricalConcentration (S := S))
    (β : ℕ → ℝ) (τ : ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (O : StageAlgorithm.BorelOracles β c r (H+1) s₀ τ (support P))
    (hrun : ∀ n ω, policy P n ω = StageAlgorithm.selected O.toOracles
      (target (S := S) (A := A) (H := H) β) (samples P) n ω)
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (hinfo : ∀ k, MeasurableSpace.comap (E.info k) inferInstance = ℱ k)
    (hpath : ∀ k, Measurable[ℱ (k+1), inferInstance] (E.path k))
    {K : ℕ} (hK : 1 ≤ K) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    μ.real {ω | Bounds.certificate (Fintype.card S) (Fintype.card A) (H+1)
        (Real.sqrt (Weights.stageWsq β (H+1))) (Weights.stagew β (H+1)) δ K -
          Bank.bank (target (S := S) (A := A) (H := H) β) (fun j => deposit P β τ c j ω) K <
        Assembly.total (fun n ω => trueRisk P β c n ω - τ) K ω} ≤ δ := by
  have hstat := PosteriorSystem.stage_theorem_5_6 E P external β hβ c hc ℱ hinfo hpath hK hδ hδ1
  have hsubset : {ω | Bounds.certificate (Fintype.card S) (Fintype.card A) (H+1)
        (Real.sqrt (Weights.stageWsq β (H+1))) (Weights.stagew β (H+1)) δ K -
          Bank.bank (target (S := S) (A := A) (H := H) β) (fun j => deposit P β τ c j ω) K <
        Assembly.total (fun n ω => trueRisk P β c n ω - τ) K ω} ≤ᵐ[μ]
      {ω | Bounds.certificate (Fintype.card S) (Fintype.card A) (H+1)
        (Real.sqrt (Weights.stageWsq β (H+1))) (Weights.stagew β (H+1)) δ K < ∑ k ∈ Finset.range K, P.stageRiskError β c k ω} := by
    filter_upwards [support_ae P] with ω hω
    intro herr
    have hb := StageAlgorithm.risk_bank_certificate_path O.toOracles
      (target (S := S) (A := A) (H := H) β) (samples P) (truth P) ω hω.2 K
      (∑ n ∈ Finset.range K, (trueRisk P β c n ω - sampledRisk P β c n ω)) (by simp only [← hrun]; exact le_rfl)
    simp only [← hrun] at hb
    have he : (∑ n ∈ Finset.range K, (trueRisk P β c n ω - sampledRisk P β c n ω)) =
        ∑ n ∈ Finset.range K, P.stageRiskError β c n ω := by
      apply Finset.sum_congr rfl
      intro n _
      exact (riskError_eq P β c n ω).symm
    change _ < _ at herr ⊢
    change Assembly.total (fun n ω => trueRisk P β c n ω - τ) K ω ≤ _ at hb
    rw [he] at hb
    linarith
  exact (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsubset)).trans hstat

/-- Corollary B.1 for the actual approximate execution rule. Its errors are
one-call deterministic certificates, and appear once in the cumulative result. -/
theorem corollary_B_1
    (external : RowTapes.ExternalCategoricalConcentration (S := S))
    (β : ℕ → ℝ) (τ : ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1) (hτ : 0 ≤ τ)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (hstrict : ∀ q ∈ support P, ∃ π : Simulation.Policy S A,
      StageRisk.risk β c π (RiskBridge.ofKernel q) (H+1) 0 s₀ < τ)
    (O : StageAlgorithm.BorelOracles β c r (H+1) s₀ τ (support P))
    (ε ζ : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hζ : ∀ n, 0 ≤ ζ n)
    (O' : StageApproximation.Oracles β c r (H+1) s₀ τ (support P) ε ζ)
    (hrun : ∀ n ω, policy P n ω = StageApproximation.selected O'
      (target (S := S) (A := A) (H := H) β) (samples P) n ω) :
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
  · filter_upwards [support_ae P] with ω hω
    intro n
    simpa only [sampledRisk, hrun] using
      StageApproximation.sampled_risk O' (target (S := S) (A := A) (H := H) β) (samples P) n ω (hω.2 n)
  · filter_upwards [support_ae P] with ω hω
    intro n
    simpa only [sampledOptimum, sampledReward, hrun, Nat.cast_add, Nat.cast_one] using
      StageApproximation.sampled_reward O' O.toOracles hr (target (S := S) (A := A) (H := H) β)
        (samples P) n ω (hω.2 n)
  · exact hK

end
end Paper36.StageMain
