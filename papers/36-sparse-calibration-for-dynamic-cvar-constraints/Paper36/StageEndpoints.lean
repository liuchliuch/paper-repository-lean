import Paper36.StageMain

/-! The H=1 strengthening for the actual B.3 algorithm. The single risk mass
is β(1); transition models disappear from both risk and reward. No concentration
inequality or finite-prior restriction is used in these endpoint theorems. -/
namespace Paper36.StageEndpoints
open MeasureTheory Paper36.Regularity Paper36.Nested Paper36.StageAlgorithm
open scoped BigOperators
noncomputable section
variable {S A Ω : Type*} [Fintype S] [Fintype A] [Nonempty A]

@[simp] lemma stageWsq_one (β : ℕ → ℝ) : Weights.stageWsq β 1 = 0 := by
  simp [Weights.stageWsq]

@[simp] lemma stagew_one (β : ℕ → ℝ) : Weights.stagew β 1 = 0 := by
  simp [Weights.stagew, Weights.stageLowTerm]

@[simp] lemma horizon_one_target (β : ℕ → ℝ) :
    StageCharging.stageTarget (S := S) (A := A) β 1 = fun _ => 0 := by
  funext K
  simp [StageCharging.stageTarget, BankTarget.paperTarget]

/-- The one-stage actual risk is exactly the compact model at its actual mass β(h+1). -/
lemma one_stage_risk_eq_nested (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (π : Nested.Policy S A) (q : Nested.Kernel S A) (h : ℕ) (s : S) :
    StageAlgorithm.risk β c π q 1 h s = Nested.risk (β (h+1)) c π q 1 h s := by
  change Simulation.risk (β (h+1)) c (RiskBridge.ofPolicy π) (RiskBridge.ofKernel q) 1 h s = _
  exact RiskBridge.risk_eq_nested (β (h+1)) (hβ (h+1)).1 (hβ (h+1)).2 c hc π q 1 h s

lemma one_stage_model_independent (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (π : Nested.Policy S A) (p q : Nested.Kernel S A) (h : ℕ) (s : S) :
    StageAlgorithm.risk β c π p 1 h s = StageAlgorithm.risk β c π q 1 h s ∧
      Nested.reward r π p 1 h s = Nested.reward r π q 1 h s := by
  simp only [one_stage_risk_eq_nested β hβ c hc]
  exact Endpoints.one_stage_model_independent (β (h+1)) c r π p q h s

lemma selected_one {β : ℕ → ℝ} {τ : ℝ} {c r : ℕ → S → A → ℝ} {s₁ : S}
    {Q : Set (Kernel S A)} (O : Oracles β c r 1 s₁ τ Q)
    (sample : ℕ → Ω → Kernel S A) (n : ℕ) (ω : Ω) :
    selected O (StageCharging.stageTarget (S := S) (A := A) β 1) sample n ω =
      O.exploitation (sample n ω) := by
  rw [horizon_one_target]
  unfold selected Bank.calibrates
  simp only [(Bank.zero_target (fun j => deposits β τ c 1 s₁ sample j ω) n).1,
    lt_self_iff_false, if_false]

/-- The actual exact source execution is feasible and has zero regret on every support path. -/
theorem horizon_one_path {β : ℕ → ℝ} (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    {τ : ℝ} {c r : ℕ → S → A → ℝ} (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    {s₁ : S} {Q : Set (Kernel S A)} (O : Oracles β c r 1 s₁ τ Q)
    (sample : ℕ → Ω → Kernel S A) (latent : Ω → Kernel S A) (ω : Ω)
    (hlatent : latent ω ∈ Q) (hsample : ∀ n, sample n ω ∈ Q) (K : ℕ) :
    (∑ n ∈ Finset.range K,
      (risk β c (selected O (StageCharging.stageTarget (S := S) (A := A) β 1) sample n ω)
        (latent ω) 1 0 s₁ - τ)) ≤ 0 ∧
    (∑ n ∈ Finset.range K,
      (constrainedValue β c r 1 s₁ τ (latent ω) -
        reward r (selected O (StageCharging.stageTarget (S := S) (A := A) β 1) sample n ω)
          (latent ω) 1 0 s₁)) = 0 := by
  simp_rw [selected_one]
  rw [constrainedValue_eq O hlatent]
  constructor
  · apply Finset.sum_nonpos
    intro n _
    have hm := (one_stage_model_independent β hβ c r hc
      (O.exploitation (sample n ω)) (latent ω) (sample n ω) 0 s₁).1
    have hf := O.exp_feasible _ (hsample n)
    rw [← hm] at hf
    exact sub_nonpos.mpr hf
  · apply Finset.sum_eq_zero
    intro n _
    have hmπ := one_stage_model_independent β hβ c r hc
      (O.exploitation (sample n ω)) (latent ω) (sample n ω) 0 s₁
    have hmC := one_stage_model_independent β hβ c r hc
      (O.exploitation (latent ω)) (latent ω) (sample n ω) 0 s₁
    have hlo := O.exp_optimal _ hlatent (O.exploitation (sample n ω))
      (by rw [hmπ.1]; exact O.exp_feasible _ (hsample n))
    have hhi := O.exp_optimal _ (hsample n) (O.exploitation (latent ω))
      (by rw [← hmC.1]; exact O.exp_feasible _ hlatent)
    rw [← hmC.2, ← hmπ.2] at hhi
    exact sub_eq_zero.mpr (le_antisymm hhi hlo)

/-- The one-stage exact endpoint on any probability space and any prior. -/
theorem horizon_one_any_prior [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {β : ℕ → ℝ} (hβ : ∀ j, 0 < β j ∧ β j ≤ 1) {τ : ℝ}
    {c r : ℕ → S → A → ℝ} (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    {s₁ : S} {Q : Set (Kernel S A)} (O : Oracles β c r 1 s₁ τ Q)
    (sample : ℕ → Ω → Kernel S A) (latent : Ω → Kernel S A)
    (hsupport : ∀ᵐ ω ∂μ, latent ω ∈ Q ∧ ∀ n, sample n ω ∈ Q) (K : ℕ) :
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
  refine ⟨?_, ?_, ?_⟩
  · apply integral_nonpos_of_ae
    filter_upwards [hsupport] with ω hω
    exact (horizon_one_path hβ hc O sample latent ω hω.1 hω.2 K).1
  · have hz : (fun ω => ∑ n ∈ Finset.range K,
        (constrainedValue β c r 1 s₁ τ (latent ω) -
          reward r (selected O (StageCharging.stageTarget (S := S) (A := A) β 1) sample n ω)
            (latent ω) 1 0 s₁)) =ᵐ[μ] (fun _ => 0) := by
      filter_upwards [hsupport] with ω hω
      exact (horizon_one_path hβ hc O sample latent ω hω.1 hω.2 K).2
    rw [integral_congr_ae hz, integral_zero]
  · intro ω
    rw [horizon_one_target]
    exact Bank.zero_target _ K

/-- The literal fixed-pair certificate vanishes, for every δ and K, at H=1. -/
@[simp] lemma horizon_one_certificate (β : ℕ → ℝ) (s a δ : ℝ) (K : ℕ) :
    Bounds.certificate s a 1 (Real.sqrt (Weights.stageWsq β 1)) (Weights.stagew β 1) δ K = 0 := by
  simp [Bounds.certificate]

/-- One-stage certified exploitation transfers to the true model without a
transition-model error term, at the actual risk mass β(h+1). -/
theorem one_stage_approximate_oracles (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (τ : ℝ) (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (p : Kernel S A) (q : ℕ → Kernel S A) (π : ℕ → Policy S A) (comparator : Policy S A)
    (h : ℕ) (s : S) (ε ζ : ℕ → ℝ)
    (hcf : StageAlgorithm.risk β c comparator p 1 h s ≤ τ)
    (hπf : ∀ n, StageAlgorithm.risk β c (π n) (q n) 1 h s ≤ τ + ε n)
    (hπo : ∀ n π', StageAlgorithm.risk β c π' (q n) 1 h s ≤ τ →
      Nested.reward r π' (q n) 1 h s ≤ Nested.reward r (π n) (q n) 1 h s + ζ n)
    (K : ℕ) :
    (∑ n ∈ Finset.range K, (StageAlgorithm.risk β c (π n) p 1 h s - τ)) ≤
      (∑ n ∈ Finset.range K, ε n) ∧
    (∑ n ∈ Finset.range K, (Nested.reward r comparator p 1 h s -
      Nested.reward r (π n) p 1 h s)) ≤ (∑ n ∈ Finset.range K, ζ n) := by
  simp only [one_stage_risk_eq_nested β hβ c hc] at hcf hπf hπo ⊢
  exact Endpoints.one_stage_approximate_oracles (β (h+1)) τ c r p q π comparator h s ε ζ hcf hπf hπo K

end
end Paper36.StageEndpoints

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

/-- The H=1 clause in Theorem 4.2 for the same arbitrary prior and protocol. -/
theorem theorem_4_2_horizon_one
    (β : ℕ → ℝ) (τ : ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (O : StageAlgorithm.BorelOracles β c r 1 s₀ τ (support P))
    (hrun : ∀ n ω, policy P n ω = StageAlgorithm.selected O.toOracles
      (target (S := S) (A := A) (H := 0) β) (samples P) n ω) (K : ℕ) :
    ((∫ ω, Assembly.total (fun n ω => trueRisk P β c n ω - τ) K ω ∂μ) ≤ 0) ∧
    ((∫ ω, Assembly.total (fun n ω => optimum P β τ c r ω - trueReward P r n ω) K ω ∂μ) = 0) ∧
    (∀ ω, Bank.bank (target (S := S) (A := A) (H := 0) β) (fun j => deposit P β τ c j ω) K = 0 ∧
      Bank.count (target (S := S) (A := A) (H := 0) β) (fun j => deposit P β τ c j ω) K = 0) := by
  have hh := StageEndpoints.horizon_one_any_prior μ hβ hc O.toOracles (samples P) (truth P) (support_ae P) K
  simpa only [Assembly.total, trueRisk, trueReward, optimum, ← hrun] using hh

lemma approximate_selected_one {β : ℕ → ℝ} {τ : ℝ} {c r : ℕ → S → A → ℝ} {ε ζ : ℕ → ℝ}
    (O' : StageApproximation.Oracles β c r 1 s₀ τ (support P) ε ζ) (n : ℕ) (ω : Ω) :
    StageApproximation.selected O' (target (S := S) (A := A) (H := 0) β) (samples P) n ω =
      O'.exploitation n (samples P n ω) := by
  unfold target
  rw [StageEndpoints.horizon_one_target]
  unfold StageApproximation.selected Bank.calibrates
  simp only [(Bank.zero_target (fun j => deposits β τ c 1 s₀ (samples P) j ω) n).1,
    lt_self_iff_false, if_false]

/-- The H=1 clause of Corollary B.1. No transition concentration is needed. -/
theorem corollary_B_1_horizon_one
    (β : ℕ → ℝ) (τ : ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (O : StageAlgorithm.BorelOracles β c r 1 s₀ τ (support P))
    (ε ζ : ℕ → ℝ)
    (O' : StageApproximation.Oracles β c r 1 s₀ τ (support P) ε ζ)
    (hrun : ∀ n ω, policy P n ω = StageApproximation.selected O'
      (target (S := S) (A := A) (H := 0) β) (samples P) n ω) (K : ℕ) :
    ((∫ ω, Assembly.total (fun n ω => trueRisk P β c n ω - τ) K ω ∂μ) ≤ ∑ n ∈ Finset.range K, ε n) ∧
    ((∫ ω, Assembly.total (fun n ω => optimum P β τ c r ω - trueReward P r n ω) K ω ∂μ) ≤
      ∑ n ∈ Finset.range K, ζ n) := by
  have hpaths : ∀ᵐ ω ∂μ,
      Assembly.total (fun n ω => trueRisk P β c n ω - τ) K ω ≤ ∑ n ∈ Finset.range K, ε n ∧
      Assembly.total (fun n ω => optimum P β τ c r ω - trueReward P r n ω) K ω ≤ ∑ n ∈ Finset.range K, ζ n := by
    filter_upwards [support_ae P] with ω hω
    have hselected (n : ℕ) : policy P n ω = O'.exploitation n (samples P n ω) :=
      (hrun n ω).trans (approximate_selected_one P O' n ω)
    have hh := StageEndpoints.one_stage_approximate_oracles β hβ τ c r hc (truth P ω) (fun n => samples P n ω)
      (fun n => policy P n ω) (O.exploitation (truth P ω)) 0 s₀ ε ζ
      (O.exp_feasible _ hω.1)
      (fun n => by
        change StageAlgorithm.risk β c (policy P n ω) (samples P n ω) 1 0 s₀ ≤ τ + ε n
        rw [hselected]; exact O'.exp_risk n _ (hω.2 n))
      (fun n π hf => by
        have hv := O'.exp_reward n _ (hω.2 n)
        have ho := O.exp_optimal _ (hω.2 n) π hf
        rw [constrainedValue_eq O.toOracles (hω.2 n)] at hv
        change reward r π (samples P n ω) 1 0 s₀ ≤ reward r (policy P n ω) (samples P n ω) 1 0 s₀ + ζ n
        rw [hselected]
        exact ho.trans hv) K
    simpa only [Assembly.total, trueRisk, trueReward, optimum, constrainedValue_eq O.toOracles hω.1] using hh
  constructor
  · have hi := Assembly.integrable_total (fun n ω => trueRisk P β c n ω - τ)
      (fun n => (trueRisk_integrable P β hβ c hc n).sub (integrable_const τ)) K
    have hh := integral_mono_ae hi (integrable_const (∑ n ∈ Finset.range K, ε n)) (hpaths.mono (fun _ h => h.1))
    simpa only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] using hh
  · have hi := Assembly.integrable_total (fun n ω => optimum P β τ c r ω - trueReward P r n ω)
      (fun n => (optimum_integrable P O hr).sub (trueReward_integrable P r hr n)) K
    have hh := integral_mono_ae hi (integrable_const (∑ n ∈ Finset.range K, ζ n)) (hpaths.mono (fun _ h => h.2))
    simpa only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] using hh

/-- At H=1 the actual fixed-pair stage certificate has zero failure probability.
Its E_delta is literally zero, and its bank is literally zero. -/
theorem risk_bank_certificate_horizon_one
    (β : ℕ → ℝ) (τ : ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (O : StageAlgorithm.BorelOracles β c r 1 s₀ τ (support P))
    (hrun : ∀ n ω, policy P n ω = StageAlgorithm.selected O.toOracles
      (target (S := S) (A := A) (H := 0) β) (samples P) n ω) (δ : ℝ) (K : ℕ) :
    μ.real {ω | Bounds.certificate (Fintype.card S) (Fintype.card A) 1
        (Real.sqrt (Weights.stageWsq β 1)) (Weights.stagew β 1) δ K -
          Bank.bank (target (S := S) (A := A) (H := 0) β) (fun j => deposit P β τ c j ω) K <
        Assembly.total (fun n ω => trueRisk P β c n ω - τ) K ω} = 0 := by
  have hempty : {ω | Bounds.certificate (Fintype.card S) (Fintype.card A) 1
        (Real.sqrt (Weights.stageWsq β 1)) (Weights.stagew β 1) δ K -
          Bank.bank (target (S := S) (A := A) (H := 0) β) (fun j => deposit P β τ c j ω) K <
        Assembly.total (fun n ω => trueRisk P β c n ω - τ) K ω} =ᵐ[μ] (∅ : Set Ω) := by
    filter_upwards [support_ae P] with ω hω
    have hr : Assembly.total (fun n ω => trueRisk P β c n ω - τ) K ω ≤ 0 := by
      simpa only [Assembly.total, trueRisk, ← hrun] using
        (StageEndpoints.horizon_one_path hβ hc O.toOracles (samples P) (truth P) ω hω.1 hω.2 K).1
    have hb : Bank.bank (target (S := S) (A := A) (H := 0) β)
        (fun j => deposit P β τ c j ω) K = 0 := by
      rw [target, StageEndpoints.horizon_one_target]
      exact (Bank.zero_target _ K).1
    change ((_ - _ < _) = False)
    simp only [StageEndpoints.horizon_one_certificate, hb, sub_self, not_lt_of_ge hr]
  simp only [measureReal_def, measure_congr hempty, measure_empty, ENNReal.toReal_zero]

end
end Paper36.StageMain
