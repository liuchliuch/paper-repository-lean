import Paper36.StageCalibration
import Paper36.StageCharging
import Paper36.BorelAlgorithm
import Paper36.SourceBank
import Paper36.PosteriorAlgorithm

/-! B.3's actual algorithm: sampled minimum-risk DP deposits, the original
threshold rule, exact planning selectors, and the induced prior-support gap.
No cumulative risk/count/oracle-cancellation conclusion is an oracle field. -/
namespace Paper36.StageCharging
noncomputable section
variable {S A : Type*} [Fintype S] [Fintype A]

/-- The original target with precisely the B.3 high-count weight substituted. -/
def stageTarget (β : ℕ → ℝ) (H : ℕ) : ℕ → ℝ :=
  BankTarget.paperTarget (Fintype.card S) (Fintype.card A) H
    (Real.sqrt (Weights.stageWsq β H))

/-- The original explicit R_* with precisely the B.3 high-count weight. -/
def stageResidual (β : ℕ → ℝ) (H : ℕ) (Δ : ℝ) : ℝ :=
  BankTarget.paperResidual (Fintype.card S) (Fintype.card A) H
    (Real.sqrt (Weights.stageWsq β H)) Δ

theorem stage_target_properties [Nonempty A] (β : ℕ → ℝ) (H : ℕ) (s₁ : S)
    (hH : 1 ≤ H) {Δ : ℝ} (hΔ : 0 < Δ) :
    Monotone (stageTarget (S := S) (A := A) β H) ∧
      stageTarget (S := S) (A := A) β H 0 = 0 ∧
      (∀ j n, stageTarget (S := S) (A := A) β H (j+n) ≤
        stageTarget (S := S) (A := A) β H j + stageTarget (S := S) (A := A) β H n) ∧
      (∀ n, stageTarget (S := S) (A := A) β H n - (n : ℝ)*Δ ≤
        stageResidual (S := S) (A := A) β H Δ) ∧
      Filter.Tendsto (fun n : ℕ => stageTarget (S := S) (A := A) β H n / (n : ℝ))
        Filter.atTop (nhds 0) := by
  have hd := SourceBank.dimensions (A := A) s₁ hH
  exact BankTarget.actual_target_properties hd.1 hd.2.1 hd.2.2 (Real.sqrt_nonneg _) hΔ

end
end Paper36.StageCharging

namespace Paper36.StageAlgorithm
open Set MeasureTheory Paper36.Nested
open scoped BigOperators
noncomputable section
variable {S A Ω : Type*} [Fintype S] [Fintype A] [Nonempty A]

/-- The actual StageRisk recursion, expressed on the source's probability simplices. -/
def risk (β : ℕ → ℝ) (c : ℕ → S → A → ℝ) (π : Policy S A) (q : Kernel S A)
    (n h : ℕ) (s : S) : ℝ :=
  StageRisk.risk β c (RiskBridge.ofPolicy π) (RiskBridge.ofKernel q) n h s

def minimumRisk (β : ℕ → ℝ) (c : ℕ → S → A → ℝ) (H : ℕ) (s₁ : S)
    (q : Kernel S A) : ℝ := StageCalibration.dp β c (RiskBridge.ofKernel q) H 0 s₁

/-- Only the exact single-model planning specifications appear in the oracle contract. -/
structure Oracles (β : ℕ → ℝ) (c r : ℕ → S → A → ℝ) (H : ℕ) (s₁ : S)
    (τ : ℝ) (Q : Set (Kernel S A)) where
  calibration : Kernel S A → Policy S A
  exploitation : Kernel S A → Policy S A
  cal_exact : ∀ q ∈ Q, risk β c (calibration q) q H 0 s₁ = minimumRisk β c H s₁ q
  cal_deterministic : ∀ q ∈ Q, StageCalibration.Deterministic (RiskBridge.ofPolicy (calibration q))
  exp_feasible : ∀ q ∈ Q, risk β c (exploitation q) q H 0 s₁ ≤ τ
  exp_optimal : ∀ q ∈ Q, ∀ π, risk β c π q H 0 s₁ ≤ τ →
    Nested.reward r π q H 0 s₁ ≤ Nested.reward r (exploitation q) q H 0 s₁

/-- Borel selection is the published external selection ingredient in the exact
oracle protocol; measurability of the actual bank/decision is proved below. -/
structure BorelOracles (β : ℕ → ℝ) (c r : ℕ → S → A → ℝ) (H : ℕ) (s₁ : S)
    (τ : ℝ) (Q : Set (Kernel S A)) extends Oracles β c r H s₁ τ Q where
  measurable_calibration : Measurable calibration
  measurable_exploitation : Measurable exploitation

/-- The exact constrained value for the stage-dependent risk and source reward. -/
def constrainedValue (β : ℕ → ℝ) (c r : ℕ → S → A → ℝ) (H : ℕ) (s₁ : S)
    (τ : ℝ) (q : Kernel S A) : ℝ :=
  sSup {v | ∃ π : Policy S A, risk β c π q H 0 s₁ ≤ τ ∧ Nested.reward r π q H 0 s₁ = v}

lemma constrainedValue_eq {β : ℕ → ℝ} {τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} (O : Oracles β c r H s₁ τ Q) {q : Kernel S A} (hq : q ∈ Q) :
    constrainedValue β c r H s₁ τ q = Nested.reward r (O.exploitation q) q H 0 s₁ := by
  unfold constrainedValue
  have hne : {v | ∃ π : Policy S A, risk β c π q H 0 s₁ ≤ τ ∧ Nested.reward r π q H 0 s₁ = v}.Nonempty :=
    ⟨_, ⟨O.exploitation q, O.exp_feasible q hq, rfl⟩⟩
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt hne
  · rintro _ ⟨π, hf, rfl⟩
    exact O.exp_optimal q hq π hf
  · intro b hb
    exact ⟨_, ⟨O.exploitation q, O.exp_feasible q hq, rfl⟩, hb⟩

/-- Pointwise exact oracles are derived from the actual DP minimizer and compact
constrained optimizer, rather than supplied as conclusions of an algorithm theorem. -/
theorem exists_oracles (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1) (τ : ℝ)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1)
    (H : ℕ) (s₁ : S) (Q : Set (Kernel S A))
    (hstrict : ∀ q ∈ Q, ∃ π : Simulation.Policy S A,
      StageRisk.risk β c π (RiskBridge.ofKernel q) H 0 s₁ < τ) :
    Nonempty (Oracles β c r H s₁ τ Q) := by
  classical
  let calA : Kernel S A → Simulation.Policy S A := fun q =>
    Classical.choose (StageCalibration.exists_deterministic_minimizer β hβ c (RiskBridge.ofKernel q) H 0)
  let cal : Kernel S A → Policy S A := fun q => StageCalibration.toPolicy (calA q)
  have hcal (q : Kernel S A) : risk β c (cal q) q H 0 s₁ = minimumRisk β c H s₁ q := by
    unfold risk minimumRisk cal
    rw [StageCalibration.ofPolicy_toPolicy]
    exact (Classical.choose_spec
      (StageCalibration.exists_deterministic_minimizer β hβ c (RiskBridge.ofKernel q) H 0)).2 s₁
  have hdet (q : Kernel S A) : StageCalibration.Deterministic (RiskBridge.ofPolicy (cal q)) := by
    rw [show cal q = StageCalibration.toPolicy (calA q) by rfl, StageCalibration.ofPolicy_toPolicy]
    exact (Classical.choose_spec
      (StageCalibration.exists_deterministic_minimizer β hβ c (RiskBridge.ofKernel q) H 0)).1
  have hex (q : Kernel S A) (hq : q ∈ Q) : ∃ π : Policy S A,
      risk β c π q H 0 s₁ ≤ τ ∧ ∀ π', risk β c π' q H 0 s₁ ≤ τ →
        Nested.reward r π' q H 0 s₁ ≤ Nested.reward r π q H 0 s₁ := by
    apply StageCalibration.exists_constrained_optimum β hβ c r hc H 0 s₁ q τ
    refine ⟨cal q, ?_⟩
    change risk β c (cal q) q H 0 s₁ ≤ τ
    rw [hcal]
    obtain ⟨π₀, hπ₀⟩ := hstrict q hq
    exact (StageCalibration.dp_le_risk β hβ c (RiskBridge.ofKernel q) π₀ H 0 s₁).trans hπ₀.le
  let exploit : Kernel S A → Policy S A := fun q =>
    if hq : q ∈ Q then Classical.choose (hex q hq) else cal q
  refine ⟨⟨cal, exploit, fun q _ => hcal q, fun q _ => hdet q, ?_, ?_⟩⟩
  · intro q hq
    simp only [exploit, dif_pos hq]
    exact (Classical.choose_spec (hex q hq)).1
  · intro q hq π hf
    simp only [exploit, dif_pos hq]
    exact (Classical.choose_spec (hex q hq)).2 π hf

/-- Episode n supplies d(n+1); the bank ignores noncalibration slack. -/
def deposits (β : ℕ → ℝ) (τ : ℝ) (c : ℕ → S → A → ℝ) (H : ℕ) (s₁ : S)
    (sample : ℕ → Ω → Kernel S A) : ℕ → Ω → ℝ
  | 0, _ => 0
  | n+1, ω => τ - minimumRisk β c H s₁ (sample n ω)

/-- The actual threshold rule uses no terminal episode K and no induced gap. -/
def selected {β : ℕ → ℝ} {τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} (O : Oracles β c r H s₁ τ Q)
    (T : ℕ → ℝ) (sample : ℕ → Ω → Kernel S A) (n : ℕ) (ω : Ω) : Policy S A :=
  if Bank.calibrates T (fun j => deposits β τ c H s₁ sample j ω) n
  then O.calibration (sample n ω) else O.exploitation (sample n ω)

lemma selected_sampled_risk {β : ℕ → ℝ} {τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} (O : Oracles β c r H s₁ τ Q)
    (T : ℕ → ℝ) (sample : ℕ → Ω → Kernel S A) (n : ℕ) (ω : Ω)
    (hsample : sample n ω ∈ Q) :
    (Bank.calibrates T (fun j => deposits β τ c H s₁ sample j ω) n →
      risk β c (selected O T sample n ω) (sample n ω) H 0 s₁ =
        τ - deposits β τ c H s₁ sample (n+1) ω) ∧
    (¬Bank.calibrates T (fun j => deposits β τ c H s₁ sample j ω) n →
      risk β c (selected O T sample n ω) (sample n ω) H 0 s₁ ≤ τ) := by
  constructor
  · intro hn
    rw [selected, if_pos hn, O.cal_exact _ hsample]
    simp only [deposits]
    ring
  · intro hn
    simp only [selected, if_neg hn]
    exact O.exp_feasible _ hsample

lemma selected_sampled_reward {β : ℕ → ℝ} {τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} (O : Oracles β c r H s₁ τ Q)
    (hr : ∀ h s a, r h s a ∈ Icc 0 1)
    (T : ℕ → ℝ) (sample : ℕ → Ω → Kernel S A) (n : ℕ) (ω : Ω)
    (hsample : sample n ω ∈ Q) :
    (Bank.calibrates T (fun j => deposits β τ c H s₁ sample j ω) n →
      constrainedValue β c r H s₁ τ (sample n ω) -
        Nested.reward r (selected O T sample n ω) (sample n ω) H 0 s₁ ≤ H) ∧
    (¬Bank.calibrates T (fun j => deposits β τ c H s₁ sample j ω) n →
      constrainedValue β c r H s₁ τ (sample n ω) -
        Nested.reward r (selected O T sample n ω) (sample n ω) H 0 s₁ = 0) := by
  rw [constrainedValue_eq O hsample]
  constructor
  · intro hn
    simp only [selected, if_pos hn]
    have hu := (Algorithm.reward_bounds r hr (O.exploitation (sample n ω)) (sample n ω) H 0 s₁).2
    have hl := (Algorithm.reward_bounds r hr (O.calibration (sample n ω)) (sample n ω) H 0 s₁).1
    linarith
  · intro hn
    simp only [selected, if_neg hn, sub_self]

/-- Actual sampled-model risk debt cancels against the actual bank. -/
theorem sampled_risk_bank {β : ℕ → ℝ} {τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} (O : Oracles β c r H s₁ τ Q)
    (T : ℕ → ℝ) (sample : ℕ → Ω → Kernel S A) (ω : Ω)
    (hsample : ∀ n, sample n ω ∈ Q) (K : ℕ) :
    (∑ n ∈ Finset.range K, (risk β c (selected O T sample n ω) (sample n ω) H 0 s₁ - τ)) ≤
      -Bank.bank T (fun j => deposits β τ c H s₁ sample j ω) K := by
  apply Bank.exact_sampled_debt_cancellation
  · intro n hn
    have h := (selected_sampled_risk O T sample n ω (hsample n)).1 hn
    linarith
  · intro n hn
    exact sub_nonpos.mpr ((selected_sampled_risk O T sample n ω (hsample n)).2 hn)

/-- The exact sampled reward loss is controlled by the actual calibration count. -/
theorem sampled_reward_count {β : ℕ → ℝ} {τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} (O : Oracles β c r H s₁ τ Q)
    (hr : ∀ h s a, r h s a ∈ Icc 0 1) (T : ℕ → ℝ)
    (sample : ℕ → Ω → Kernel S A) (ω : Ω) (hsample : ∀ n, sample n ω ∈ Q) (K : ℕ) :
    (∑ n ∈ Finset.range K, (constrainedValue β c r H s₁ τ (sample n ω) -
      Nested.reward r (selected O T sample n ω) (sample n ω) H 0 s₁)) ≤
      (H : ℝ) * (Bank.count T (fun j => deposits β τ c H s₁ sample j ω) K : ℝ) := by
  simpa using Bank.sampled_reward_shortfall T (fun j => deposits β τ c H s₁ sample j ω)
    (fun n => constrainedValue β c r H s₁ τ (sample n ω) -
      Nested.reward r (selected O T sample n ω) (sample n ω) H 0 s₁) (fun _ => 0) H
    (fun _ => le_rfl) (fun n hn => (selected_sampled_reward O hr T sample n ω (hsample n)).1 hn)
    (fun n hn => ((selected_sampled_reward O hr T sample n ω (hsample n)).2 hn).le) K

/-- Exact debt cancellation on the realized stage-risk values. -/
theorem risk_bank_certificate_path {β : ℕ → ℝ} {τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} (O : Oracles β c r H s₁ τ Q)
    (T : ℕ → ℝ) (sample : ℕ → Ω → Kernel S A) (latent : Ω → Kernel S A) (ω : Ω)
    (hsample : ∀ n, sample n ω ∈ Q) (K : ℕ) (E : ℝ)
    (hmodel : (∑ n ∈ Finset.range K,
      (risk β c (selected O T sample n ω) (latent ω) H 0 s₁ -
        risk β c (selected O T sample n ω) (sample n ω) H 0 s₁)) ≤ E) :
    (∑ n ∈ Finset.range K, (risk β c (selected O T sample n ω) (latent ω) H 0 s₁ - τ)) ≤
      E - Bank.bank T (fun j => deposits β τ c H s₁ sample j ω) K := by
  have hb := sampled_risk_bank O T sample ω hsample K
  have heq : (∑ n ∈ Finset.range K, (risk β c (selected O T sample n ω) (latent ω) H 0 s₁ - τ)) =
      (∑ n ∈ Finset.range K, (risk β c (selected O T sample n ω) (latent ω) H 0 s₁ -
        risk β c (selected O T sample n ω) (sample n ω) H 0 s₁)) +
      (∑ n ∈ Finset.range K, (risk β c (selected O T sample n ω) (sample n ω) H 0 s₁ - τ)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  linarith

section Borel
variable [MeasurableSpace Ω]
local instance policyKernel_opens : OpensMeasurableSpace (Policy S A × Kernel S A) :=
  @Prod.opensMeasurableSpace _ _ _ _ _ _ inferInstance inferInstance inferInstance

lemma measurable_deposits (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1) (τ : ℝ)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1) (H : ℕ) (s₁ : S)
    (sample : ℕ → Ω → Kernel S A) (hsample : ∀ n, Measurable (sample n)) (n : ℕ) :
    Measurable (deposits β τ c H s₁ sample n) := by
  cases n with
  | zero => exact measurable_const
  | succ n =>
    exact measurable_const.sub ((StageCalibration.continuous_dp β hβ c hc H 0 s₁).measurable.comp (hsample n))

theorem measurable_selected {β : ℕ → ℝ} {τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} (O : BorelOracles β c r H s₁ τ Q)
    (hβ : ∀ j, 0 < β j ∧ β j ≤ 1) (hc : ∀ h s a, c h s a ∈ Icc 0 1)
    (T : ℕ → ℝ) (sample : ℕ → Ω → Kernel S A) (hsample : ∀ n, Measurable (sample n))
    (n : ℕ) : Measurable (fun ω => selected O.toOracles T sample n ω) := by
  have hd := measurable_deposits β hβ τ c hc H s₁ sample hsample
  have hset : MeasurableSet {ω | Bank.calibrates T (fun j => deposits β τ c H s₁ sample j ω) n} :=
    measurableSet_lt (Assembly.measurable_bank T _ hd n) measurable_const
  exact Measurable.ite hset (O.measurable_calibration.comp (hsample n))
    (O.measurable_exploitation.comp (hsample n))

/-- A Borel version of the source's constrained comparator. -/
def comparator {β : ℕ → ℝ} {τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} (O : BorelOracles β c r H s₁ τ Q) (q : Kernel S A) : ℝ :=
  Nested.reward r (O.exploitation q) q H 0 s₁

lemma measurable_comparator {β : ℕ → ℝ} {τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} (O : BorelOracles β c r H s₁ τ Q) : Measurable (comparator O) :=
  (Nested.continuous_reward r H 0 s₁).measurable.comp (O.measurable_exploitation.prodMk measurable_id)

lemma comparator_eq_source {β : ℕ → ℝ} {τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} (O : BorelOracles β c r H s₁ τ Q) {q : Kernel S A} (hq : q ∈ Q) :
    comparator O q = constrainedValue β c r H s₁ τ q := (constrainedValue_eq O.toOracles hq).symm

lemma integrable_comparator (μ : Measure Ω) [IsFiniteMeasure μ]
    {β : ℕ → ℝ} {τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} (O : BorelOracles β c r H s₁ τ Q)
    (hr : ∀ h s a, r h s a ∈ Icc 0 1) (p : Ω → Kernel S A) (hp : Measurable p) :
    Integrable (fun ω => comparator O (p ω)) μ := by
  apply Integrable.of_bound ((measurable_comparator O).comp hp).aestronglyMeasurable H
  apply ae_of_all
  intro ω
  have hb := Algorithm.reward_bounds r hr (O.exploitation (p ω)) (p ω) H 0 s₁
  change |Nested.reward r (O.exploitation (p ω)) (p ω) H 0 s₁| ≤ (H : ℝ)
  simpa only [abs_of_nonneg hb.1] using hb.2

lemma measurable_selected_reward {β : ℕ → ℝ} {τ : ℝ} {c r : ℕ → S → A → ℝ}
    {H : ℕ} {s₁ : S} {Q : Set (Kernel S A)} (O : BorelOracles β c r H s₁ τ Q)
    (hβ : ∀ j, 0 < β j ∧ β j ≤ 1) (hc : ∀ h s a, c h s a ∈ Icc 0 1)
    (T : ℕ → ℝ) (sample : ℕ → Ω → Kernel S A) (hsample : ∀ n, Measurable (sample n))
    (p : Ω → Kernel S A) (hp : Measurable p) (n : ℕ) :
    Measurable (fun ω => Nested.reward r (selected O.toOracles T sample n ω) (p ω) H 0 s₁) :=
  (Nested.continuous_reward r H 0 s₁).measurable.comp
    ((measurable_selected O hβ hc T sample hsample n).prodMk hp)

lemma integrable_selected_reward (μ : Measure Ω) [IsFiniteMeasure μ]
    {β : ℕ → ℝ} {τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S} {Q : Set (Kernel S A)}
    (O : BorelOracles β c r H s₁ τ Q) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (hc : ∀ h s a, c h s a ∈ Icc 0 1) (hr : ∀ h s a, r h s a ∈ Icc 0 1)
    (T : ℕ → ℝ) (sample : ℕ → Ω → Kernel S A) (hsample : ∀ n, Measurable (sample n))
    (p : Ω → Kernel S A) (hp : Measurable p) (n : ℕ) :
    Integrable (fun ω => Nested.reward r (selected O.toOracles T sample n ω) (p ω) H 0 s₁) μ := by
  apply Integrable.of_bound (measurable_selected_reward O hβ hc T sample hsample p hp n).aestronglyMeasurable H
  apply ae_of_all
  intro ω
  have hb := Algorithm.reward_bounds r hr (selected O.toOracles T sample n ω) (p ω) H 0 s₁
  simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2

lemma measurable_selected_risk {β : ℕ → ℝ} {τ : ℝ} {c r : ℕ → S → A → ℝ}
    {H : ℕ} {s₁ : S} {Q : Set (Kernel S A)} (O : BorelOracles β c r H s₁ τ Q)
    (hβ : ∀ j, 0 < β j ∧ β j ≤ 1) (hc : ∀ h s a, c h s a ∈ Icc 0 1)
    (T : ℕ → ℝ) (sample : ℕ → Ω → Kernel S A) (hsample : ∀ n, Measurable (sample n))
    (p : Ω → Kernel S A) (hp : Measurable p) (n : ℕ) :
    Measurable (fun ω => risk β c (selected O.toOracles T sample n ω) (p ω) H 0 s₁) :=
  (StageCalibration.continuous_actualRisk β hβ c hc H 0 s₁).measurable.comp
    ((measurable_selected O hβ hc T sample hsample n).prodMk hp)

lemma integrable_selected_risk (μ : Measure Ω) [IsFiniteMeasure μ]
    {β : ℕ → ℝ} {τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S} {Q : Set (Kernel S A)}
    (O : BorelOracles β c r H s₁ τ Q) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (hc : ∀ h s a, c h s a ∈ Icc 0 1)
    (T : ℕ → ℝ) (sample : ℕ → Ω → Kernel S A) (hsample : ∀ n, Measurable (sample n))
    (p : Ω → Kernel S A) (hp : Measurable p) (n : ℕ) :
    Integrable (fun ω => risk β c (selected O.toOracles T sample n ω) (p ω) H 0 s₁) μ := by
  apply Integrable.of_bound (measurable_selected_risk O hβ hc T sample hsample p hp n).aestronglyMeasurable H
  apply ae_of_all
  intro ω
  have hb := StageRisk.risk_bounds β hβ c hc
    (RiskBridge.ofPolicy (selected O.toOracles T sample n ω)) (RiskBridge.ofKernel (p ω)) H 0 s₁
  change |StageRisk.risk β c (RiskBridge.ofPolicy (selected O.toOracles T sample n ω))
    (RiskBridge.ofKernel (p ω)) H 0 s₁| ≤ (H : ℝ)
  simpa only [abs_of_nonneg hb.1] using hb.2

section Posterior
variable {Model Hist : Type*} [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model]
  [MeasurableSpace Hist] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Posterior sampling cancels the actual stage-constrained comparator. -/
theorem comparator_symmetry (decode : Model → Kernel S A) (hdecode : Measurable decode)
    (latent sampled : Ω → Model) (hlatent : Measurable latent) (hsampled : Measurable sampled)
    (history : Ω → Hist) (hhistory : Measurable history)
    (hposterior : ProbabilityTheory.condDistrib latent history μ =ᵐ[μ.map history]
      ProbabilityTheory.condDistrib sampled history μ)
    {τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {masses : ℕ → ℝ} {Q : Set (Kernel S A)} (O : BorelOracles masses c r H s₁ τ Q)
    (hr : ∀ h s a, r h s a ∈ Icc 0 1)
    (hsupport : ∀ᵐ ω ∂μ, decode (latent ω) ∈ Q ∧ decode (sampled ω) ∈ Q) :
    (∫ ω, constrainedValue masses c r H s₁ τ (decode (latent ω)) -
      constrainedValue masses c r H s₁ τ (decode (sampled ω)) ∂μ) = 0 := by
  have hm := (measurable_comparator O).comp hdecode
  have he := Posterior.posterior_expectation_eq hhistory.aemeasurable hlatent.aemeasurable
    hsampled.aemeasurable hposterior (hm.comp measurable_snd)
  have hli := integrable_comparator μ O hr (fun ω => decode (latent ω)) (hdecode.comp hlatent)
  have hsi := integrable_comparator μ O hr (fun ω => decode (sampled ω)) (hdecode.comp hsampled)
  have hcongr : (fun ω => constrainedValue masses c r H s₁ τ (decode (latent ω)) -
      constrainedValue masses c r H s₁ τ (decode (sampled ω))) =ᵐ[μ]
      (fun ω => comparator O (decode (latent ω)) - comparator O (decode (sampled ω))) := by
    filter_upwards [hsupport] with ω hω
    rw [← comparator_eq_source O hω.1, ← comparator_eq_source O hω.2]
  rw [integral_congr_ae hcongr, integral_sub hli hsi]
  simpa only [sub_eq_zero] using he

end Posterior

end Borel

section PriorBank

variable (ν : Measure (Kernel S A)) [IsProbabilityMeasure ν]
  (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
  (τ : ℝ) (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1)
  (H : ℕ) (s₁ : S)
  (hstrict : ∀ q ∈ ν.support, ∃ π : Simulation.Policy S A,
    StageRisk.risk β c π (RiskBridge.ofKernel q) H 0 s₁ < τ)
include hβ hc hstrict

/-- The positive bank gap and nonnegative threshold follow from actual strict
feasibility on the compact support, with no numerical gap supplied. -/
lemma induced_gap_parameters :
    0 < StageCalibration.uniformGap ν β c H s₁ τ ∧ 0 ≤ τ := by
  have hb := StageCalibration.calibration_deposit_bounds ν β hβ H c hc s₁ τ hstrict
  have hν : ν ≠ 0 := by
    intro hz
    have hm : ν Set.univ = 1 := measure_univ
    simp [hz] at hm
  obtain ⟨q, hq⟩ := ν.nonempty_support hν
  exact ⟨hb.1, (hb.1.le.trans (hb.2 q hq).1).trans (hb.2 q hq).2⟩

/-- The exact source deposits satisfy the bank inequalities on each support path. -/
lemma actual_deposit_bounds (sample : ℕ → Ω → Kernel S A) (ω : Ω)
    (hsample : ∀ n, sample n ω ∈ ν.support) :
    ∀ n, StageCalibration.uniformGap ν β c H s₁ τ ≤ deposits β τ c H s₁ sample (n+1) ω ∧
      deposits β τ c H s₁ sample (n+1) ω ≤ τ := by
  intro n
  exact (StageCalibration.calibration_deposit_bounds ν β hβ H c hc s₁ τ hstrict).2
    (sample n ω) (hsample n)

/-- B.3's calibration bound for the actual stage target and induced prior gap. -/
theorem calibration_count (hH : 1 ≤ H) (sample : ℕ → Ω → Kernel S A) (ω : Ω)
    (hsample : ∀ n, sample n ω ∈ ν.support) (K : ℕ) :
    (Bank.count (StageCharging.stageTarget (S := S) (A := A) β H)
      (fun j => deposits β τ c H s₁ sample j ω) K : ℝ) ≤
      min (K : ℝ) ((StageCharging.stageTarget (S := S) (A := A) β H K + τ) /
        StageCalibration.uniformGap ν β c H s₁ τ) := by
  have hg := induced_gap_parameters ν β hβ τ c hc H s₁ hstrict
  have hd := actual_deposit_bounds ν β hβ τ c hc H s₁ hstrict sample ω hsample
  have hp := StageCharging.stage_target_properties (A := A) β H s₁ hH hg.1
  exact Bank.calibration_count_bound _ _ _ _ hg.1 hp.1 (by simpa [hp.2.1] using hg.2)
    (fun n _ => (hd n).1) (fun n _ => (hd n).2) K

/-- The actual calibration bank pays all but the explicit stage residual. -/
theorem bank_deficit (hH : 1 ≤ H) (sample : ℕ → Ω → Kernel S A) (ω : Ω)
    (hsample : ∀ n, sample n ω ∈ ν.support) (K : ℕ) :
    StageCharging.stageTarget (S := S) (A := A) β H K -
      Bank.bank (StageCharging.stageTarget (S := S) (A := A) β H)
        (fun j => deposits β τ c H s₁ sample j ω) K ≤
      StageCharging.stageResidual (S := S) (A := A) β H
        (StageCalibration.uniformGap ν β c H s₁ τ) := by
  have hg := induced_gap_parameters ν β hβ τ c hc H s₁ hstrict
  have hd := actual_deposit_bounds ν β hβ τ c hc H s₁ hstrict sample ω hsample
  have hp := StageCharging.stage_target_properties (A := A) β H s₁ hH hg.1
  exact Bank.deficit_le_residual _ _ _ _ hp.2.1 (fun n _ => (hd n).1)
    hp.2.2.1 hp.2.2.2.1 K

/-- For every support path the actual calibration frequency vanishes. -/
theorem calibration_sparse (hH : 1 ≤ H) (sample : ℕ → Ω → Kernel S A) (ω : Ω)
    (hsample : ∀ n, sample n ω ∈ ν.support) :
    Filter.Tendsto (fun K : ℕ =>
      (Bank.count (StageCharging.stageTarget (S := S) (A := A) β H)
        (fun j => deposits β τ c H s₁ sample j ω) K : ℝ) / (K : ℝ))
      Filter.atTop (nhds 0) := by
  have hg := induced_gap_parameters ν β hβ τ c hc H s₁ hstrict
  have hd := actual_deposit_bounds ν β hβ τ c hc H s₁ hstrict sample ω hsample
  have hp := StageCharging.stage_target_properties (A := A) β H s₁ hH hg.1
  exact Bank.calibration_sparse_of_target_sublinear _ _ _ _ hg.1 hp.1
    (by simpa [hp.2.1] using hg.2) (fun n _ => (hd n).1) (fun n _ => (hd n).2) hp.2.2.2.2

/-- Exact optimization charges sampled reward only on calibration episodes,
and the real stage bank supplies its explicit numerical bound. -/
theorem sampled_reward_bound (r : ℕ → S → A → ℝ) (hr : ∀ h s a, r h s a ∈ Icc 0 1)
    (O : Oracles β c r H s₁ τ ν.support) (hH : 1 ≤ H)
    (sample : ℕ → Ω → Kernel S A) (ω : Ω) (hsample : ∀ n, sample n ω ∈ ν.support) (K : ℕ) :
    (∑ n ∈ Finset.range K, (constrainedValue β c r H s₁ τ (sample n ω) -
      Nested.reward r (selected O (StageCharging.stageTarget (S := S) (A := A) β H) sample n ω)
        (sample n ω) H 0 s₁)) ≤
      (H : ℝ) * min (K : ℝ) ((StageCharging.stageTarget (S := S) (A := A) β H K + τ) /
        StageCalibration.uniformGap ν β c H s₁ τ) := by
  exact (sampled_reward_count O hr _ sample ω hsample K).trans
    (mul_le_mul_of_nonneg_left (calibration_count ν β hβ τ c hc H s₁ hstrict hH sample ω hsample K)
      (Nat.cast_nonneg H))

section Expected
variable [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (sample : ℕ → Ω → Kernel S A) (hsample : ∀ n, Measurable (sample n))
  (hsupport : ∀ᵐ ω ∂μ, ∀ n, sample n ω ∈ ν.support)
include hsample hsupport

lemma actual_deposit_bounds_ae (T : ℕ → ℝ) :
    ∀ᵐ ω ∂μ, Assembly.DepositBounds T (deposits β τ c H s₁ sample)
      (StageCalibration.uniformGap ν β c H s₁ τ) τ ω := by
  filter_upwards [hsupport] with ω hω
  exact fun n _ => actual_deposit_bounds ν β hβ τ c hc H s₁ hstrict sample ω hω n

theorem expected_calibration_count (hH : 1 ≤ H) (K : ℕ) :
    (∫ ω, Assembly.countRV (StageCharging.stageTarget (S := S) (A := A) β H)
      (deposits β τ c H s₁ sample) K ω ∂μ) ≤
      min (K : ℝ) ((StageCharging.stageTarget (S := S) (A := A) β H K + τ) /
        StageCalibration.uniformGap ν β c H s₁ τ) := by
  have hg := induced_gap_parameters ν β hβ τ c hc H s₁ hstrict
  have hp := StageCharging.stage_target_properties (A := A) β H s₁ hH hg.1
  exact Assembly.expected_count_bound _ _ _ _ (measurable_deposits β hβ τ c hc H s₁ sample hsample)
    hg.1 hp.1 (by simpa [hp.2.1] using hg.2)
    (actual_deposit_bounds_ae ν β hβ τ c hc H s₁ hstrict μ sample hsample hsupport _) K

theorem expected_bank_deficit (hH : 1 ≤ H) (K : ℕ) :
    StageCharging.stageTarget (S := S) (A := A) β H K -
      (∫ ω, Assembly.bankRV (StageCharging.stageTarget (S := S) (A := A) β H)
        (deposits β τ c H s₁ sample) K ω ∂μ) ≤
      StageCharging.stageResidual (S := S) (A := A) β H
        (StageCalibration.uniformGap ν β c H s₁ τ) := by
  have hg := induced_gap_parameters ν β hβ τ c hc H s₁ hstrict
  have hp := StageCharging.stage_target_properties (A := A) β H s₁ hH hg.1
  exact Assembly.expected_deficit_bound _ _ _ _ _
    (measurable_deposits β hβ τ c hc H s₁ sample hsample) hg.1 hp.1
    (by simpa [hp.2.1] using hg.2) hp.2.1 hp.2.2.1 hp.2.2.2.1
    (actual_deposit_bounds_ae ν β hβ τ c hc H s₁ hstrict μ sample hsample hsupport _) K

end Expected
end PriorBank
end
end Paper36.StageAlgorithm
