import Paper36.Calibration
import Paper36.Prior
import Paper36.BankTarget

/-! Algorithm 1 in the actual finite randomized physical-state Markov model.
The rule only reads the known target and exact sampled-model slack. It has no
terminal episode argument and no numerical feasibility-gap argument. -/
namespace Paper36.Algorithm
open Set Paper36.Regularity Paper36.Nested
open scoped BigOperators
noncomputable section
variable {S A Ω : Type*} [Fintype S] [Fintype A] [Nonempty A]

/-- The exact two planning oracles assumed by the source. Their Borel selection
can be supplied using the published measurable maximum/selection theorem; the
quantified optimization specifications themselves are explicit here. -/
structure Oracles (α : ℝ) (c r : ℕ → S → A → ℝ) (H : ℕ) (s₁ : S)
    (τ : ℝ) (Q : Set (Kernel S A)) where
  calibration : Kernel S A → Policy S A
  exploitation : Kernel S A → Policy S A
  cal_exact : ∀ q ∈ Q, risk α c (calibration q) q H 0 s₁ = minimumRisk α c H 0 s₁ q
  exp_feasible : ∀ q ∈ Q, risk α c (exploitation q) q H 0 s₁ ≤ τ
  exp_optimal : ∀ q ∈ Q, ∀ π, risk α c π q H 0 s₁ ≤ τ →
    reward r π q H 0 s₁ ≤ reward r (exploitation q) q H 0 s₁

/-- The source's exact constrained comparator value (2.5). -/
def constrainedValue (α : ℝ) (c r : ℕ → S → A → ℝ) (H : ℕ) (s₁ : S)
    (τ : ℝ) (q : Kernel S A) : ℝ :=
  sSup {v | ∃ π : Policy S A, risk α c π q H 0 s₁ ≤ τ ∧ reward r π q H 0 s₁ = v}

lemma constrainedValue_eq {α τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} (O : Oracles α c r H s₁ τ Q) {q : Kernel S A} (hq : q ∈ Q) :
    constrainedValue α c r H s₁ τ q = reward r (O.exploitation q) q H 0 s₁ := by
  unfold constrainedValue
  have hne : {v | ∃ π : Policy S A, risk α c π q H 0 s₁ ≤ τ ∧ reward r π q H 0 s₁ = v}.Nonempty :=
    ⟨reward r (O.exploitation q) q H 0 s₁, ⟨O.exploitation q, O.exp_feasible q hq, rfl⟩⟩
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt hne
  · rintro _ ⟨π, hf, rfl⟩
    exact O.exp_optimal q hq π hf
  · intro b hb
    exact ⟨_, ⟨O.exploitation q, O.exp_feasible q hq, rfl⟩, hb⟩

/-- Ordinary bounded rewards give the exact per-calibration H allowance. -/
lemma reward_bounds (r : ℕ → S → A → ℝ) (hr : ∀ h s a, r h s a ∈ Icc 0 1)
    (π : Policy S A) (q : Kernel S A) (n h : ℕ) (s : S) :
    reward r π q n h s ∈ Icc 0 (n : ℝ) := by
  induction n generalizing h s with
  | zero => simp [reward]
  | succ n ih =>
    have hinner (a : A) : (∑ t, q s a t * reward r π q n (h+1) t) ∈ Icc 0 (n : ℝ) := by
      constructor
      · exact Finset.sum_nonneg fun t _ => mul_nonneg ((q s a).property.1 t) (ih (h+1) t).1
      · calc
          _ ≤ ∑ t, q s a t * (n : ℝ) := Finset.sum_le_sum fun t _ =>
            mul_le_mul_of_nonneg_left (ih (h+1) t).2 ((q s a).property.1 t)
          _ = n := by rw [← Finset.sum_mul, law_sum (q s a), one_mul]
    constructor
    · exact Finset.sum_nonneg fun a _ => mul_nonneg ((π h s).property.1 a)
        (add_nonneg (hr h s a).1 (hinner a).1)
    · calc
        _ ≤ ∑ a, π h s a * ((n : ℝ)+1) := by
          apply Finset.sum_le_sum
          intro a _
          apply mul_le_mul_of_nonneg_left _ ((π h s).property.1 a)
          linarith [(hr h s a).2, (hinner a).2]
        _ = (n+1 : ℕ) := by rw [← Finset.sum_mul, law_sum (π h s), one_mul]; push_cast; rfl

lemma minimumRisk_nonneg (α : ℝ) (hα : 0 ≤ α) (c : ℕ → S → A → ℝ)
    (hc : ∀ h s a, c h s a ∈ Icc 0 1) (q : Kernel S A) (H : ℕ) (s₁ : S) :
    0 ≤ minimumRisk α c H 0 s₁ q := by
  obtain ⟨π, hπ⟩ := exists_minimumRisk α c H 0 s₁ q
  rw [hπ]
  exact (risk_bounds α hα c hc π q H 0 s₁).1

/-- A sample at episode n (zero based) supplies the exact deposit d(n+1). -/
def deposits (α τ : ℝ) (c : ℕ → S → A → ℝ) (H : ℕ) (s₁ : S)
    (sample : ℕ → Ω → Kernel S A) : ℕ → Ω → ℝ
  | 0, _ => 0
  | n+1, ω => τ - minimumRisk α c H 0 s₁ (sample n ω)

/-- The actual execution rule; its arguments deliberately contain neither K nor Δ. -/
def selected {α τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} (O : Oracles α c r H s₁ τ Q)
    (T : ℕ → ℝ) (sample : ℕ → Ω → Kernel S A) (n : ℕ) (ω : Ω) : Policy S A :=
  if Bank.calibrates T (fun j => deposits α τ c H s₁ sample j ω) n
  then O.calibration (sample n ω) else O.exploitation (sample n ω)

lemma selected_sampled_risk {α τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} (O : Oracles α c r H s₁ τ Q)
    (T : ℕ → ℝ) (sample : ℕ → Ω → Kernel S A) (n : ℕ) (ω : Ω)
    (hsample : sample n ω ∈ Q) :
    (Bank.calibrates T (fun j => deposits α τ c H s₁ sample j ω) n →
      risk α c (selected O T sample n ω) (sample n ω) H 0 s₁ =
        τ - deposits α τ c H s₁ sample (n+1) ω) ∧
    (¬ Bank.calibrates T (fun j => deposits α τ c H s₁ sample j ω) n →
      risk α c (selected O T sample n ω) (sample n ω) H 0 s₁ ≤ τ) := by
  constructor
  · intro hn
    rw [selected, if_pos hn, O.cal_exact _ hsample]
    simp only [deposits]
    ring
  · intro hn
    simp only [selected, if_neg hn]
    exact O.exp_feasible _ hsample

lemma selected_sampled_reward {α τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} (O : Oracles α c r H s₁ τ Q)
    (hr : ∀ h s a, r h s a ∈ Icc 0 1)
    (T : ℕ → ℝ) (sample : ℕ → Ω → Kernel S A) (n : ℕ) (ω : Ω)
    (hsample : sample n ω ∈ Q) :
    (Bank.calibrates T (fun j => deposits α τ c H s₁ sample j ω) n →
      constrainedValue α c r H s₁ τ (sample n ω) -
        reward r (selected O T sample n ω) (sample n ω) H 0 s₁ ≤ H) ∧
    (¬ Bank.calibrates T (fun j => deposits α τ c H s₁ sample j ω) n →
      constrainedValue α c r H s₁ τ (sample n ω) -
        reward r (selected O T sample n ω) (sample n ω) H 0 s₁ = 0) := by
  rw [constrainedValue_eq O hsample]
  constructor
  · intro hn
    simp only [selected, if_pos hn]
    have hu := (reward_bounds r hr (O.exploitation (sample n ω)) (sample n ω) H 0 s₁).2
    have hl := (reward_bounds r hr (O.calibration (sample n ω)) (sample n ω) H 0 s₁).1
    linarith
  · intro hn
    simp only [selected, if_neg hn, sub_self]

/-- Actual minimum risks and the uniform gap supply every deposit bound (5.15). -/
lemma actual_deposit_bounds (α τ Δ : ℝ) (hα : 0 ≤ α)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1)
    (H : ℕ) (s₁ : S) (Q : Set (Kernel S A))
    (hgap : ∀ q ∈ Q, minimumRisk α c H 0 s₁ q ≤ τ - Δ)
    (sample : ℕ → Ω → Kernel S A) (ω : Ω) (hsample : ∀ n, sample n ω ∈ Q) :
    ∀ n, Δ ≤ deposits α τ c H s₁ sample (n+1) ω ∧
      deposits α τ c H s₁ sample (n+1) ω ≤ τ := by
  intro n
  exact Bank.slack_bounds τ Δ _ (minimumRisk_nonneg α hα c hc _ H s₁)
    (hgap _ (hsample n))

/-- The actual algorithm's sampled-model risk debts telescope to minus its actual bank. -/
theorem sampled_risk_bank {α τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} (O : Oracles α c r H s₁ τ Q)
    (T : ℕ → ℝ) (sample : ℕ → Ω → Kernel S A) (ω : Ω)
    (hsample : ∀ n, sample n ω ∈ Q) (K : ℕ) :
    (∑ n ∈ Finset.range K, (risk α c (selected O T sample n ω) (sample n ω) H 0 s₁ - τ)) ≤
      -Bank.bank T (fun j => deposits α τ c H s₁ sample j ω) K := by
  apply Bank.exact_sampled_debt_cancellation
  · intro n hn
    have h := (selected_sampled_risk O T sample n ω (hsample n)).1 hn
    linarith
  · intro n hn
    exact sub_nonpos.mpr ((selected_sampled_risk O T sample n ω (hsample n)).2 hn)

/-- The consequent (5.12) of a model-error certificate uses the real selected policies and bank. -/
theorem risk_bank_certificate_path {α τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} (O : Oracles α c r H s₁ τ Q)
    (T : ℕ → ℝ) (sample : ℕ → Ω → Kernel S A) (latent : Ω → Kernel S A)
    (ω : Ω) (hsample : ∀ n, sample n ω ∈ Q) (K : ℕ) (E : ℝ)
    (hmodel : (∑ n ∈ Finset.range K,
      (risk α c (selected O T sample n ω) (latent ω) H 0 s₁ -
       risk α c (selected O T sample n ω) (sample n ω) H 0 s₁)) ≤ E) :
    (∑ n ∈ Finset.range K, (risk α c (selected O T sample n ω) (latent ω) H 0 s₁ - τ)) ≤
      E - Bank.bank T (fun j => deposits α τ c H s₁ sample j ω) K := by
  have hc := sampled_risk_bank O T sample ω hsample K
  have heq : (∑ n ∈ Finset.range K,
      (risk α c (selected O T sample n ω) (latent ω) H 0 s₁ - τ)) =
      (∑ n ∈ Finset.range K,
        (risk α c (selected O T sample n ω) (latent ω) H 0 s₁ -
         risk α c (selected O T sample n ω) (sample n ω) H 0 s₁)) +
      (∑ n ∈ Finset.range K,
        (risk α c (selected O T sample n ω) (sample n ω) H 0 s₁ - τ)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [heq]
  linarith

/-- Exact planning selectors exist pointwise on every strictly feasible model support.
This theorem supplies the optimization specifications. Borel selection is a
separate, explicitly recorded external measurable-selection ingredient. -/
theorem exists_oracles (α τ : ℝ) (hα : 0 ≤ α) (c r : ℕ → S → A → ℝ)
    (H : ℕ) (s₁ : S) (Q : Set (Kernel S A))
    (hstrict : ∀ q ∈ Q, minimumRisk α c H 0 s₁ q < τ) :
    Nonempty (Oracles α c r H s₁ τ Q) := by
  classical
  let cal : Kernel S A → Policy S A := fun q =>
    Classical.choose (Calibration.exists_deterministic_minimizer α c q H 0)
  have hcal (q : Kernel S A) : risk α c (cal q) q H 0 s₁ = minimumRisk α c H 0 s₁ q := by
    rw [Calibration.minimumRisk_eq_dp α hα]
    exact (Classical.choose_spec (Calibration.exists_deterministic_minimizer α c q H 0)).2 s₁
  have hex (q : Kernel S A) (hq : q ∈ Q) : ∃ π : Policy S A,
      risk α c π q H 0 s₁ ≤ τ ∧ ∀ π', risk α c π' q H 0 s₁ ≤ τ →
        reward r π' q H 0 s₁ ≤ reward r π q H 0 s₁ :=
    exists_constrained_optimum α c r H 0 s₁ q τ ⟨cal q, by rw [hcal]; exact (hstrict q hq).le⟩
  let exploit : Kernel S A → Policy S A := fun q =>
    if hq : q ∈ Q then Classical.choose (hex q hq) else cal q
  refine ⟨⟨cal, exploit, fun q _ => hcal q, ?_, ?_⟩⟩
  · intro q hq
    simp only [exploit, dif_pos hq]
    exact (Classical.choose_spec (hex q hq)).1
  · intro q hq π hf
    simp only [exploit, dif_pos hq]
    exact (Classical.choose_spec (hex q hq)).2 π hf

end
end Paper36.Algorithm
