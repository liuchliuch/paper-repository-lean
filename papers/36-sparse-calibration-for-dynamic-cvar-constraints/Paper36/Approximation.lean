import Paper36.Algorithm
import Paper36.SourceBank

/-! Corollary B.1 at the oracle/execution level. Only exploitation is approximate;
calibration deposits remain the actual exact sampled minimum-risk slack. -/
namespace Paper36.Approximation
open Paper36.Regularity Paper36.Nested Paper36.Algorithm
open scoped BigOperators
noncomputable section
variable {S A Ω : Type*} [Fintype S] [Fintype A] [Nonempty A]

structure Oracles (α : ℝ) (c r : ℕ → S → A → ℝ) (H : ℕ) (s₁ : S)
    (τ : ℝ) (Q : Set (Kernel S A)) (ε ζ : ℕ → ℝ) where
  calibration : Kernel S A → Policy S A
  exploitation : ℕ → Kernel S A → Policy S A
  cal_exact : ∀ q ∈ Q, risk α c (calibration q) q H 0 s₁ = minimumRisk α c H 0 s₁ q
  exp_risk : ∀ n q, q ∈ Q → risk α c (exploitation n q) q H 0 s₁ ≤ τ + ε n
  exp_reward : ∀ n q, q ∈ Q → constrainedValue α c r H s₁ τ q ≤
    reward r (exploitation n q) q H 0 s₁ + ζ n

def selected {α τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} {ε ζ : ℕ → ℝ} (O : Oracles α c r H s₁ τ Q ε ζ)
    (T : ℕ → ℝ) (sample : ℕ → Ω → Kernel S A) (n : ℕ) (ω : Ω) : Policy S A :=
  if Bank.calibrates T (fun j => Algorithm.deposits α τ c H s₁ sample j ω) n
  then O.calibration (sample n ω) else O.exploitation n (sample n ω)

lemma sampled_risk {α τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} {ε ζ : ℕ → ℝ} (O : Oracles α c r H s₁ τ Q ε ζ)
    (T : ℕ → ℝ) (sample : ℕ → Ω → Kernel S A) (n : ℕ) (ω : Ω) (hs : sample n ω ∈ Q) :
    (Bank.calibrates T (fun j => Algorithm.deposits α τ c H s₁ sample j ω) n →
      risk α c (selected O T sample n ω) (sample n ω) H 0 s₁ =
        τ - Algorithm.deposits α τ c H s₁ sample (n+1) ω) ∧
    (¬ Bank.calibrates T (fun j => Algorithm.deposits α τ c H s₁ sample j ω) n →
      risk α c (selected O T sample n ω) (sample n ω) H 0 s₁ ≤ τ + ε n) := by
  constructor
  · intro hn
    rw [selected, if_pos hn, O.cal_exact _ hs]
    simp only [Algorithm.deposits]
    ring
  · intro hn
    rw [selected, if_neg hn]
    exact O.exp_risk n _ hs

lemma sampled_reward {α τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} {ε ζ : ℕ → ℝ} (O : Oracles α c r H s₁ τ Q ε ζ)
    (exact : Algorithm.Oracles α c r H s₁ τ Q)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (T : ℕ → ℝ) (sample : ℕ → Ω → Kernel S A) (n : ℕ) (ω : Ω) (hs : sample n ω ∈ Q) :
    (Bank.calibrates T (fun j => Algorithm.deposits α τ c H s₁ sample j ω) n →
      constrainedValue α c r H s₁ τ (sample n ω) -
        reward r (selected O T sample n ω) (sample n ω) H 0 s₁ ≤ H) ∧
    (¬ Bank.calibrates T (fun j => Algorithm.deposits α τ c H s₁ sample j ω) n →
      constrainedValue α c r H s₁ τ (sample n ω) -
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
theorem sampled_bank_cancellation {α τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} {ε ζ : ℕ → ℝ} (O : Oracles α c r H s₁ τ Q ε ζ)
    (hε : ∀ n, 0 ≤ ε n) (T : ℕ → ℝ) (sample : ℕ → Ω → Kernel S A)
    (ω : Ω) (hs : ∀ n, sample n ω ∈ Q) (K : ℕ) :
    (∑ n ∈ Finset.range K, (risk α c (selected O T sample n ω) (sample n ω) H 0 s₁ - τ)) ≤
      (∑ n ∈ Finset.range K, ε n) -
        Bank.bank T (fun j => Algorithm.deposits α τ c H s₁ sample j ω) K := by
  apply Bank.sampled_debt_cancellation _ _ _ _ hε
  · intro n hn
    have hh := (sampled_risk O T sample n ω (hs n)).1 hn
    linarith
  · intro n hn
    have hh := (sampled_risk O T sample n ω (hs n)).2 hn
    linarith

/-- Certified optimization error is additive to the actual calibration episode cost. -/
theorem sampled_reward_total {α τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} {ε ζ : ℕ → ℝ} (O : Oracles α c r H s₁ τ Q ε ζ)
    (exact : Algorithm.Oracles α c r H s₁ τ Q) (hζ : ∀ n, 0 ≤ ζ n)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (T : ℕ → ℝ) (sample : ℕ → Ω → Kernel S A) (ω : Ω)
    (hs : ∀ n, sample n ω ∈ Q) (K : ℕ) :
    (∑ n ∈ Finset.range K, (constrainedValue α c r H s₁ τ (sample n ω) -
      reward r (selected O T sample n ω) (sample n ω) H 0 s₁)) ≤
      H * (Bank.count T (fun j => Algorithm.deposits α τ c H s₁ sample j ω) K : ℝ) +
        ∑ n ∈ Finset.range K, ζ n := by
  apply Bank.sampled_reward_shortfall _ _ _ _ _ hζ
  · intro n hn
    exact (sampled_reward O exact hr T sample n ω (hs n)).1 hn
  · intro n hn
    exact (sampled_reward O exact hr T sample n ω (hs n)).2 hn

end
end Paper36.Approximation
