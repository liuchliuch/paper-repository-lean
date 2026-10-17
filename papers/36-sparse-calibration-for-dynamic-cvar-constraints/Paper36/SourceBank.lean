import Paper36.Algorithm
import Paper36.Weights

/-! Source-instance bank guarantees: all weights, dimensions and deposits are
those of the actual randomized physical-state Markov problem. -/
namespace Paper36.SourceBank
open Paper36.Regularity Paper36.Nested Paper36.Algorithm
noncomputable section
variable {S A Ω : Type*} [Fintype S] [Fintype A] [Nonempty A]

def target (α : ℝ) (H : ℕ) : ℕ → ℝ :=
  BankTarget.paperTarget (Fintype.card S) (Fintype.card A) H (Weights.W α H)

def residual (α Δ : ℝ) (H : ℕ) : ℝ :=
  BankTarget.paperResidual (Fintype.card S) (Fintype.card A) H (Weights.W α H) Δ

def lowConstant (α : ℝ) (H : ℕ) : ℝ :=
  2 * Fintype.card S * Fintype.card A * H * Weights.w α H + (H : ℝ)/2

def riskEnvelope (α Δ : ℝ) (H : ℕ) : ℝ := lowConstant (S := S) (A := A) α H + residual (S := S) (A := A) α Δ H

lemma dimensions (s₁ : S) {H : ℕ} (hH : 1 ≤ H) :
    1 ≤ (Fintype.card S : ℝ) ∧ 1 ≤ (Fintype.card A : ℝ) ∧ 1 ≤ (H : ℝ) := by
  letI : Nonempty S := ⟨s₁⟩
  exact ⟨by exact_mod_cast Fintype.card_pos (α := S),
    by exact_mod_cast Fintype.card_pos (α := A), by exact_mod_cast hH⟩

/-- Theorem 4.2's pathwise calibration bound for every actual sample path. -/
theorem calibration_count (α τ Δ : ℝ) (hα : 0 < α) (hΔ : 0 < Δ) (hτ : 0 ≤ τ)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (H : ℕ) (hH : 1 ≤ H) (s₁ : S) (Q : Set (Kernel S A))
    (hgap : ∀ q ∈ Q, minimumRisk α c H 0 s₁ q ≤ τ - Δ)
    (sample : ℕ → Ω → Kernel S A) (ω : Ω) (hsample : ∀ n, sample n ω ∈ Q) (K : ℕ) :
    (Bank.count (target (S := S) (A := A) α H)
      (fun j => deposits α τ c H s₁ sample j ω) K : ℝ) ≤
      min (K : ℝ) ((target (S := S) (A := A) α H K + τ)/Δ) := by
  have hd := actual_deposit_bounds α τ Δ hα.le c hc H s₁ Q hgap sample ω hsample
  have hp := dimensions (A := A) s₁ hH
  exact BankTarget.calibration_count _ hp.1 hp.2.1 hp.2.2 (Weights.W_nonneg α H)
    hΔ hτ (fun n _ => hd n) K

/-- The actual sampled-risk bank has the source's explicit K-independent residual. -/
theorem bank_deficit (α τ Δ : ℝ) (hα : 0 < α) (hΔ : 0 < Δ)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (H : ℕ) (hH : 1 ≤ H) (s₁ : S) (Q : Set (Kernel S A))
    (hgap : ∀ q ∈ Q, minimumRisk α c H 0 s₁ q ≤ τ - Δ)
    (sample : ℕ → Ω → Kernel S A) (ω : Ω) (hsample : ∀ n, sample n ω ∈ Q) (K : ℕ) :
    target (S := S) (A := A) α H K -
      Bank.bank (target (S := S) (A := A) α H) (fun j => deposits α τ c H s₁ sample j ω) K ≤
      residual (S := S) (A := A) α Δ H := by
  have hd := actual_deposit_bounds α τ Δ hα.le c hc H s₁ Q hgap sample ω hsample
  have hp := dimensions (A := A) s₁ hH
  exact BankTarget.bank_deficit _ hp.1 hp.2.1 hp.2.2 (Weights.W_nonneg α H)
    hΔ (fun n _ => (hd n).1) K

/-- For each fixed source instance the actual calibration frequency tends to zero. -/
theorem calibration_sparse (α τ Δ : ℝ) (hα : 0 < α) (hΔ : 0 < Δ) (hτ : 0 ≤ τ)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (H : ℕ) (hH : 1 ≤ H) (s₁ : S) (Q : Set (Kernel S A))
    (hgap : ∀ q ∈ Q, minimumRisk α c H 0 s₁ q ≤ τ - Δ)
    (sample : ℕ → Ω → Kernel S A) (ω : Ω) (hsample : ∀ n, sample n ω ∈ Q) :
    Filter.Tendsto (fun K : ℕ =>
      (Bank.count (target (S := S) (A := A) α H)
        (fun j => deposits α τ c H s₁ sample j ω) K : ℝ)/(K : ℝ))
      Filter.atTop (nhds 0) := by
  have hd := actual_deposit_bounds α τ Δ hα.le c hc H s₁ Q hgap sample ω hsample
  have hp := dimensions (A := A) s₁ hH
  exact BankTarget.calibration_sparse _ hp.1 hp.2.1 hp.2.2 (Weights.W_nonneg α H)
    hΔ hτ (fun n _ => hd n)

@[simp] theorem horizon_one_target (α : ℝ) : target (S := S) (A := A) α 1 = fun _ => 0 := by
  funext K
  simp [target, BankTarget.paperTarget]

end
end Paper36.SourceBank
