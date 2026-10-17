import Paper36.SourceBank
import Paper36.BorelAlgorithm
import Paper36.Endpoints

/-! The H=1 portion of Theorem 4.2 for the actual algorithm on an arbitrary
probability space, not a restriction to a finite prior. -/
namespace Paper36.SourceEndpoints
open MeasureTheory Paper36.Regularity Paper36.Nested Paper36.Algorithm
open scoped BigOperators
noncomputable section
variable {S A Ω : Type*} [Fintype S] [Fintype A] [Nonempty A]

lemma selected_one {α τ : ℝ} {c r : ℕ → S → A → ℝ} {s₁ : S}
    {Q : Set (Kernel S A)} (O : Oracles α c r 1 s₁ τ Q)
    (sample : ℕ → Ω → Kernel S A) (n : ℕ) (ω : Ω) :
    selected O (SourceBank.target (S := S) (A := A) α 1) sample n ω =
      O.exploitation (sample n ω) := by
  rw [SourceBank.horizon_one_target]
  unfold selected Bank.calibrates
  simp only [(Bank.zero_target (fun j => deposits α τ c 1 s₁ sample j ω) n).1, lt_self_iff_false, if_false]

lemma horizon_one_path {α τ : ℝ} {c r : ℕ → S → A → ℝ} {s₁ : S}
    {Q : Set (Kernel S A)} (O : Oracles α c r 1 s₁ τ Q)
    (sample : ℕ → Ω → Kernel S A) (latent : Ω → Kernel S A) (ω : Ω)
    (hlatent : latent ω ∈ Q) (hsample : ∀ n, sample n ω ∈ Q) (K : ℕ) :
    (∑ n ∈ Finset.range K,
      (risk α c (selected O (SourceBank.target (S := S) (A := A) α 1) sample n ω)
        (latent ω) 1 0 s₁ - τ)) ≤ 0 ∧
    (∑ n ∈ Finset.range K,
      (constrainedValue α c r 1 s₁ τ (latent ω) -
        reward r (selected O (SourceBank.target (S := S) (A := A) α 1) sample n ω)
          (latent ω) 1 0 s₁)) = 0 := by
  simp_rw [selected_one]
  rw [constrainedValue_eq O hlatent]
  exact Endpoints.one_stage_exact_oracles α τ c r (latent ω) (fun n => sample n ω)
    (fun n => O.exploitation (sample n ω)) (O.exploitation (latent ω)) 0 s₁
    (O.exp_feasible _ hlatent) (fun π hf => O.exp_optimal _ hlatent π hf)
    (fun n => O.exp_feasible _ (hsample n)) (fun n π hf => O.exp_optimal _ (hsample n) π hf) K

/-- No model identifiability or posterior concentration is needed at H=1. -/
theorem horizon_one_any_prior [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {α τ : ℝ} {c r : ℕ → S → A → ℝ} {s₁ : S} {Q : Set (Kernel S A)}
    (O : Oracles α c r 1 s₁ τ Q)
    (sample : ℕ → Ω → Kernel S A) (latent : Ω → Kernel S A)
    (hsupport : ∀ᵐ ω ∂μ, latent ω ∈ Q ∧ ∀ n, sample n ω ∈ Q) (K : ℕ) :
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
  refine ⟨?_, ?_, ?_⟩
  · apply integral_nonpos_of_ae
    filter_upwards [hsupport] with ω hω
    exact (horizon_one_path O sample latent ω hω.1 hω.2 K).1
  · have hz : (fun ω => ∑ n ∈ Finset.range K,
        (constrainedValue α c r 1 s₁ τ (latent ω) -
          reward r (selected O (SourceBank.target (S := S) (A := A) α 1) sample n ω)
            (latent ω) 1 0 s₁)) =ᵐ[μ] (fun _ => 0) := by
      filter_upwards [hsupport] with ω hω
      exact (horizon_one_path O sample latent ω hω.1 hω.2 K).2
    rw [integral_congr_ae hz, integral_zero]
  · intro ω
    rw [SourceBank.horizon_one_target]
    exact Bank.zero_target _ K

end
end Paper36.SourceEndpoints
