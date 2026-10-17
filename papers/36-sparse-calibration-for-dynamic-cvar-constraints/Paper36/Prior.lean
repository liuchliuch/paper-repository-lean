import Paper36.Nested
import Mathlib.MeasureTheory.Measure.Support

/-! Lemma 2.1 on the support of an arbitrary prior on the finite kernel simplex. -/
namespace Paper36.Prior
open Set MeasureTheory Paper36.Regularity Paper36.Nested
noncomputable section
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
variable [MeasurableSpace (Kernel S A)]

/-- The uniform margin follows from pointwise strict feasibility on the actual prior support.
No common feasible policy or numerical margin is supplied. -/
theorem lemma_2_1 (μ : Measure (Kernel S A)) [IsProbabilityMeasure μ]
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (H : ℕ)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1) (s₁ : S)
    (τ : ℝ) (hstrict : ∀ q ∈ μ.support, minimumRisk α c H 0 s₁ q < τ) :
    0 < τ - sSup (minimumRisk α c H 0 s₁ '' μ.support) ∧
      ∀ q ∈ μ.support, τ - sSup (minimumRisk α c H 0 s₁ '' μ.support) ≤
        τ - minimumRisk α c H 0 s₁ q := by
  have hμ : μ ≠ 0 := by
    intro hz
    have hmass : μ univ = 1 := measure_univ
    simp [hz] at hmass
  exact uniform_margin α c H s₁ μ.support μ.isClosed_support (μ.nonempty_support hμ) τ hstrict

/-- The range statement records that the compact recursion is the original unrestricted CVaR. -/
theorem source_risk_recursion (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1)
    (π : Policy S A) (q : Kernel S A) (n h : ℕ) (s : S) :
    risk α c π q (n+1) h s = primalCVaR α (joint (π h s) (q s))
      (fun x => c h s x.1 + risk α c π q n (h+1) x.2) :=
  risk_step_eq_primal α hα hα1 c hc π q n h s

end
end Paper36.Prior
