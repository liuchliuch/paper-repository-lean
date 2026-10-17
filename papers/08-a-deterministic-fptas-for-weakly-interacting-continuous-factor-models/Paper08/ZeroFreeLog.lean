import Paper08.ZeroFree
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# Constructing the normalized analytic logarithm on a nonzero disk

This is the analytic implication following Lemma 2.1. It takes non-vanishing
as an explicit hypothesis of a generic theorem and proves logarithm existence;
it does not assert or assume Barvinok's theorem as an axiom or model field.
-/

noncomputable section

open scoped Topology
open Set Metric

namespace Paper08
namespace ZeroFree

/-- A holomorphic function on a disk about zero, with `f 0 = 1` and without
 zeros in that disk, has a normalized holomorphic logarithm there. The proof
 constructs a primitive of `f'/f` and proves the exponential identity. -/
theorem exists_normalized_log {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hf₀ : f 0 = 1)
    (hne : ∀ z ∈ ball 0 R, f z ≠ 0) :
    ∃ L : ℂ → ℂ, L 0 = 0 ∧ DifferentiableOn ℂ L (ball 0 R) ∧
      (∀ z ∈ ball 0 R, HasDerivAt L (logDeriv f z) z) ∧
      (∀ z ∈ ball 0 R, Complex.exp (L z) = f z) := by
  have hld : DifferentiableOn ℂ (logDeriv f) (ball 0 R) :=
    (hf.deriv isOpen_ball).div hf hne
  obtain ⟨g, hg⟩ := hld.isExactOn_ball
  let L : ℂ → ℂ := fun z => g z - g 0
  have hL₀ : L 0 = 0 := sub_self _
  have hL : ∀ z ∈ ball 0 R, HasDerivAt L (logDeriv f z) z := by
    intro z hz
    exact (hg z hz).sub_const (g 0)
  have hLdiff : DifferentiableOn ℂ L (ball 0 R) :=
    fun z hz => (hL z hz).differentiableAt.differentiableWithinAt
  have hediff : DifferentiableOn ℂ (fun z => Complex.exp (L z)) (ball 0 R) :=
    fun z hz => ((Complex.hasDerivAt_exp (L z)).comp z
      (hL z hz)).differentiableAt.differentiableWithinAt
  have held : EqOn (logDeriv f) (logDeriv (fun z => Complex.exp (L z))) (ball 0 R) := by
    intro z hz
    have he := ((Complex.hasDerivAt_exp (L z)).comp z (hL z hz)).deriv
    change logDeriv f z = deriv (Complex.exp ∘ L) z / Complex.exp (L z)
    rw [he]
    exact (mul_div_cancel_left₀ (logDeriv f z) (Complex.exp_ne_zero (L z))).symm
  obtain ⟨c, _, hc⟩ := (logDeriv_eqOn_iff hf hediff isOpen_ball
    (convex_ball (0 : ℂ) R).isPreconnected
    (fun z _ => Complex.exp_ne_zero (L z)) hne).mp held
  have hzero : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
  have hc₁ : c = 1 := by
    have hc₀ := hc hzero
    simpa [hf₀, hL₀] using hc₀.symm
  refine ⟨L, hL₀, hLdiff, hL, ?_⟩
  intro z hz
  have heq := hc hz
  simpa [hc₁] using heq.symm

/-- The derivative part determines the normalized logarithm uniquely on the
 disk. This makes its coefficients independent of the chosen primitive. -/
theorem normalized_log_unique {f L₁ L₂ : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (h₁ : ∀ z ∈ ball 0 R, HasDerivAt L₁ (logDeriv f z) z)
    (h₂ : ∀ z ∈ ball 0 R, HasDerivAt L₂ (logDeriv f z) z)
    (h₁₀ : L₁ 0 = 0) (h₂₀ : L₂ 0 = 0) :
    EqOn L₁ L₂ (ball 0 R) := by
  apply isOpen_ball.eqOn_of_deriv_eq (convex_ball (0 : ℂ) R).isPreconnected
    (fun z hz => (h₁ z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (h₂ z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (h₁ z hz).deriv.trans (h₂ z hz).deriv.symm)
    (mem_ball_self hR)
  exact h₁₀.trans h₂₀.symm

/-- Application to the actual model integral. The open disk non-vanishing
 obligation remains visible; the common radius must be proved separately. -/
theorem exists_normalized_log_Q {n r : ℕ} {ι : Type*} (E : ι → Factor n r)
    (B : Finset ι) {q K R : ℝ} (hq : 0 ≤ q) (hR : 0 < R)
    (hE : ∀ i ∈ B, (E i).RangeOk q) (hLip : ∀ i ∈ B, (E i).LipOk K)
    (hne : ∀ z ∈ ball 0 R, Q E B z ≠ 0) :
    ∃ L : ℂ → ℂ, L 0 = 0 ∧ DifferentiableOn ℂ L (ball 0 R) ∧
      (∀ z ∈ ball 0 R, HasDerivAt L (logDeriv (Q E B) z) z) ∧
      (∀ z ∈ ball 0 R, Complex.exp (L z) = Q E B z) :=
  exists_normalized_log hR (differentiable_Q E B hq hE hLip).differentiableOn
    (Q_zero E B) hne

end ZeroFree
end Paper08
