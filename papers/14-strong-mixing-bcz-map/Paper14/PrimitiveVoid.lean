import Paper14.SieveVariance
import Mathlib.Analysis.Normed.Group.Tannery
/-!
# Lemma 5: primitive-point void probability

Paper anchors: Thmtheorem5, E12, E20/E21.
-/
open MeasureTheory Filter Topology Set
open scoped ENNReal

noncomputable section
namespace Paper14

/-- Lemma 5 is `Lemma5Statement` from `Paper14.Basic`. -/
def Lemma5Claim : Prop := Lemma5Statement

/-- Paper E20 algebraic form: void probability RHS
`((K:ℝ)²)⁻¹ + 8M/β + 2ε Q S_P / β`. -/
def voidRHS (K M Q P : ℕ) (ε β : ℝ) : ℝ :=
  ((K : ℝ) ^ 2)⁻¹ + 8 * M / β + 2 * ε * Q * SP P / β

lemma voidRHS_nonneg (K M Q P : ℕ) {ε β : ℝ}
    (hε : 0 ≤ ε) (hβ : 0 < β) : 0 ≤ voidRHS K M Q P ε β := by
  unfold voidRHS
  have h1 : (0:ℝ) ≤ ((K:ℝ) ^ 2)⁻¹ := by positivity
  have h2 : (0:ℝ) ≤ 8 * (M:ℝ) / β := by positivity
  have h3 : 0 ≤ SP P := SP_nonneg P
  have h4 : (0:ℝ) ≤ 2 * ε * (Q:ℝ) * SP P / β := by positivity
  linarith

/-- The unsieved prime tail in (19)--(21) tends to zero. -/
theorem SP_tendsto_zero : Tendsto SP atTop (𝓝 0) := by
  have hpoint (ℓ : ℕ) : Tendsto
      (fun P : ℕ => if P < ℓ ∧ Nat.Prime ℓ then (ℓ : ℝ)⁻¹ ^ 2 else 0)
      atTop (𝓝 (0 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop ℓ] with P hP
    simp [not_lt.mpr hP]
  have hdom : ∀ P ℓ : ℕ,
      ‖(if P < ℓ ∧ Nat.Prime ℓ then (ℓ : ℝ)⁻¹ ^ 2 else 0)‖ ≤ ((ℓ : ℝ)^2)⁻¹ := by
    intro P ℓ
    split_ifs
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ((ℓ : ℝ)⁻¹)), inv_pow]
    · simp
  change Tendsto (fun P : ℕ => ∑' ℓ : ℕ,
    if P < ℓ ∧ Nat.Prime ℓ then (ℓ : ℝ)⁻¹ ^ 2 else 0) atTop (𝓝 0)
  simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence summable_invSq hpoint
    (Eventually.of_forall hdom)

end Paper14
