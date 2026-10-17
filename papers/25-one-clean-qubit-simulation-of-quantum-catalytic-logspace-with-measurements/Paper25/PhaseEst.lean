import Paper25.Filter
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Appendix B: phase-estimation scalar bounds

Jordan's inequality `2Δ ≤ |sin(πΔ)|` is in `Paper25.Filter`. This file records
the scalar tail comparison `(1/2)(1/a² + 1/a) ≤ 1/a` for `a ≥ 1` used in the
failure-probability estimate of Appendix B.
-/

noncomputable section

namespace Paper25

/-- Circular distance of `x` from the nearest integer. -/
def circDist (x : ℝ) : ℝ := |x - round x|

lemma circDist_nonneg (x : ℝ) : 0 ≤ circDist x := abs_nonneg _

lemma circDist_le_half (x : ℝ) : circDist x ≤ 1 / 2 :=
  abs_sub_round x

/-- Scalar tail comparison used in Appendix B:
for `a ≥ 1`, `(1/2) (1/a² + 1/a) ≤ 1/a`. -/
theorem pe_tail_scalar (a : ℝ) (ha : 1 ≤ a) :
    (1 / 2) * (1 / a ^ 2 + 1 / a) ≤ 1 / a := by
  have hpos : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have h1 : 1 / a ^ 2 ≤ 1 / a := by
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < a ^ 2) hpos]
    nlinarith [sq_nonneg (a - 1)]
  nlinarith [one_div_pos.mpr hpos]

/-- Consequence of Jordan: `1 / |sin(πΔ)| ≤ 1 / (2Δ)` for `Δ ∈ (0, 1/2]`. -/
theorem pe_inv_sin_le (Δ : ℝ) (h0 : 0 < Δ) (h1 : Δ ≤ 1 / 2) :
    1 / |Real.sin (Real.pi * Δ)| ≤ 1 / (2 * Δ) := by
  have h : 2 * Δ ≤ |Real.sin (Real.pi * Δ)| :=
    Paper25.sin_pi_ge_two_mul Δ (le_of_lt h0) h1
  have hpos : 0 < 2 * Δ := by positivity
  have hsin : 0 < |Real.sin (Real.pi * Δ)| := lt_of_lt_of_le hpos h
  exact one_div_le_one_div_of_le hpos h

end Paper25
