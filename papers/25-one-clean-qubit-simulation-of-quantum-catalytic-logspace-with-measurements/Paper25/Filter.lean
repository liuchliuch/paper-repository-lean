import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/-!
# Coherent spectral filter (paper Lemma 5, analytic core)

The scalar filter `f_δ(t) = δ t / (t² + δ²)` satisfies `|f_δ(t)| ≤ 1/2` and
`|f_δ'(t)| ≤ 1/δ`. The periodic version `g_δ(θ) = f_δ(cos θ)` obeys the same
bounds. Jordan's inequality gives `2Δ ≤ |sin(πΔ)|` for `Δ ∈ [0, 1/2]`.
-/

noncomputable section

namespace Paper25

/-- Scalar spectral filter `f_δ(t) = δ t / (t² + δ²)`. -/
def filterFn (δ t : ℝ) : ℝ := δ * t / (t ^ 2 + δ ^ 2)

/-- Periodic filter `g_δ(θ) = f_δ(cos θ)`. -/
def filterG (δ θ : ℝ) : ℝ := filterFn δ (Real.cos θ)

/-- Fundamental bound `2 δ |t| ≤ t² + δ²`. -/
lemma two_mul_abs_le (δ t : ℝ) : 2 * δ * |t| ≤ t ^ 2 + δ ^ 2 := by
  have h1 : 0 ≤ (|t| - δ) ^ 2 := sq_nonneg _
  have h2 : (|t| - δ) ^ 2 = |t| ^ 2 - 2 * δ * |t| + δ ^ 2 := by ring
  have h3 : |t| ^ 2 = t ^ 2 := sq_abs t
  nlinarith [abs_nonneg t]

/-- Filter range bound `|δ t / (t² + δ²)| ≤ 1/2`. -/
theorem filter_range_bound (δ t : ℝ) (hδ : 0 < δ) :
    |filterFn δ t| ≤ 1 / 2 := by
  unfold filterFn
  have hden : 0 < t ^ 2 + δ ^ 2 := by
    nlinarith [sq_pos_of_ne_zero (ne_of_gt hδ), sq_nonneg t]
  have h : 2 * δ * |t| ≤ t ^ 2 + δ ^ 2 := two_mul_abs_le δ t
  have habs : |δ * t| = δ * |t| := by
    rw [abs_mul, abs_of_pos hδ]
  rw [abs_div, habs, abs_of_pos hden]
  rw [div_le_iff₀ hden]
  nlinarith [abs_nonneg t, abs_nonneg δ]

/-- Filter derivative bound `|δ(δ²-t²)/(t²+δ²)²| ≤ 1/δ`. -/
theorem filter_deriv_bound (δ t : ℝ) (hδ : 0 < δ) :
    |δ * (δ ^ 2 - t ^ 2) / (t ^ 2 + δ ^ 2) ^ 2| ≤ 1 / δ := by
  have hden : 0 < t ^ 2 + δ ^ 2 := by
    nlinarith [sq_pos_of_ne_zero (ne_of_gt hδ), sq_nonneg t]
  have hsq : 0 < (t ^ 2 + δ ^ 2) ^ 2 := by positivity
  have h1 : |δ * (δ ^ 2 - t ^ 2)| = δ * |δ ^ 2 - t ^ 2| := by
    rw [abs_mul, abs_of_pos hδ]
  have h2 : |δ ^ 2 - t ^ 2| ≤ t ^ 2 + δ ^ 2 := by
    rcases le_or_gt 0 (δ ^ 2 - t ^ 2) with h | h
    · rw [abs_of_nonneg h]
      nlinarith [sq_nonneg t]
    · rw [abs_of_neg h]
      nlinarith [sq_nonneg δ]
  have h3 : δ * |δ ^ 2 - t ^ 2| / (t ^ 2 + δ ^ 2) ^ 2
      ≤ δ * (t ^ 2 + δ ^ 2) / (t ^ 2 + δ ^ 2) ^ 2 := by
    apply div_le_div_of_nonneg_right
    · exact mul_le_mul_of_nonneg_left h2 (le_of_lt hδ)
    · exact le_of_lt hsq
  have h4 : δ * (t ^ 2 + δ ^ 2) / (t ^ 2 + δ ^ 2) ^ 2 = δ / (t ^ 2 + δ ^ 2) := by
    have hne : (t ^ 2 + δ ^ 2) ^ 2 ≠ 0 := ne_of_gt hsq
    field_simp [hne, hden.ne']
  have h5 : δ / (t ^ 2 + δ ^ 2) ≤ 1 / δ := by
    rw [div_le_div_iff₀ hden (by positivity : (0:ℝ) < δ)]
    nlinarith [mul_pos hδ hden]
  have h6 : |(t ^ 2 + δ ^ 2) ^ 2| = (t ^ 2 + δ ^ 2) ^ 2 := abs_of_pos hsq
  rw [abs_div, h1, h6]
  calc δ * |δ ^ 2 - t ^ 2| / (t ^ 2 + δ ^ 2) ^ 2
      ≤ δ * (t ^ 2 + δ ^ 2) / (t ^ 2 + δ ^ 2) ^ 2 := h3
    _ = δ / (t ^ 2 + δ ^ 2) := h4
    _ ≤ 1 / δ := h5

/-- Periodic filter range. -/
theorem filterG_range_bound (δ θ : ℝ) (hδ : 0 < δ) :
    |filterG δ θ| ≤ 1 / 2 :=
  filter_range_bound δ (Real.cos θ) hδ

/-- `2Δ ≤ |sin(πΔ)|` for `Δ ∈ [0, 1/2]` (Jordan). -/
theorem sin_pi_ge_two_mul (Δ : ℝ) (h0 : 0 ≤ Δ) (h1 : Δ ≤ 1 / 2) :
    2 * Δ ≤ |Real.sin (Real.pi * Δ)| := by
  have hx : 0 ≤ Real.pi * Δ := by nlinarith [Real.pi_pos, h0]
  have hy : Real.pi * Δ ≤ Real.pi / 2 := by nlinarith [Real.pi_pos, h1]
  have h5 : 2 / Real.pi * (Real.pi * Δ) ≤ Real.sin (Real.pi * Δ) :=
    Real.mul_le_sin hx hy
  have h4 : (2 / Real.pi) * (Real.pi * Δ) = 2 * Δ := by
    have hne : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp [hne]
  rw [h4] at h5
  have h6 : 0 ≤ Real.sin (Real.pi * Δ) := by nlinarith [h5, Real.pi_pos, h0]
  rw [abs_of_nonneg h6]
  exact h5

end Paper25
