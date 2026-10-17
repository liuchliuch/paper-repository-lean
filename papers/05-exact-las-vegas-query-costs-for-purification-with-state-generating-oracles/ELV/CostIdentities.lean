import ELV.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# Closed-form cost identities of Theorem 1.1 (algebraic layer)

These equalities are the numerical content of (1.1)–(1.2) and (3.5)–(3.10).
They do **not** by themselves constitute Theorem 1.1; the operational
transducer quantifiers live in `ELV.Oracle` and `ELV.Main`.
-/

noncomputable section

namespace ELV

namespace Cost

open ELV.Gap

/-- Unrestricted state-generating cost value `1/(2δ)`. -/
def sgValue (g : Gap) : ℝ := 1 / (2 * g.δ)

/-- Ray-restricted admissible cost value `1/(1-μ)`. -/
def admValue (g : Gap) : ℝ := 1 / (1 - g.mu)

/-- Algebraic reformulation of the admissible cost used in (1.2). -/
def admValueAlt (g : Gap) : ℝ := (1 + g.mu) / (4 * g.δ ^ 2)

theorem sgValue_eq (g : Gap) : sgValue g = 1 / (2 * g.δ) := rfl

theorem admValue_eq (g : Gap) : admValue g = 1 / (1 - g.mu) := rfl

theorem sgValue_pos (g : Gap) : 0 < sgValue g := by
  unfold sgValue
  have h : 0 < 2 * g.δ := by
    have := g.δ_pos
    positivity
  exact one_div_pos.mpr h

theorem admValue_pos (g : Gap) : 0 < admValue g := by
  unfold admValue
  exact one_div_pos.mpr g.one_sub_mu_pos

/-- The two printed forms of `C_adm` coincide (equation (1.2)). -/
theorem admValue_eq_alt (g : Gap) : admValue g = admValueAlt g := by
  unfold admValue admValueAlt
  have h4 : (4 : ℝ) * g.δ ^ 2 = (1 - g.mu) * (1 + g.mu) := g.four_δ_sq_eq
  have hden : 1 - g.mu ≠ 0 := g.one_sub_mu_ne_zero
  have hne : (4 : ℝ) * g.δ ^ 2 ≠ 0 := by
    have := g.δ_pos
    positivity
  -- Cross-multiply: 1 / (1-μ) = (1+μ) / (4δ²)
  apply (div_eq_div_iff hden hne).2
  -- goal: 1 * (4 δ²) = (1+μ) * (1-μ)
  nlinarith

/-- `|1-2p| = 2|p-1/2|`. -/
theorem abs_one_sub_two_p (p : ℝ) : |1 - 2 * p| = 2 * |p - 1 / 2| := by
  have h1 : 1 - 2 * p = 2 * (1 / 2 - p) := by ring
  have h2 : p - 1 / 2 = -(1 / 2 - p) := by ring
  rw [h1, h2, abs_neg, abs_mul, abs_two]

/-- Phase-purifier cost identity (3.10). -/
theorem phase_cost_eq (p : ℝ) :
    1 / |1 - 2 * p| = 1 / (2 * |p - 1 / 2|) := by
  rw [abs_one_sub_two_p]

/-- On the promised family the phase cost is at most `1/(2δ)`. -/
theorem phase_cost_le (p : ℝ) (δ : ℝ) (hδ : 0 < δ) (h : δ ≤ |p - 1 / 2|) :
    1 / (2 * |p - 1 / 2|) ≤ 1 / (2 * δ) := by
  have h2 : 0 < 2 * |p - 1 / 2| := by
    have : |p - 1 / 2| ≠ 0 := by
      intro hc
      have : δ ≤ (0 : ℝ) := by rw [← hc]; exact h
      linarith
    positivity
  have h3 : 0 < 2 * δ := by positivity
  have hle : 2 * δ ≤ 2 * |p - 1 / 2| := by nlinarith
  exact one_div_le_one_div_of_le h3 hle

end Cost

/-- `γ² / (1-γ²) = p/(1-2p)` when `γ² = p/(1-p)` and `p < 1/2`. -/
theorem gamma_sq_div (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1 / 2) :
    p / (1 - p) / (1 - p / (1 - p)) = p / (1 - 2 * p) := by
  have h1 : 0 < 1 - p := by linarith
  have h2 : 0 < 1 - 2 * p := by linarith
  have hden : 1 - p / (1 - p) = (1 - 2 * p) / (1 - p) := by
    field_simp [h1.ne']
    ring
  rw [hden]
  field_simp [h1.ne', h2.ne']

/-- `γ^{-2} / (1-γ^{-2}) = (1-p)/(2p-1)` when `p > 1/2`. -/
theorem gamma_inv_sq_div (p : ℝ) (hp1 : 1 / 2 < p) (hp2 : p < 1) :
    (p / (1 - p))⁻¹ / (1 - (p / (1 - p))⁻¹) = (1 - p) / (2 * p - 1) := by
  have h1 : 0 < 1 - p := by linarith
  have h2 : 0 < 2 * p - 1 := by linarith
  have hp0 : 0 < p := by linarith
  have hγn : p / (1 - p) ≠ 0 := by positivity
  have hinv : (p / (1 - p))⁻¹ = (1 - p) / p := by
    field_simp [hγn, hp0.ne']
  have hden : 1 - (p / (1 - p))⁻¹ = (2 * p - 1) / p := by
    rw [hinv]
    field_simp [hp0.ne']
    ring
  rw [hden, hinv]
  field_simp [hp0.ne', h2.ne']

/-- Total line-walk cost for `p < 1/2`. -/
theorem line_total_cost_low (p : ℝ) (hp1 : p < 1 / 2) :
    1 + 2 * (p / (1 - 2 * p)) = 1 / (1 - 2 * p) := by
  have h2 : 0 < 1 - 2 * p := by linarith
  field_simp [h2.ne']
  ring

/-- Total line-walk cost for `p > 1/2`. -/
theorem line_total_cost_high (p : ℝ) (hp1 : 1 / 2 < p) :
    1 + 2 * ((1 - p) / (2 * p - 1)) = 1 / (2 * p - 1) := by
  have h2 : 0 < 2 * p - 1 := by linarith
  field_simp [h2.ne']
  ring

/-- Boundary identity `μ² + (2δ)² = 1`. -/
theorem mu_two_δ_norm (g : Gap) : g.mu ^ 2 + (2 * g.δ) ^ 2 = 1 := by
  nlinarith [g.mu_sq]

end ELV
