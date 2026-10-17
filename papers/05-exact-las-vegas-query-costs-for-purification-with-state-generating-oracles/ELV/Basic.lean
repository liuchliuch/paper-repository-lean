import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# Parameters of the purification cost formulas (paper 05)

Throughout, `δ` is a fixed gap with `0 < δ < 1/2`.  The boundary answer
probabilities `ℓ, h`, their geometric-mean factor `μ = √(1-4δ²)`, and the
reciprocal-rescaling factor `κ` are the only numerical data used by the
closed-form costs of Theorem 1.1.
-/

noncomputable section

namespace ELV

/-- Gap parameter of the promised family. -/
structure Gap where
  δ : ℝ
  δ_pos : 0 < δ
  δ_lt_half : δ < 1 / 2

namespace Gap

variable (g : Gap)

/-- Low boundary answer probability `ℓ = 1/2 - δ`. -/
def ell : ℝ := 1 / 2 - g.δ

/-- High boundary answer probability `h = 1/2 + δ`. -/
def high : ℝ := 1 / 2 + g.δ

/-- Overlap parameter `μ = √(1 - 4δ²)`. -/
def mu : ℝ := Real.sqrt (1 - 4 * g.δ ^ 2)

/-- Reciprocal-rescaling factor `κ = (ℓ/h)^{1/4}`. -/
def kappa : ℝ := (g.ell / g.high) ^ (1 / 4 : ℝ)

lemma two_δ_lt_one : 2 * g.δ < 1 := by
  linarith [g.δ_lt_half]

lemma four_δ_sq_lt_one : 4 * g.δ ^ 2 < 1 := by
  have h := g.two_δ_lt_one
  nlinarith [g.δ_pos]

lemma one_sub_four_δ_sq_pos : 0 < 1 - 4 * g.δ ^ 2 := by
  linarith [g.four_δ_sq_lt_one]

lemma mu_pos : 0 < g.mu := by
  unfold Gap.mu
  exact Real.sqrt_pos.mpr g.one_sub_four_δ_sq_pos

lemma mu_nonneg : 0 ≤ g.mu := g.mu_pos.le

lemma mu_lt_one : g.mu < 1 := by
  have h : Real.sqrt (1 - 4 * g.δ ^ 2) < Real.sqrt (1 : ℝ) := by
    refine Real.sqrt_lt_sqrt ?_ ?_
    · exact le_of_lt g.one_sub_four_δ_sq_pos
    · nlinarith [g.δ_pos]
  have h1 : Real.sqrt (1 : ℝ) = 1 := Real.sqrt_one
  unfold Gap.mu
  linarith [h, h1]

lemma mu_sq : g.mu ^ 2 = 1 - 4 * g.δ ^ 2 := by
  unfold Gap.mu
  exact Real.sq_sqrt (le_of_lt g.one_sub_four_δ_sq_pos)

lemma mu_sq_add : g.mu ^ 2 + 4 * g.δ ^ 2 = 1 := by
  linarith [g.mu_sq]

lemma ell_pos : 0 < g.ell := by
  unfold Gap.ell
  linarith [g.δ_lt_half]

lemma ell_nonneg : 0 ≤ g.ell := g.ell_pos.le

lemma high_pos : 0 < g.high := by
  unfold Gap.high
  linarith [g.δ_pos]

lemma high_lt_one : g.high < 1 := by
  unfold Gap.high
  linarith [g.δ_lt_half]

lemma high_nonneg : 0 ≤ g.high := g.high_pos.le

lemma ell_lt_high : g.ell < g.high := by
  unfold Gap.ell Gap.high
  linarith [g.δ_pos]

lemma ell_add_high : g.ell + g.high = 1 := by
  unfold Gap.ell Gap.high
  ring

lemma ell_mul_high : g.ell * g.high = 1 / 4 - g.δ ^ 2 := by
  unfold Gap.ell Gap.high
  ring

lemma ell_mul_high_pos : 0 < g.ell * g.high := mul_pos g.ell_pos g.high_pos

lemma mu_eq_two_sqrt : g.mu = 2 * Real.sqrt (g.ell * g.high) := by
  have hpos : 0 < g.ell * g.high := g.ell_mul_high_pos
  have h2 : 0 ≤ 2 * Real.sqrt (g.ell * g.high) := by positivity
  have hsq : (2 * Real.sqrt (g.ell * g.high)) ^ 2 = g.mu ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (le_of_lt hpos), g.mu_sq, g.ell_mul_high]
    ring
  have hne : 2 ≠ 0 := by norm_num
  have := (pow_left_inj₀ h2 g.mu_nonneg hne).mp hsq
  linarith

lemma one_sub_mu_pos : 0 < 1 - g.mu := by
  linarith [g.mu_lt_one]

lemma one_sub_mu_ne_zero : 1 - g.mu ≠ 0 := g.one_sub_mu_pos.ne'

lemma four_δ_sq_eq : 4 * g.δ ^ 2 = (1 - g.mu) * (1 + g.mu) := by
  nlinarith [g.mu_sq]

end Gap

end ELV
