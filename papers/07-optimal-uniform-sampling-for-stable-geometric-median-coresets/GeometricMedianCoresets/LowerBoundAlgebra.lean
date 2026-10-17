import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import GeometricMedianCoresets.Basic

/-!
# Lower-bound algebra (paper §3, Theorem 1.2(ii))

Algebraic inequalities of the two-cluster construction.
The complete distinct-point construction and without-replacement probability
statement are proved in `DistinctClusters` and `MainLower`.
-/

noncomputable section

namespace GeometricMedianCoresets
namespace LowerBound

/-- Gap of population preferences (paper §3):
`p_B - (1+17ε)p_A ≥ (3/2)ε + 85 ε²` when `10ε ≤ θ`, `θ ≤ 11ε`, `ε ≤ 1/100`. -/
theorem pref_gap {ε θ pA pB : ℝ}
    (hε : 0 < ε) (hε' : ε ≤ 1/100)
    (hθlo : 10 * ε ≤ θ) (hθhi : θ ≤ 11 * ε)
    (hp : pA = (1 - θ) / 2 ∧ pB = (1 + θ) / 2) :
    pB - (1 + 17 * ε) * pA ≥ (3/2) * ε + 85 * ε ^ 2 := by
  obtain ⟨hpA, hpB⟩ := hp
  rw [hpA, hpB]
  have h1 : (1 + θ) / 2 - (1 + 17 * ε) * ((1 - θ) / 2)
      = θ - (17 * ε / 2) * (1 - θ) := by
    ring
  rw [h1]
  have hθθ : 1 - θ ≤ 1 - 10 * ε := by nlinarith
  have h7 : (17 * ε / 2) * (1 - θ) ≤ (17 * ε / 2) * (1 - 10 * ε) := by
    exact mul_le_mul_of_nonneg_left hθθ (by nlinarith)
  have h8 : θ - (17 * ε / 2) * (1 - θ)
      ≥ 10 * ε - (17 * ε / 2) * (1 - 10 * ε) := by
    nlinarith [hθlo]
  have h9 : 10 * ε - (17 * ε / 2) * (1 - 10 * ε) = (3/2) * ε + 85 * ε ^ 2 := by
    ring
  nlinarith [h8, h9]

/-- Sample majority event reverses the comparison (paper §3):
`1/2 + ρ ≤ (1+ε)(1/2)(1-ρ)` when `ρ(3+ε) ≤ ε`. -/
theorem majority_reversal {ε ρ : ℝ}
    (hε : 0 < ε)
    (hρok : ρ * (3 + ε) ≤ ε) :
    1/2 + ρ ≤ (1 + ε) * (1/2 * (1 - ρ)) := by
  nlinarith [hρok, hε, mul_nonneg (le_of_lt hε) (le_of_lt hε)]

/-- For `ρ = ε²/100` and `0 < ε < 1/4`, one has `ρ(3+ε) ≤ ε`. -/
theorem rho_ok {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1/4) :
    (ε ^ 2 / 100) * (3 + ε) ≤ ε := by
  have hlt1 : ε < 1 := by linarith
  have hprod : ε * (3 + ε) ≤ 4 := by
    have h1 : ε * (3 + ε) ≤ 1 * (3 + 1) := by nlinarith
    nlinarith
  have hstep : ε ^ 2 / 100 * (3 + ε) = ε * (ε * (3 + ε) / 100) := by
    field_simp
  rw [hstep]
  have hfrac : ε * (3 + ε) / 100 ≤ 4 / 100 := by
    exact div_le_div_of_nonneg_right hprod (by norm_num)
  have h4 : (4:ℝ) / 100 < 1 := by norm_num
  nlinarith [le_of_lt hε, hfrac, h4]

end LowerBound
end GeometricMedianCoresets
