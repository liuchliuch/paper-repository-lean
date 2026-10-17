import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# Parameter choices and decision bias (paper Section 4.3)

Choose `lam = 1/(100 J² K³)`, `δ = lam/3`, `ε = lam/(200 K)`.
Equation (22) left-hand side: `(lam²/2) J² K² + ε ≤ lam/(100 K)`.
-/

noncomputable section

namespace Paper25

/-- Regularization scale `lam = 1/(100 J² K³)`. -/
def biasLam (J K : ℝ) : ℝ := 1 / (100 * J ^ 2 * K ^ 3)

/-- Spectral filter width `δ = lam/3`. -/
def biasDelta (J K : ℝ) : ℝ := biasLam J K / 3

/-- Filter accuracy `ε = lam/(200 K)`. -/
def biasEps (J K : ℝ) : ℝ := biasLam J K / (200 * K)

/-- Decision gap `γ = lam / (2^{k+3} √K)`. -/
def biasGamma (lam K k : ℝ) : ℝ := lam / (2 ^ (k + 3) * Real.sqrt K)

lemma biasLam_pos {J K : ℝ} (hJ : 0 < J) (hK : 0 < K) : 0 < biasLam J K := by
  unfold biasLam
  positivity

lemma biasGamma_pos {lam K k : ℝ} (hlam : 0 < lam) (hK : 0 < K) :
    0 < biasGamma lam K k := by
  unfold biasGamma
  have hs : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  positivity

/-- Explicit forms of the chosen scales. -/
lemma biasLam_eq (J K : ℝ) : biasLam J K = 1 / (100 * J ^ 2 * K ^ 3) := rfl

lemma biasEps_eq {J K : ℝ} (hJ : J ≠ 0) (hK : K ≠ 0) :
    biasEps J K = 1 / (20000 * J ^ 2 * K ^ 4) := by
  unfold biasEps biasLam
  have hden : (100:ℝ) * J ^ 2 * K ^ 3 ≠ 0 := by
    positivity
  field_simp [hden, hJ, hK]
  ring

/-- The error budget (22) from (19): with the chosen parameters,
`(lam²/2) J² K² + ε ≤ lam/(100 K)`. -/
theorem bias_error_budget (J K : ℝ) (hJ : 1 ≤ J) (hK : 1 ≤ K) :
    (biasLam J K ^ 2 / 2) * J ^ 2 * K ^ 2 + biasEps J K ≤ biasLam J K / (100 * K) := by
  have hJ0 : (0:ℝ) < J := lt_of_lt_of_le (by norm_num) hJ
  have hK0 : (0:ℝ) < K := lt_of_lt_of_le (by norm_num) hK
  have hden : (100:ℝ) * J ^ 2 * K ^ 3 ≠ 0 := by positivity
  have hA : (biasLam J K ^ 2 / 2) * J ^ 2 * K ^ 2 = 1 / (20000 * J ^ 2 * K ^ 4) := by
    unfold biasLam
    have : (1 / (100 * J ^ 2 * K ^ 3)) ^ 2 = 1 / ((100 * J ^ 2 * K ^ 3) ^ 2) := by
      rw [one_div_pow]
    rw [this]
    have h2 : (100 * J ^ 2 * K ^ 3) ^ 2 = 100 * J ^ 2 * K ^ 3 * (100 * J ^ 2 * K ^ 3) := by ring
    rw [h2]
    field_simp [hden]
    ring
  have hB : biasEps J K = 1 / (20000 * J ^ 2 * K ^ 4) :=
    biasEps_eq (ne_of_gt hJ0) (ne_of_gt hK0)
  have hC : biasLam J K / (100 * K) = 1 / (10000 * J ^ 2 * K ^ 4) := by
    unfold biasLam
    field_simp [hden]
    ring
  rw [hA, hB, hC]
  have hsum : (1:ℝ) / (20000 * J ^ 2 * K ^ 4) + 1 / (20000 * J ^ 2 * K ^ 4)
      = 1 / (10000 * J ^ 2 * K ^ 4) := by
    have hpos : (0:ℝ) < 20000 * J ^ 2 * K ^ 4 := by positivity
    have hpos2 : (0:ℝ) < 10000 * J ^ 2 * K ^ 4 := by positivity
    have h : (1:ℝ) / (20000 * J ^ 2 * K ^ 4) + 1 / (20000 * J ^ 2 * K ^ 4)
        = (2:ℝ) / (20000 * J ^ 2 * K ^ 4) := by
      have hne : (20000:ℝ) * J ^ 2 * K ^ 4 ≠ 0 := ne_of_gt hpos
      field_simp [hne]
      ring
    have h2 : (2:ℝ) / (20000 * J ^ 2 * K ^ 4) = 1 / (10000 * J ^ 2 * K ^ 4) := by
      have hne : (20000:ℝ) * J ^ 2 * K ^ 4 ≠ 0 := ne_of_gt hpos
      have hne2 : (10000:ℝ) * J ^ 2 * K ^ 4 ≠ 0 := ne_of_gt hpos2
      field_simp [hne, hne2]
      ring
    exact h.trans h2
  rw [hsum]

/-- Core numerical inequality used for the decision gap. -/
lemma one_third_gap : (1 / 3 : ℝ) - 1 / 100 > 1 / 4 := by norm_num

/-- Weak form of (22): the budget implies the `√K` bound. -/
theorem bias_eq22 (lam K e a : ℝ)
    (hlam : 0 < lam) (hK : 1 ≤ K)
    (herr : |a - lam * e / Real.sqrt K| ≤ lam / (100 * K)) :
    |a - lam * e / Real.sqrt K| ≤ lam / (100 * Real.sqrt K) := by
  have hK0 : (0:ℝ) < K := lt_of_lt_of_le (by norm_num) hK
  have hs : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK0
  have hsK : Real.sqrt K ≤ K := by
    nlinarith [sq_nonneg (Real.sqrt K - 1), Real.sq_sqrt (le_of_lt hK0), Real.sqrt_nonneg K]
  have h3 : (100:ℝ) * Real.sqrt K ≤ 100 * K := by nlinarith
  exact le_trans herr (div_le_div_of_nonneg_left (le_of_lt hlam) (by positivity) h3)

end Paper25
