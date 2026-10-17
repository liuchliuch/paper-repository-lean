import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import GeometricMedianCoresets.Basic

/-!
# Geometric and numerical inequalities (paper eq. (11), Lemma 2.6 algebra)
-/

noncomputable section

namespace GeometricMedianCoresets

/-- For `a b ≥ 0`, `2 √(a b) ≤ a + b`. -/
theorem two_sqrt_mul_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * Real.sqrt (a * b) ≤ a + b := by
  have h1 : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  have h2 : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
  have h3 : (Real.sqrt a - Real.sqrt b) ^ 2 ≥ 0 := sq_nonneg _
  have h4 : Real.sqrt a * Real.sqrt b = Real.sqrt (a * b) := by
    rw [← Real.sqrt_mul ha b]
  nlinarith [Real.mul_self_sqrt ha, Real.mul_self_sqrt hb, h4]

/-- For `ε < 5/19`, the numerical gap of Lemma 2.6 is positive. -/
theorem stability_gap_pos {ε : ℝ} (hε : 0 < ε) (hε' : ε < 5/19) :
    0 < ε * (5 - 19 * ε) := by
  have : 0 < 5 - 19 * ε := by nlinarith
  exact mul_pos hε this

/-- On `0 < ε < 1/4`, one has `ε < 5/19`. -/
theorem eps_lt_five_nineteenth {ε : ℝ} (_hε : 0 < ε) (hε' : ε < 1/4) :
    ε < 5/19 := by
  have h : (1/4 : ℝ) < 5/19 := by norm_num
  exact lt_trans hε' h

/-- Algebraic step of Lemma 2.6. -/
theorem transfer_stability {ε fx fy : ℝ}
    (hε : 0 < ε) (hε' : ε < 5/19)
    (h : (1 - ε) * fx ≤ (1 + 11 * ε + 2 * ε ^ 2) * fy)
    (hfy : 0 ≤ fy) :
    fx ≤ (1 + 17 * ε) * fy := by
  have h1e : 0 < 1 - ε := by nlinarith
  by_cases hy : fy = 0
  · subst hy
    have : (1 - ε) * fx ≤ 0 := by nlinarith
    have : fx ≤ 0 := by nlinarith
    nlinarith
  · have hfy' : 0 < fy := lt_of_le_of_ne hfy (Ne.symm hy)
    have hgap : 0 < ε * (5 - 19 * ε) := stability_gap_pos hε hε'
    have hexpand :
        (1 + 17 * ε) * (1 - ε) - (1 + 11 * ε + 2 * ε ^ 2) = ε * (5 - 19 * ε) := by
      ring
    have hdiff : (1 + 17 * ε) * (1 - ε) * fy - (1 + 11 * ε + 2 * ε ^ 2) * fy
        = ε * (5 - 19 * ε) * fy := by
      nlinarith [hexpand]
    have hstrict : (1 + 11 * ε + 2 * ε ^ 2) * fy < (1 + 17 * ε) * (1 - ε) * fy := by
      nlinarith [hgap, hfy', hdiff]
    have hlt : (1 - ε) * fx < (1 + 17 * ε) * (1 - ε) * fy :=
      lt_of_le_of_lt h hstrict
    have hrew : (1 + 17 * ε) * (1 - ε) * fy = (1 - ε) * ((1 + 17 * ε) * fy) := by
      ring
    rw [hrew] at hlt
    have hmul : fx * (1 - ε) < ((1 + 17 * ε) * fy) * (1 - ε) := by
      nlinarith [hlt]
    have hfinal : fx < (1 + 17 * ε) * fy := by
      nlinarith [hmul, h1e]
    exact le_of_lt hfinal

/-- Lemma 2.6 gap identity. -/
theorem lemma26_gap_identity (ε : ℝ) :
    (1 + 17 * ε) * (1 - ε) - (1 + 11 * ε + 2 * ε ^ 2) = ε * (5 - 19 * ε) := by
  ring

/-- Scale form of Proposition 2.4. -/
theorem prop24_scale_bound
    {m opt dist_xy fp_x fp_y mean_err : ℝ}
    (hm : 0 < m) (hopt : 0 ≤ opt)
    (hmean : mean_err ≤ 10 * opt / m)
    (_hmean0 : 0 ≤ mean_err)
    (htri : dist_xy ≤ fp_x + fp_y)
    (h2opt : 2 * opt ≤ fp_x + fp_y)
    (hs : 0 ≤ fp_x + fp_y)
    (hd : 0 ≤ dist_xy) :
    Real.sqrt (dist_xy * mean_err)
      ≤ Real.sqrt (20 / m) * ((fp_x + fp_y) / 2) := by
  have hle_prod : dist_xy * mean_err ≤ dist_xy * (10 * opt / m) :=
    mul_le_mul_of_nonneg_left hmean hd
  have h3 : dist_xy * opt ≤ (fp_x + fp_y) ^ 2 / 2 := by
    have h1 : dist_xy * opt ≤ (fp_x + fp_y) * opt :=
      mul_le_mul_of_nonneg_right htri hopt
    have h2 : opt ≤ (fp_x + fp_y) / 2 := by nlinarith
    have : (fp_x + fp_y) * opt ≤ (fp_x + fp_y) * ((fp_x + fp_y) / 2) :=
      mul_le_mul_of_nonneg_left h2 hs
    nlinarith
  have key : dist_xy * (10 * opt / m) ≤ (20 / m) * ((fp_x + fp_y) ^ 2 / 4) := by
    have h4 : dist_xy * (10 * opt / m) = 10 * (dist_xy * opt) / m := by
      field_simp
    rw [h4]
    have h5 : 10 * (dist_xy * opt) / m ≤ 10 * ((fp_x + fp_y) ^ 2 / 2) / m :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h3 (by norm_num))
        (le_of_lt hm)
    have h6 : 10 * ((fp_x + fp_y) ^ 2 / 2) / m
        = (20 / m) * ((fp_x + fp_y) ^ 2 / 4) := by
      field_simp; ring
    rw [h6] at h5
    exact h5
  have hsq : Real.sqrt (dist_xy * mean_err)
      ≤ Real.sqrt ((20 / m) * ((fp_x + fp_y) ^ 2 / 4)) :=
    Real.sqrt_le_sqrt (le_trans hle_prod key)
  have hm0 : 0 ≤ 20 / m := div_nonneg (by norm_num) (le_of_lt hm)
  have hs2 : 0 ≤ (fp_x + fp_y) ^ 2 / 4 := by positivity
  have hrew : Real.sqrt ((20 / m) * ((fp_x + fp_y) ^ 2 / 4))
      = Real.sqrt (20 / m) * Real.sqrt ((fp_x + fp_y) ^ 2 / 4) :=
    Real.sqrt_mul hm0 _
  have hinner : Real.sqrt ((fp_x + fp_y) ^ 2 / 4) = (fp_x + fp_y) / 2 := by
    have hnn : 0 ≤ (fp_x + fp_y) / 2 := by positivity
    have hsq' : ((fp_x + fp_y) / 2) ^ 2 = (fp_x + fp_y) ^ 2 / 4 := by ring
    have := Real.sqrt_sq hnn
    -- Real.sqrt ((fp+fy)^2 / 4) = Real.sqrt (((fp+fy)/2)^2) = |(fp+fy)/2| = (fp+fy)/2
    have habs : Real.sqrt ((fp_x + fp_y) ^ 2 / 4)
        = Real.sqrt (((fp_x + fp_y) / 2) ^ 2) := by
      rw [hsq']
    rw [habs, Real.sqrt_sq hnn]
  rw [hrew, hinner] at hsq
  exact hsq

/-- Deterministic implication used by Proposition 2.4 (full form). -/
theorem prop24_deterministic
    {m opt dist_xy fp_x fp_y mean_err : ℝ}
    (hm : 0 < m) (hopt : 0 ≤ opt)
    (hmean : mean_err ≤ 10 * opt / m)
    (hmean0 : 0 ≤ mean_err)
    (htri : dist_xy ≤ fp_x + fp_y)
    (h2opt : 2 * opt ≤ fp_x + fp_y)
    (hs : 0 ≤ fp_x + fp_y)
    (hd : 0 ≤ dist_xy) :
    2 * Real.sqrt (dist_xy * mean_err)
      ≤ Real.sqrt (20 / m) * (fp_x + fp_y) := by
  have h := prop24_scale_bound hm hopt hmean hmean0 htri h2opt hs hd
  -- 2 * sqrt ≤ 2 * (sqrt(20/m) * s/2) = sqrt(20/m) * s
  have h2 : 2 * (Real.sqrt (20 / m) * ((fp_x + fp_y) / 2))
      = Real.sqrt (20 / m) * (fp_x + fp_y) := by ring
  have hle : 2 * Real.sqrt (dist_xy * mean_err)
      ≤ 2 * (Real.sqrt (20 / m) * ((fp_x + fp_y) / 2)) :=
    mul_le_mul_of_nonneg_left h (by norm_num)
  rw [h2] at hle
  exact hle

end GeometricMedianCoresets
