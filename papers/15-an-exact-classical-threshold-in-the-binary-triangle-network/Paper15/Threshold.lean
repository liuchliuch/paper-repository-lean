import Paper15.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Order.IntermediateValue

/-!
# The threshold `t*`

Paper: *An exact classical threshold in the binary triangle network*.

Equations (4)–(5): `t*` is the unique root in `(0.36, 0.37)` of
`3t^4 + 28t^3 + 66t^2 - 36t + 3 = 0`, i.e. `thresholdPoly t = 0`.

This file constructs `tStar`, proves its defining properties, and records the
exact sign pattern of `thresholdPoly` at the rational endpoints `9/25` and
`37/100`, together with positivity of its derivative on the intervening
interval (Section 2).
-/

noncomputable section

namespace Paper15

open Set Real

/-! ## Exact evaluations at the rational endpoints -/

lemma nineTwentyFifths_eq : nineTwentyFifths = (9 : ℝ) / 25 := rfl

lemma nineTwentyFifths_lt_thirtySevenHundredths :
    nineTwentyFifths < (37 / 100 : ℝ) := by
  norm_num [nineTwentyFifths]

lemma nineTwentyFifths_le_thirtySevenHundredths :
    nineTwentyFifths ≤ (37 / 100 : ℝ) :=
  le_of_lt nineTwentyFifths_lt_thirtySevenHundredths

/-- The threshold polynomial vanishes at the origin to the constant term `3`. -/
lemma thresholdPoly_zero : thresholdPoly 0 = 3 := by
  norm_num [thresholdPoly]

/-- The threshold polynomial is strictly positive at `0`. -/
lemma thresholdPoly_pos_zero : 0 < thresholdPoly 0 := by
  rw [thresholdPoly_zero]; norm_num

/-- On a left interval near the origin the threshold polynomial stays positive. -/
theorem thresholdPoly_pos_left : ∀ t, t ∈ Set.Icc 0 (1 / 10) → 0 < thresholdPoly t := by
  intro t ht
  have ht1 : (0 : ℝ) ≤ t := ht.1
  have ht2 : t ≤ 1 / 10 := ht.2
  have hpow3 : (0 : ℝ) ≤ t ^ 3 := pow_nonneg ht1 3
  have hpow4 : (0 : ℝ) ≤ t ^ 4 := pow_nonneg ht1 4
  have hpow2 : (0 : ℝ) ≤ t ^ 2 := pow_two_nonneg t
  have h : thresholdPoly t = 3 * t ^ 4 + 28 * t ^ 3 + 66 * t ^ 2 - 36 * t + 3 := rfl
  rw [h]
  nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hpow4,
    mul_nonneg (by norm_num : (0 : ℝ) ≤ 28) hpow3,
    mul_nonneg (by norm_num : (0 : ℝ) ≤ 66) hpow2,
    sq_nonneg (t - 1 / 10), sq_nonneg (3 * t - 1)]

/-- Exact rational value: `thresholdPoly (9/25) = -19392 / 390625 < 0`. -/
lemma thresholdPoly_eq_neg_rat :
    thresholdPoly nineTwentyFifths = (-19392 : ℝ) / 390625 := by
  norm_num [thresholdPoly, nineTwentyFifths]

/-- The threshold polynomial is strictly negative at `9/25 = 0.36` (paper eq. (5)). -/
theorem thresholdPoly_neg : thresholdPoly nineTwentyFifths < 0 := by
  rw [thresholdPoly_eq_neg_rat]
  norm_num

/-- Exact rational value: `thresholdPoly (37/100) = 18990883 / 100000000 > 0`. -/
lemma thresholdPoly_eq_pos_rat :
    thresholdPoly (37 / 100 : ℝ) = (18990883 : ℝ) / 100000000 := by
  norm_num [thresholdPoly]

/-- The threshold polynomial is strictly positive at `37/100 = 0.37`. -/
theorem thresholdPoly_pos_right : 0 < thresholdPoly (37 / 100 : ℝ) := by
  rw [thresholdPoly_eq_pos_rat]
  norm_num

/-- Alias matching the opposite sign convention of the right endpoint. -/
theorem thresholdPoly_pos : 0 < thresholdPoly (37 / 100 : ℝ) := thresholdPoly_pos_right

/-! ## Derivative of the threshold polynomial -/

/-- Analytic derivative of `thresholdPoly` (paper, Section 2):
`12t^3 + 84t^2 + 132t - 36`. -/
theorem hasDerivAt_thresholdPoly (t : ℝ) :
    HasDerivAt thresholdPoly (12 * t ^ 3 + 84 * t ^ 2 + 132 * t - 36) t := by
  have h := (((((hasDerivAt_const t (3 : ℝ)).mul (hasDerivAt_pow 4 t)).add
    ((hasDerivAt_const t 28).mul (hasDerivAt_pow 3 t))).add
    ((hasDerivAt_const t 66).mul (hasDerivAt_pow 2 t))).sub
    ((hasDerivAt_const t 36).mul (hasDerivAt_id t))).add (hasDerivAt_const t 3)
  refine h.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
  · filter_upwards with y
    rfl
  · ring

theorem deriv_thresholdPoly (t : ℝ) :
    deriv thresholdPoly t = 12 * t ^ 3 + 84 * t ^ 2 + 132 * t - 36 :=
  (hasDerivAt_thresholdPoly t).deriv

theorem continuous_thresholdPoly : Continuous thresholdPoly :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_thresholdPoly t).continuousAt

/-- The derivative is positive at `9/25`. -/
lemma thresholdPoly_deriv_pos_at_left :
    0 < 12 * (9 / 25 : ℝ) ^ 3 + 84 * (9 / 25) ^ 2 + 132 * (9 / 25) - 36 := by
  norm_num

/-- The derivative `12t^3 + 84t^2 + 132t - 36` is positive for all `t ≥ 9/25`.
In particular it is positive throughout `(0.36, 0.37)` (paper, Section 2). -/
theorem thresholdPoly_deriv_pos {t : ℝ} (ht : nineTwentyFifths ≤ t) :
    0 < 12 * t ^ 3 + 84 * t ^ 2 + 132 * t - 36 := by
  have ht' : (9 / 25 : ℝ) ≤ t := by
    rwa [show (9 / 25 : ℝ) = nineTwentyFifths from rfl]
  have ht0 : (0 : ℝ) ≤ t := le_trans (by norm_num) ht'
  have hbase : (12 : ℝ) * (9 / 25) ^ 3 + 84 * (9 / 25) ^ 2 + 132 * (9 / 25) - 36 > 0 := by
    norm_num
  have e3 : (9 / 25 : ℝ) ^ 3 ≤ t ^ 3 := by gcongr
  have e2 : (9 / 25 : ℝ) ^ 2 ≤ t ^ 2 := by gcongr
  have s3 : (12 : ℝ) * (9 / 25) ^ 3 ≤ 12 * t ^ 3 := by gcongr
  have s2 : (84 : ℝ) * (9 / 25) ^ 2 ≤ 84 * t ^ 2 := by gcongr
  have s1 : (132 : ℝ) * (9 / 25) ≤ 132 * t := by gcongr
  linarith

/-- The analytic derivative of `thresholdPoly` is positive at every
`t ∈ (9/25, 37/100)`. -/
theorem deriv_thresholdPoly_pos {t : ℝ}
    (h : t ∈ Set.Ioo nineTwentyFifths (37 / 100 : ℝ)) :
    0 < deriv thresholdPoly t := by
  rw [deriv_thresholdPoly]
  exact thresholdPoly_deriv_pos (le_of_lt h.1)

/-- The derivative is positive on the interior of `Ioo 9/25 (37/100)`, so
`thresholdPoly` is strictly increasing there (paper, Section 2). -/
theorem thresholdPoly_strictMonoOn :
    StrictMonoOn thresholdPoly (Set.Ioo nineTwentyFifths (37 / 100 : ℝ)) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioo _ _)
    continuous_thresholdPoly.continuousOn ?_
  intro x hx
  have hx' : x ∈ Set.Ioo nineTwentyFifths (37 / 100 : ℝ) := by
    rwa [interior_Ioo] at hx
  exact deriv_thresholdPoly_pos hx'

/-- On a left window near the origin the derivative is negative, so
`thresholdPoly` is strictly decreasing there. -/
lemma thresholdPoly_strictAntiOn_left :
    StrictAntiOn thresholdPoly (Set.Icc 0 (1 / 10)) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _)
    continuous_thresholdPoly.continuousOn ?_
  intro x hx
  have hx' : x ∈ Set.Ioo 0 (1 / 10) := by
    rwa [interior_Icc] at hx
  have hx1 : (0 : ℝ) < x := hx'.1
  have hx2 : x < 1 / 10 := hx'.2
  rw [deriv_thresholdPoly]
  have s3 : (12 : ℝ) * x ^ 3 < 12 * (1 / 10) ^ 3 := by gcongr
  have s2 : (84 : ℝ) * x ^ 2 < 84 * (1 / 10) ^ 2 := by gcongr
  have s1 : (132 : ℝ) * x < 132 * (1 / 10) := by gcongr
  linarith

/-! ## Existence and uniqueness of the root `t*` -/

/-- Intermediate value theorem: `thresholdPoly` has a zero in `(9/25, 37/100)`. -/
theorem exists_thresholdPoly_zero :
    ∃ t ∈ Set.Ioo nineTwentyFifths (37 / 100 : ℝ), thresholdPoly t = 0 := by
  have hle : nineTwentyFifths ≤ (37 / 100 : ℝ) := nineTwentyFifths_le_thirtySevenHundredths
  have hcont : ContinuousOn thresholdPoly (Set.Icc nineTwentyFifths (37 / 100 : ℝ)) :=
    continuous_thresholdPoly.continuousOn
  have hleft : thresholdPoly nineTwentyFifths < 0 := thresholdPoly_neg
  have hright : (0 : ℝ) < thresholdPoly (37 / 100) := thresholdPoly_pos_right
  have hmem : (0 : ℝ) ∈ Set.Ioo (thresholdPoly nineTwentyFifths)
      (thresholdPoly (37 / 100 : ℝ)) :=
    ⟨hleft, hright⟩
  have himg : (0 : ℝ) ∈ thresholdPoly '' Set.Ioo nineTwentyFifths (37 / 100 : ℝ) :=
    intermediate_value_Ioo hle hcont hmem
  obtain ⟨t, ht, ht0⟩ := (Set.mem_image _ _ _).1 himg
  exact ⟨t, ht, ht0⟩

/-- Any two roots of `thresholdPoly` inside `(9/25, 37/100)` coincide. -/
theorem thresholdPoly_zero_unique_on {t s : ℝ}
    (ht : t ∈ Set.Ioo nineTwentyFifths (37 / 100 : ℝ)) (hzt : thresholdPoly t = 0)
    (hs : s ∈ Set.Ioo nineTwentyFifths (37 / 100 : ℝ)) (hzs : thresholdPoly s = 0) :
    t = s := by
  rcases lt_trichotomy t s with h | h | h
  · exact absurd (thresholdPoly_strictMonoOn ht hs h) (by simp [hzt, hzs])
  · exact h
  · exact absurd (thresholdPoly_strictMonoOn hs ht h) (by simp [hzt, hzs])

/-- There is exactly one root of `thresholdPoly` in the open interval
`(9/25, 37/100) = (0.36, 0.37)`: this is `t*` of equations (4)–(5). -/
theorem exists_unique_tStar :
    ∃! t : ℝ, t ∈ Set.Ioo nineTwentyFifths (37 / 100 : ℝ) ∧ thresholdPoly t = 0 := by
  have hex : ∃ t, t ∈ Set.Ioo nineTwentyFifths (37 / 100 : ℝ) ∧ thresholdPoly t = 0 :=
    exists_thresholdPoly_zero
  refine existsUnique_of_exists_of_unique hex ?_
  intro y₁ y₂ h₁ h₂
  exact thresholdPoly_zero_unique_on h₁.1 h₁.2 h₂.1 h₂.2

/-- The classical threshold `t*`, the unique root of `thresholdPoly` in
`(0.36, 0.37)`. -/
def tStar : ℝ :=
  Classical.choose (ExistsUnique.exists exists_unique_tStar)

lemma tStar_spec :
    tStar ∈ Set.Ioo nineTwentyFifths (37 / 100 : ℝ) ∧ thresholdPoly tStar = 0 :=
  Classical.choose_spec (ExistsUnique.exists exists_unique_tStar)

/-- The threshold lies strictly between `0.36` and `0.37` (paper eq. (4)). -/
theorem tStar_mem : tStar ∈ Set.Ioo nineTwentyFifths (37 / 100 : ℝ) :=
  tStar_spec.1

/-- `t*` is a root of the threshold polynomial (paper eq. (5)). -/
theorem thresholdPoly_tStar : thresholdPoly tStar = 0 :=
  tStar_spec.2

/-- Characterization: `tStar` is the unique root of `thresholdPoly` in
`(0.36, 0.37)`. -/
theorem tStar_unique {t : ℝ}
    (ht : t ∈ Set.Ioo nineTwentyFifths (37 / 100 : ℝ))
    (hz : thresholdPoly t = 0) : t = tStar :=
  thresholdPoly_zero_unique_on ht hz tStar_mem thresholdPoly_tStar

/-- Two-sided characterization of roots in the critical interval. -/
theorem thresholdPoly_eq_zero_iff {t : ℝ}
    (ht : t ∈ Set.Ioo nineTwentyFifths (37 / 100 : ℝ)) :
    thresholdPoly t = 0 ↔ t = tStar :=
  ⟨fun hz => tStar_unique ht hz, fun h => h ▸ thresholdPoly_tStar⟩

/-! ## Elementary order properties of `t*` -/

/-- `9/25 = 0.36` is strictly less than `t*` (paper: `9/25 < t*`). -/
theorem nineTwentyFifths_lt_tStar : nineTwentyFifths < tStar :=
  tStar_mem.1

/-- `t*` is strictly less than `37/100 = 0.37`. -/
theorem tStar_lt_thirtySevenHundredths : tStar < (37 / 100 : ℝ) :=
  tStar_mem.2

/-- The threshold is positive. -/
theorem tStar_pos : 0 < tStar :=
  lt_of_lt_of_le nineTwentyFifths_pos (le_of_lt nineTwentyFifths_lt_tStar)

/-- The threshold is below `1`. -/
theorem tStar_lt_one : tStar < 1 :=
  lt_of_lt_of_le tStar_lt_thirtySevenHundredths (by norm_num)

/-- Restating membership of `t*` as a conjunction of strict inequalities. -/
theorem tStar_bounds :
    nineTwentyFifths < tStar ∧ tStar < (37 / 100 : ℝ) :=
  ⟨nineTwentyFifths_lt_tStar, tStar_lt_thirtySevenHundredths⟩

end Paper15
