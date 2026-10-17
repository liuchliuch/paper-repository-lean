import Paper29.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-! The exact scalar majority gap, Lemma 4.1 of the paper. -/
noncomputable section

namespace Paper29.Majority

/-- The width-one Huber loss is even. -/
theorem huber_even (x : ℝ) : huber (-x) = huber x := by
  simp [huber, abs_neg]

/-- Every slope in `[-1,1]` gives a global supporting affine function. -/
theorem huber_ge_affine (x q : ℝ) (hqlo : -1 ≤ q) (hqhi : q ≤ 1) :
    q * x - q ^ 2 / 2 ≤ huber x := by
  unfold huber
  split_ifs with hx
  · nlinarith [sq_nonneg (x - q)]
  · have hxlarge : 1 < |x| := lt_of_not_ge hx
    by_cases hx0 : 0 ≤ x
    · rw [abs_of_nonneg hx0] at hxlarge ⊢
      have hp : 0 ≤ (1 - q) * (x - 1) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith [sq_nonneg (q - 1)]
    · have hxneg : x ≤ 0 := le_of_lt (lt_of_not_ge hx0)
      rw [abs_of_nonpos hxneg] at hxlarge ⊢
      have hp : 0 ≤ (q + 1) * (-x - 1) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith [sq_nonneg (q + 1)]

/-- The scalar majority ratio is a valid Huber slope. -/
theorem ratio_bounds (γ : ℝ) (hγ : 0 < γ) (hγhi : γ ≤ 1 / 2) :
    0 ≤ majorityRatio γ ∧ majorityRatio γ < 1 := by
  have hb : 0 < (1 / 2 : ℝ) + γ := by linarith
  constructor
  · exact div_nonneg (by linarith) (le_of_lt hb)
  · exact (div_lt_one hb).2 (by linarith)

/-- The ratio satisfies its defining cancellation identity. -/
theorem ratio_identity (γ : ℝ) (hγ : 0 < γ) :
    (1 / 2 + γ) * majorityRatio γ = 1 / 2 - γ := by
  have hb : (1 / 2 : ℝ) + γ ≠ 0 := by linarith
  exact mul_div_cancel₀ _ hb

/-- At the displayed optimizer the zero-label residual is in the linear branch. -/
theorem huber_at_minimizer_zero (γ : ℝ) (hγ : 0 < γ) (hγhi : γ ≤ 1 / 2) :
    huber (4 * majorityMinimizer γ) = 7 / 2 - majorityRatio γ := by
  obtain ⟨hq0, hq1⟩ := ratio_bounds γ hγ hγhi
  have hx : 4 * majorityMinimizer γ = 4 - majorityRatio γ := by
    unfold majorityMinimizer
    ring
  have hpos : 0 ≤ 4 - majorityRatio γ := by linarith
  rw [hx, huber, abs_of_nonneg hpos, if_neg (by linarith)]
  ring

/-- At the displayed optimizer the one-label residual is in the quadratic branch. -/
theorem huber_at_minimizer_one (γ : ℝ) (hγ : 0 < γ) (hγhi : γ ≤ 1 / 2) :
    huber (4 * (majorityMinimizer γ - 1)) = (majorityRatio γ) ^ 2 / 2 := by
  obtain ⟨hq0, hq1⟩ := ratio_bounds γ hγ hγhi
  have hx : 4 * (majorityMinimizer γ - 1) = -majorityRatio γ := by
    unfold majorityMinimizer
    ring
  rw [hx, huber, abs_neg, abs_of_nonneg hq0, if_pos (le_of_lt hq1)]
  ring

/-- Exact optimum, in a ratio form useful for the supporting-line proof. -/
theorem minimizer_value_ratio (N γ : ℝ) (hγ : 0 < γ) (hγhi : γ ≤ 1 / 2) :
    majorityObjective N γ (majorityMinimizer γ) =
      N * ((1 / 2 - γ) * (7 / 2 - majorityRatio γ / 2)) := by
  rw [majorityObjective, huber_at_minimizer_zero γ hγ hγhi,
    huber_at_minimizer_one γ hγ hγhi]
  calc
    _ = N * ((1 / 2 - γ) * (7 / 2 - majorityRatio γ) +
        ((1 / 2 + γ) * majorityRatio γ) * majorityRatio γ / 2) := by ring
    _ = N * ((1 / 2 - γ) * (7 / 2 - majorityRatio γ) +
        (1 / 2 - γ) * majorityRatio γ / 2) := by rw [ratio_identity γ hγ]
    _ = _ := by ring

/-- The paper's explicit formula for the scalar minimum. -/
theorem minimizer_value (N γ : ℝ) (hγ : 0 < γ) (hγhi : γ ≤ 1 / 2) :
    majorityObjective N γ (majorityMinimizer γ) =
      N * (7 / 2 * (1 / 2 - γ) - (1 / 2 - γ) ^ 2 / (2 * (1 / 2 + γ))) := by
  rw [minimizer_value_ratio N γ hγ hγhi]
  unfold majorityRatio
  have hb : (1 / 2 : ℝ) + γ ≠ 0 := by linarith
  field_simp [hb]

/-- The displayed point is a global minimizer, including at the endpoint `γ=1/2`. -/
theorem global_minimizer (N γ : ℝ) (hN : 0 ≤ N)
    (hγ : 0 < γ) (hγhi : γ ≤ 1 / 2) (t : ℝ) :
    majorityObjective N γ (majorityMinimizer γ) ≤ majorityObjective N γ t := by
  obtain ⟨hq0, hq1⟩ := ratio_bounds γ hγ hγhi
  have ha : 0 ≤ N * (1 / 2 - γ) := mul_nonneg hN (by linarith)
  have hb : 0 ≤ N * (1 / 2 + γ) := mul_nonneg hN (by linarith)
  have hz := mul_le_mul_of_nonneg_left
    (huber_ge_affine (4 * t) 1 (by norm_num) (by norm_num)) ha
  have ho := mul_le_mul_of_nonneg_left
    (huber_ge_affine (4 * (t - 1)) (-majorityRatio γ) (by linarith) (by linarith)) hb
  rw [minimizer_value_ratio N γ hγ hγhi]
  unfold majorityObjective
  have hsum := add_le_add hz ho
  have hid : N * (1 / 2 - γ) * (1 * (4 * t) - 1 ^ 2 / 2) +
      N * (1 / 2 + γ) * ((-majorityRatio γ) * (4 * (t - 1)) -
        (-majorityRatio γ) ^ 2 / 2) =
      N * ((1 / 2 - γ) * (7 / 2 - majorityRatio γ / 2)) := by
    calc
      _ = N * ((1 / 2 - γ) * (4 * t - 1 / 2) +
          ((1 / 2 + γ) * majorityRatio γ) *
            (-4 * (t - 1) - majorityRatio γ / 2)) := by ring
      _ = N * ((1 / 2 - γ) * (4 * t - 1 / 2) +
          (1 / 2 - γ) * (-4 * (t - 1) - majorityRatio γ / 2)) := by
        rw [ratio_identity γ hγ]
      _ = _ := by ring
  rw [hid] at hsum
  exact hsum

/-- The objective at the decision boundary has a particularly simple value. -/
theorem midpoint_value (N γ : ℝ) : majorityObjective N γ (1 / 2) = 3 * N / 2 := by
  norm_num [majorityObjective, huber]
  ring

/-- An affine support at the midpoint controls the whole wrong half-line. -/
theorem wrong_halfline_boundary (N γ : ℝ) (hN : 0 ≤ N)
    (hγ : 0 < γ) (hγhi : γ ≤ 1 / 2) (t : ℝ) (ht : t ≤ 1 / 2) :
    majorityObjective N γ (1 / 2) ≤ majorityObjective N γ t := by
  have ha : 0 ≤ N * (1 / 2 - γ) := mul_nonneg hN (by linarith)
  have hb : 0 ≤ N * (1 / 2 + γ) := mul_nonneg hN (by linarith)
  have hz := mul_le_mul_of_nonneg_left
    (huber_ge_affine (4 * t) 1 (by norm_num) (by norm_num)) ha
  have ho := mul_le_mul_of_nonneg_left
    (huber_ge_affine (4 * (t - 1)) (-1) (by norm_num) (by norm_num)) hb
  have hg : 0 ≤ 8 * N * γ * (1 / 2 - t) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hN) (le_of_lt hγ))
      (by linarith)
  rw [midpoint_value]
  unfold majorityObjective
  nlinarith [add_le_add hz ho]

/-- The exact midpoint-to-optimum gap in equation (4.3). -/
theorem midpoint_gap (N γ : ℝ) (hγ : 0 < γ) (hγhi : γ ≤ 1 / 2) :
    majorityObjective N γ (1 / 2) - majorityObjective N γ (majorityMinimizer γ) =
      2 * γ * N * ((1 + 4 * γ) / (1 + 2 * γ)) := by
  rw [midpoint_value, minimizer_value_ratio N γ hγ hγhi]
  unfold majorityRatio
  have hb : (1 / 2 : ℝ) + γ ≠ 0 := by linarith
  have hc : (1 : ℝ) + 2 * γ ≠ 0 := by linarith
  field_simp
  ring

/-- Exact scalar majority gap: every incorrectly decoded scalar pays the sharp gap. -/
theorem exact_scalar_majority_gap (N γ : ℝ) (hN : 1 ≤ N)
    (hγ : 0 < γ) (hγhi : γ ≤ 1 / 2) (t : ℝ) (ht : t ≤ 1 / 2) :
    2 * γ * N * ((1 + 4 * γ) / (1 + 2 * γ)) ≤
      majorityObjective N γ t - majorityObjective N γ (majorityMinimizer γ) ∧
    2 * γ * N ≤ 2 * γ * N * ((1 + 4 * γ) / (1 + 2 * γ)) := by
  have hN0 : 0 ≤ N := by linarith
  constructor
  · rw [← midpoint_gap N γ hγ hγhi]
    exact sub_le_sub_right (wrong_halfline_boundary N γ hN0 hγ hγhi t ht) _
  · have hr : (1 : ℝ) ≤ (1 + 4 * γ) / (1 + 2 * γ) :=
      (le_div_iff₀ (by linarith : (0 : ℝ) < 1 + 2 * γ)).2 (by linarith)
    have hc : 0 ≤ 2 * γ * N := by positivity
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hr hc

/-- Reflection interchanges positive and negative empirical majorities. -/
theorem reflection (N γ t : ℝ) :
    majorityObjective N (-γ) t = majorityObjective N γ (1 - t) := by
  have hzero : 4 * (1 - t) = -(4 * (t - 1)) := by ring
  have hone : 4 * (1 - t - 1) = -(4 * t) := by ring
  unfold majorityObjective
  rw [hzero, hone, huber_even, huber_even]
  ring

/-- Reflected optimizer for a negative empirical majority. -/
theorem negative_global_minimizer (N γ : ℝ) (hN : 0 ≤ N)
    (hγ : 0 < γ) (hγhi : γ ≤ 1 / 2) (t : ℝ) :
    majorityObjective N (-γ) (1 - majorityMinimizer γ) ≤ majorityObjective N (-γ) t := by
  rw [reflection, reflection]
  have hx : 1 - (1 - majorityMinimizer γ) = majorityMinimizer γ := by ring
  rw [hx]
  exact global_minimizer N γ hN hγ hγhi (1 - t)

/-- The complete symmetric wrong-half-line statement for a negative majority. -/
theorem negative_exact_scalar_majority_gap (N γ : ℝ) (hN : 1 ≤ N)
    (hγ : 0 < γ) (hγhi : γ ≤ 1 / 2) (t : ℝ) (ht : 1 / 2 ≤ t) :
    2 * γ * N * ((1 + 4 * γ) / (1 + 2 * γ)) ≤
      majorityObjective N (-γ) t -
        majorityObjective N (-γ) (1 - majorityMinimizer γ) ∧
    2 * γ * N ≤ 2 * γ * N * ((1 + 4 * γ) / (1 + 2 * γ)) := by
  rw [reflection, reflection]
  have hx : 1 - (1 - majorityMinimizer γ) = majorityMinimizer γ := by ring
  rw [hx]
  exact exact_scalar_majority_gap N γ hN hγ hγhi (1 - t) (by linarith)

/-- Lemma 4.1, bundling the unrestricted global optimum with its sharp decision gap. -/
theorem lemma4_1 (N γ : ℝ) (hN : 1 ≤ N)
    (hγ : 0 < γ) (hγhi : γ ≤ 1 / 2) :
    (∀ t : ℝ, majorityObjective N γ (majorityMinimizer γ) ≤ majorityObjective N γ t) ∧
    (∀ t : ℝ, t ≤ 1 / 2 →
      2 * γ * N * ((1 + 4 * γ) / (1 + 2 * γ)) ≤
        majorityObjective N γ t - majorityObjective N γ (majorityMinimizer γ) ∧
      2 * γ * N ≤ 2 * γ * N * ((1 + 4 * γ) / (1 + 2 * γ))) := by
  constructor
  · intro t
    exact global_minimizer N γ (by linarith) hγ hγhi t
  · intro t ht
    exact exact_scalar_majority_gap N γ hN hγ hγhi t ht

end Paper29.Majority
