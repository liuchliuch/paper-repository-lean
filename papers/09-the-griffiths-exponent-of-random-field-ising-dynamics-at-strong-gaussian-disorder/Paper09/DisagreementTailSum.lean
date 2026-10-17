import Paper09.Disagreement
import Mathlib.Algebra.Order.Field.GeomSum

open Finset BigOperators Classical Real
noncomputable section
attribute [local instance] Classical.propDecidable

namespace Paper09.Disagreement

/-- A finite interval of exponential tails is bounded by the complete geometric
sum, independently of both integer endpoints. -/
theorem sum_exp_neg_Ico_le (r₀ s : ℕ) :
    (∑ r ∈ Ico r₀ s, Real.exp (-(r : ℝ))) ≤
      1 / (1 - Real.exp (-1)) := by
  have h0 : 0 ≤ Real.exp (-1) := Real.exp_nonneg _
  have h1 : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  calc
    (∑ r ∈ Ico r₀ s, Real.exp (-(r : ℝ))) =
        ∑ r ∈ Ico r₀ s, Real.exp (-1) ^ r := by
      apply sum_congr rfl
      intro r _
      simpa only [mul_neg_one] using Real.exp_nat_mul (-1) r
    _ ≤ Real.exp (-1) ^ r₀ / (1 - Real.exp (-1)) :=
      geom_sum_Ico_le_of_lt_one h0 h1
    _ ≤ 1 / (1 - Real.exp (-1)) :=
      div_le_div_of_nonneg_right (pow_le_one₀ h0 h1.le) (sub_nonneg.mpr h1.le)

/-- A simple numerical version of the geometric-tail constant. -/
theorem one_div_one_sub_exp_neg_one_le_two :
    1 / (1 - Real.exp (-1)) ≤ (2 : ℝ) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hhalf : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left htwo (Real.exp_nonneg (-1))
    have he : Real.exp (-1) * Real.exp 1 = 1 := by
      rw [← Real.exp_add]
      norm_num
    nlinarith
  have hden : 0 < 1 - Real.exp (-1) := by linarith
  apply (div_le_iff₀ hden).mpr
  linarith

/-- Uniform finite exponential-tail summability with the numerical constant 2. -/
theorem sum_exp_neg_Ico_le_two (r₀ s : ℕ) :
    (∑ r ∈ Ico r₀ s, Real.exp (-(r : ℝ))) ≤ (2 : ℝ) :=
  (sum_exp_neg_Ico_le r₀ s).trans one_div_one_sub_exp_neg_one_le_two

/-- The numerical layer-cake step: an exponential upper bound on the actual
intermediate tails gives a bound on the expectation of a truncated statistic.
The tail premise is used only for positive integers between the two cutoffs. -/
theorem expected_truncated_of_exponential_tail {Ω : Type*} [Fintype Ω]
    (m : FinProb Ω) (X : Ω → ℕ) (N r₀ s : ℕ) (ρ : ℝ)
    (hρ : 0 < ρ) (hr₀ : 0 < r₀) (hrs : r₀ ≤ s)
    (htail : ∀ r : ℕ, 0 < r → r₀ ≤ r → r ≤ s →
      m.expect (fun ω => if r ≤ X ω then (1 : ℝ) else 0) ≤
        ρ⁻¹ * Real.exp (-(r : ℝ))) :
    m.expect (fun ω => (min N (X ω) : ℝ)) ≤
      (r₀ : ℝ) + (1 / (1 - Real.exp (-1))) / ρ +
        (N : ℝ) / ρ * Real.exp (-(s : ℝ)) := by
  have hsum :
      (∑ r ∈ Ico r₀ s, m.expect (fun ω => if r < X ω then (1 : ℝ) else 0)) ≤
        ρ⁻¹ * (1 / (1 - Real.exp (-1))) := by
    calc
      (∑ r ∈ Ico r₀ s, m.expect (fun ω => if r < X ω then (1 : ℝ) else 0)) ≤
          ∑ r ∈ Ico r₀ s, ρ⁻¹ * Real.exp (-(r : ℝ)) := by
        apply sum_le_sum
        intro r hr
        have hr' := mem_Ico.mp hr
        exact (m.expect_mono (fun ω => by
          by_cases hx : r < X ω
          · simp [hx, hx.le]
          · simp only [hx, if_false]
            split_ifs <;> norm_num)).trans
              (htail r (lt_of_lt_of_le hr₀ hr'.1) hr'.1 hr'.2.le)
      _ = ρ⁻¹ * (∑ r ∈ Ico r₀ s, Real.exp (-(r : ℝ))) := by rw [mul_sum]
      _ ≤ ρ⁻¹ * (1 / (1 - Real.exp (-1))) :=
        mul_le_mul_of_nonneg_left (sum_exp_neg_Ico_le r₀ s) (inv_nonneg.mpr hρ.le)
  have hs := htail s (lt_of_lt_of_le hr₀ hrs) hrs le_rfl
  have h := expected_truncated_tail m X N r₀ s
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hlast := mul_le_mul_of_nonneg_left hs hN
  calc
    m.expect (fun ω => (min N (X ω) : ℝ)) ≤
        (r₀ : ℝ) + ρ⁻¹ * (1 / (1 - Real.exp (-1))) +
          (N : ℝ) * (ρ⁻¹ * Real.exp (-(s : ℝ))) := by linarith
    _ = (r₀ : ℝ) + (1 / (1 - Real.exp (-1))) / ρ +
        (N : ℝ) / ρ * Real.exp (-(s : ℝ)) := by ring

/-- Numerical-constant form of the truncated exponential-tail estimate. -/
theorem expected_truncated_of_exponential_tail_two {Ω : Type*} [Fintype Ω]
    (m : FinProb Ω) (X : Ω → ℕ) (N r₀ s : ℕ) (ρ : ℝ)
    (hρ : 0 < ρ) (hr₀ : 0 < r₀) (hrs : r₀ ≤ s)
    (htail : ∀ r : ℕ, 0 < r → r₀ ≤ r → r ≤ s →
      m.expect (fun ω => if r ≤ X ω then (1 : ℝ) else 0) ≤
        ρ⁻¹ * Real.exp (-(r : ℝ))) :
    m.expect (fun ω => (min N (X ω) : ℝ)) ≤
      (r₀ : ℝ) + 2 / ρ + (N : ℝ) / ρ * Real.exp (-(s : ℝ)) := by
  have h := expected_truncated_of_exponential_tail m X N r₀ s ρ hρ hr₀ hrs htail
  have hc := div_le_div_of_nonneg_right one_div_one_sub_exp_neg_one_le_two hρ.le
  linarith

end Paper09.Disagreement
