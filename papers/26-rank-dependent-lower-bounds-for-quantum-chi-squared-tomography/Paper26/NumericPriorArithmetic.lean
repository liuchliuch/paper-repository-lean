import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# Numerical arithmetic for the graph Gaussian prior

These are scalar consequences of native exponential inequalities and field
arithmetic.  No probability, prior-existence, matrix, or Fisher conclusion is
an input.  The variance, net-tail estimate, and normalization constants are
kept explicit for the actual-prior construction.
-/
noncomputable section

namespace Paper26.NumericPriorArithmetic

def variance (s : ℕ) : ℝ := (4096 * (s : ℝ))⁻¹

theorem variance_pos {s : ℕ} (hs : 0 < s) : 0 < variance s := by
  unfold variance
  positivity

theorem nine_lt_exp_four : (9 : ℝ) < Real.exp 4 := by
  have h2 : (3 : ℝ) < Real.exp 2 := by
    have h := Real.add_one_lt_exp (show (2 : ℝ) ≠ 0 by norm_num)
    norm_num at h
    exact h
  have h9 : (9 : ℝ) < Real.exp 2 * Real.exp 2 := by nlinarith [Real.exp_pos 2]
  convert h9 using 1
  rw [← Real.exp_add]
  norm_num

/-- The finite net factor is absorbed by exp(16s) when r<=s. -/
theorem net_factor_le_exp {r s : ℕ} (hrs : r ≤ s) :
    (9 : ℝ) ^ (2 * (r + s)) ≤ Real.exp (16 * (s : ℝ)) := by
  have hpow : (9 : ℝ) ^ (2 * (r + s)) ≤ Real.exp 4 ^ (2 * (r + s)) := by
    gcongr
    exact nine_lt_exp_four.le
  have hrsR : (r : ℝ) ≤ s := by exact_mod_cast hrs
  calc
    _ ≤ Real.exp 4 ^ (2 * (r + s)) := hpow
    _ = Real.exp ((2 * (r + s) : ℕ) * (4 : ℝ)) := (Real.exp_nat_mul _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by push_cast; linarith)

/-- The actual net-tail bound, with an exponential margin uniform in r,s. -/
theorem net_tail_lt_half_exp {r s : ℕ} (hr : 0 < r) (hrs : r ≤ s) :
    (9 : ℝ) ^ (2 * (r + s)) * Real.exp (-32 * (s : ℝ)) < 1 / 2 := by
  have hs : 0 < s := lt_of_lt_of_le hr hrs
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hex : (2 : ℝ) < Real.exp (16 * (s : ℝ)) := by
    have he := Real.add_one_le_exp (16 * (s : ℝ))
    linarith
  have hsmall : Real.exp (-16 * (s : ℝ)) < 1 / 2 := by
    have hi := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 2) hex
    simpa only [Real.exp_neg, one_div, neg_mul] using hi
  calc
    _ ≤ Real.exp (16 * (s : ℝ)) * Real.exp (-32 * (s : ℝ)) :=
      mul_le_mul_of_nonneg_right (net_factor_le_exp hrs) (Real.exp_nonneg _)
    _ = Real.exp (-16 * (s : ℝ)) := by rw [← Real.exp_add]; congr 1; ring
    _ < _ := hsmall

/-- At cutoff radius a=1/2, the tail radius a/2=1/4 gives exponent -32s. -/
theorem tail_exponent {s : ℕ} (hs : 0 < s) :
    -(1 / 4 : ℝ) ^ 2 / (8 * variance s) = -32 * (s : ℝ) := by
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  unfold variance
  field_simp
  ring

theorem cutoff_tail_exponent {s : ℕ} (hs : 0 < s) :
    -((1 / 2 : ℝ) / 2) ^ 2 / (8 * variance s) = -32 * (s : ℝ) := by
  simpa only [show (1 / 2 : ℝ) / 2 = 1 / 4 by norm_num] using tail_exponent hs

theorem tail_exponent_div {s : ℕ} (hs : 0 < s) :
    -(1 / 4 : ℝ) ^ 2 / (8 * (1 / (4096 * (s : ℝ)))) = -32 * (s : ℝ) := by
  simpa only [variance, one_div] using tail_exponent hs

theorem net_tail_lt_half {r s : ℕ} (hr : 0 < r) (hrs : r ≤ s) :
    (9 : ℝ) ^ (2 * (r + s)) * Real.exp (-(1 / 4 : ℝ) ^ 2 / (8 * variance s)) < 1 / 2 := by
  rw [tail_exponent (lt_of_lt_of_le hr hrs)]
  exact net_tail_lt_half_exp hr hrs

/-- The same estimate in the literal division notation of the Gaussian bound. -/
theorem net_tail_lt_half_div {r s : ℕ} (hr : 1 ≤ r) (hrs : r ≤ s) :
    (9 : ℝ) ^ (2 * (r + s)) *
      Real.exp (-(1 / 4 : ℝ) ^ 2 / (8 * (1 / (4096 * (s : ℝ))))) < 1 / 2 := by
  simpa only [variance, one_div] using net_tail_lt_half (show 0 < r by omega) hrs

/-- A normalization mass of at least one half costs a factor at most sixteen. -/
theorem eight_div_normalization_le {Z : ℝ} (hZ : 1 / 2 ≤ Z) : 8 / Z ≤ 16 := by
  apply (div_le_iff₀ (by linarith : 0 < Z)).mpr
  linarith

/-- Generic cutoff normalization arithmetic, with the scalar signs explicit. -/
theorem normalization_bound {Z p v : ℝ} (hZ : 1 / 2 ≤ Z) (hp : 0 ≤ p) (hv : 0 < v) :
    (8 / Z) * (p / (4 * v) + 16) ≤ 4 * p / v + 256 := by
  calc
    _ ≤ 16 * (p / (4 * v) + 16) :=
      mul_le_mul_of_nonneg_right (eight_div_normalization_le hZ) (by positivity)
    _ = _ := by field_simp; ring

theorem information_algebra (r s : ℕ) :
    4 * ((2 * r * s : ℕ) : ℝ) / variance s + 256 =
      32768 * (r : ℝ) * (s : ℝ) ^ 2 + 256 := by
  unfold variance
  rw [div_inv_eq_mul]
  push_cast
  ring

/-- The real-coordinate dimension is exactly p=2rs, with variance 1/(4096s). -/
theorem information_bound {r s : ℕ} (hr : 0 < r) (hrs : r ≤ s) :
    4 * ((2 * r * s : ℕ) : ℝ) / variance s + 256 ≤
      65536 * (r : ℝ) * (s : ℝ) ^ 2 := by
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast (lt_of_lt_of_le hr hrs)
  have hprod : (1 : ℝ) ≤ (r : ℝ) * (s : ℝ) ^ 2 := by nlinarith
  rw [information_algebra]
  nlinarith

theorem information_bound_div {r s : ℕ} (hr : 1 ≤ r) (hrs : r ≤ s) :
    4 * ((2 * r * s : ℕ) : ℝ) / (1 / (4096 * (s : ℝ))) + 256 ≤
      65536 * (r : ℝ) * (s : ℝ) ^ 2 := by
  simpa only [variance, one_div] using information_bound (show 0 < r by omega) hrs

/-- Direct interface for the normalized prior's native energy estimate. -/
theorem normalized_information_bound {r s : ℕ} (hr : 0 < r) (hrs : r ≤ s)
    {Z : ℝ} (hZ : 1 / 2 ≤ Z) :
    (8 / Z) * (((2 * r * s : ℕ) : ℝ) / (4 * variance s) + 16) ≤
      65536 * (r : ℝ) * (s : ℝ) ^ 2 :=
  (normalization_bound hZ (by positivity) (variance_pos (lt_of_lt_of_le hr hrs))).trans
    (information_bound hr hrs)

end Paper26.NumericPriorArithmetic
