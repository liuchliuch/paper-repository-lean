import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# Scalar volume rates in Theorem 2.4

This file proves the final arithmetic conversion of a Frobenius-ball or
ellipsoid numerator bound and the Grassmannian normalizer lower bound into the
`6e` and `18e` rates. Geometric numerator bounds are explicit preceding inputs;
the final rates are not assumptions. The factorial estimate is proved directly
from mathlib's kernel-checked global Stirling lower bound.
-/
noncomputable section
open scoped BigOperators
open Real Finset

namespace Paper26.VolumeRates

/-- The elementary factorial estimate used after the ball-volume comparison. -/
theorem pow_div_exp_le_factorial (q : ℕ) (hq : 0 < q) :
    ((q : ℝ) / Real.exp 1) ^ q ≤ (q.factorial : ℝ) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hs : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * q) := by
    apply Real.one_le_sqrt.mpr
    nlinarith [Real.pi_gt_three]
  calc
    ((q : ℝ) / Real.exp 1) ^ q =
        1 * ((q : ℝ) / Real.exp 1) ^ q := (one_mul _).symm
    _ ≤ Real.sqrt (2 * Real.pi * q) * ((q : ℝ) / Real.exp 1) ^ q :=
      mul_le_mul_of_nonneg_right hs (by positivity)
    _ ≤ (q.factorial : ℝ) := Stirling.le_factorial_stirling q

/-- Generic scalar conversion of the numerator and normalizer bounds. -/
theorem normalized_volume_bound {q : ℕ} (hq : 0 < q)
    {s T numerator V : ℝ} (hs : 0 < s) (hT : 0 ≤ T)
    (hnum0 : 0 ≤ numerator)
    (hnum : numerator ≤ Real.pi ^ q * T ^ q / (q.factorial : ℝ))
    (hV : (Real.pi / (2 * s)) ^ q ≤ V) :
    numerator / V ≤ (2 * Real.exp 1 * s * T / (q : ℝ)) ^ q := by
  have hbase : 0 < (Real.pi / (2 * s)) ^ q := by positivity
  have hfac : (0 : ℝ) < q.factorial := by exact_mod_cast Nat.factorial_pos q
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hlow : (0 : ℝ) < ((q : ℝ) / Real.exp 1) ^ q := by positivity
  calc
    numerator / V ≤ numerator / (Real.pi / (2 * s)) ^ q :=
      div_le_div_of_nonneg_left hnum0 hbase hV
    _ ≤ (Real.pi ^ q * T ^ q / (q.factorial : ℝ)) /
        (Real.pi / (2 * s)) ^ q :=
      div_le_div_of_nonneg_right hnum hbase.le
    _ = (2 * s * T) ^ q / (q.factorial : ℝ) := by
      rw [div_pow, mul_pow, mul_pow]
      field_simp
      ring
    _ ≤ (2 * s * T) ^ q / (((q : ℝ) / Real.exp 1) ^ q) :=
      div_le_div_of_nonneg_left (by positivity) hlow (pow_div_exp_le_factorial q hq)
    _ = (2 * Real.exp 1 * s * T / (q : ℝ)) ^ q := by
      rw [← div_pow]
      congr 1
      field_simp

/-- Substituting the Bures Frobenius-ball squared radius gives the source's
`6e` rate base. -/
theorem bures_rate_base (r s : ℕ) (hr : 0 < r) (hs : 0 < s) (ε : ℝ) :
    2 * Real.exp 1 * (s : ℝ) *
      (3 * (r : ℝ) * Real.sqrt (r : ℝ) * ε / Real.sqrt (s : ℝ)) /
        ((r * s : ℕ) : ℝ) =
      6 * Real.exp 1 * ε * Real.sqrt ((r : ℝ) / (s : ℝ)) := by
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have hss : Real.sqrt (s : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast hs)).ne'
  rw [Real.sqrt_div (Nat.cast_nonneg r)]
  push_cast
  field_simp
  ring

/-- Substituting the right-inverse ellipsoid squared radius gives the source's
`18e` rate base. -/
theorem rightInverse_rate_base (r s : ℕ) (hr : 0 < r) (hs : 0 < s) (ε : ℝ) :
    2 * Real.exp 1 * (s : ℝ) * (9 * (r : ℝ) ^ 2 * ε ^ 2 / (s : ℝ)) /
      ((r * s : ℕ) : ℝ) = 18 * Real.exp 1 * (r : ℝ) * ε ^ 2 / (s : ℝ) := by
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  push_cast
  field_simp
  ring

/-- The final scalar part of Theorem 2.4, Equation (19). The actual geometric
numerator and normalizer estimates are the preceding inputs. -/
theorem bures_normalized_volume_rate (r s : ℕ) (hr : 0 < r) (hs : 0 < s)
    (ε : ℝ) (hε : 0 < ε) {numerator V : ℝ}
    (hnum0 : 0 ≤ numerator)
    (hnum : numerator ≤ Real.pi ^ (r * s) *
      (3 * (r : ℝ) * Real.sqrt (r : ℝ) * ε / Real.sqrt (s : ℝ)) ^ (r * s) /
        ((r * s).factorial : ℝ))
    (hV : (Real.pi / (2 * (s : ℝ))) ^ (r * s) ≤ V) :
    numerator / V ≤
      (6 * Real.exp 1 * ε * Real.sqrt ((r : ℝ) / (s : ℝ))) ^ (r * s) := by
  have h := normalized_volume_bound (Nat.mul_pos hr hs)
    (by exact_mod_cast hs : (0 : ℝ) < s)
    (by positivity : 0 ≤ 3 * (r : ℝ) * Real.sqrt (r : ℝ) * ε / Real.sqrt (s : ℝ))
    hnum0 hnum hV
  simpa only [bures_rate_base r s hr hs ε] using h

/-- The final scalar part of Theorem 2.4, Equation (20). -/
theorem rightInverse_normalized_volume_rate (r s : ℕ) (hr : 0 < r) (hs : 0 < s)
    (ε : ℝ) (hε : 0 < ε) {numerator V : ℝ}
    (hnum0 : 0 ≤ numerator)
    (hnum : numerator ≤ Real.pi ^ (r * s) *
      (9 * (r : ℝ) ^ 2 * ε ^ 2 / (s : ℝ)) ^ (r * s) /
        ((r * s).factorial : ℝ))
    (hV : (Real.pi / (2 * (s : ℝ))) ^ (r * s) ≤ V) :
    numerator / V ≤ (18 * Real.exp 1 * (r : ℝ) * ε ^ 2 / (s : ℝ)) ^ (r * s) := by
  have h := normalized_volume_bound (Nat.mul_pos hr hs)
    (by exact_mod_cast hs : (0 : ℝ) < s)
    (by positivity : 0 ≤ 9 * (r : ℝ) ^ 2 * ε ^ 2 / (s : ℝ))
    hnum0 hnum hV
  simpa only [rightInverse_rate_base r s hr hs ε] using h

/-- The graph-chart normalizer in Lemma 2.1. Index `j=0,...,r-1` is the
source's index `j+1=1,...,r`. -/
def graphNormalizer (s r : ℕ) : ℝ :=
  Real.pi ^ (r * s) *
    ∏ j ∈ Finset.range r, (j.factorial : ℝ) / ((s + j).factorial : ℝ)

/-- Each factorial ratio has the elementary lower bound used in the normalizer
estimate. This follows from the ascending-factorial bound in mathlib. -/
theorem factorial_ratio_lower (s j : ℕ) (_hs : 0 < s) (hj : j ≤ s) :
    1 / (2 * (s : ℝ)) ^ s ≤ (j.factorial : ℝ) / ((s + j).factorial : ℝ) := by
  have ha : (0 : ℝ) < (j + 1).ascFactorial s := by
    exact_mod_cast Nat.ascFactorial_pos j s
  have hb : ((j + 1).ascFactorial s : ℝ) ≤ (2 * (s : ℝ)) ^ s := by
    have hnat := (Nat.ascFactorial_le_pow_add j s).trans
      (Nat.pow_le_pow_left (show j + s ≤ 2 * s by omega) s)
    exact_mod_cast hnat
  have he : ((s + j).factorial : ℝ) =
      (j.factorial : ℝ) * ((j + 1).ascFactorial s : ℝ) := by
    rw [Nat.add_comm s j]
    exact_mod_cast (Nat.factorial_mul_ascFactorial j s).symm
  have hjfac : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  calc
    1 / (2 * (s : ℝ)) ^ s ≤ 1 / ((j + 1).ascFactorial s : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) ha hb
    _ = (j.factorial : ℝ) / ((s + j).factorial : ℝ) := by
      rw [he]
      field_simp

/-- Equation (14)'s coarse normalizer lower bound, proved from the exact
factorial-product expression, for all `r ≤ s`. -/
theorem graphNormalizer_lower (s r : ℕ) (hs : 0 < s) (hrs : r ≤ s) :
    (Real.pi / (2 * (s : ℝ))) ^ (r * s) ≤ graphNormalizer s r := by
  have hp : (∏ _j ∈ Finset.range r, (1 / (2 * (s : ℝ)) ^ s)) ≤
      ∏ j ∈ Finset.range r, (j.factorial : ℝ) / ((s + j).factorial : ℝ) := by
    apply Finset.prod_le_prod (fun _ _ => by positivity)
    intro j hj
    exact factorial_ratio_lower s j hs (by have := Finset.mem_range.mp hj; omega)
  calc
    (Real.pi / (2 * (s : ℝ))) ^ (r * s) =
        Real.pi ^ (r * s) * (∏ _j ∈ Finset.range r, 1 / (2 * (s : ℝ)) ^ s) := by
      rw [Finset.prod_const, Finset.card_range, one_div_pow, ← pow_mul, Nat.mul_comm s r,
        div_pow]
      simp only [div_eq_mul_inv, one_mul]
    _ ≤ graphNormalizer s r := mul_le_mul_of_nonneg_left hp (by positivity)

/-- Bures rate with the exact factorial-product normalizer substituted. -/
theorem bures_graphNormalizer_rate (r s : ℕ) (hr : 0 < r) (hs : 0 < s)
    (hrs : r ≤ s) (ε : ℝ) (hε : 0 < ε) {numerator : ℝ}
    (hnum0 : 0 ≤ numerator)
    (hnum : numerator ≤ Real.pi ^ (r * s) *
      (3 * (r : ℝ) * Real.sqrt (r : ℝ) * ε / Real.sqrt (s : ℝ)) ^ (r * s) /
        ((r * s).factorial : ℝ)) :
    numerator / graphNormalizer s r ≤
      (6 * Real.exp 1 * ε * Real.sqrt ((r : ℝ) / (s : ℝ))) ^ (r * s) :=
  bures_normalized_volume_rate r s hr hs ε hε hnum0 hnum (graphNormalizer_lower s r hs hrs)

/-- Right-inverse rate with the exact factorial-product normalizer substituted. -/
theorem rightInverse_graphNormalizer_rate (r s : ℕ) (hr : 0 < r) (hs : 0 < s)
    (hrs : r ≤ s) (ε : ℝ) (hε : 0 < ε) {numerator : ℝ}
    (hnum0 : 0 ≤ numerator)
    (hnum : numerator ≤ Real.pi ^ (r * s) *
      (9 * (r : ℝ) ^ 2 * ε ^ 2 / (s : ℝ)) ^ (r * s) /
        ((r * s).factorial : ℝ)) :
    numerator / graphNormalizer s r ≤
      (18 * Real.exp 1 * (r : ℝ) * ε ^ 2 / (s : ℝ)) ^ (r * s) :=
  rightInverse_normalized_volume_rate r s hr hs ε hε hnum0 hnum
    (graphNormalizer_lower s r hs hrs)

end Paper26.VolumeRates
