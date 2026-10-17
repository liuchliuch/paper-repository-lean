import Paper27.JetCalculation
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Ring.GeomSum

/-!
# The normal-coordinate Taylor jet comparison

These are polynomial identities for finite Taylor jets, including arbitrary
intermediate coefficients in the third retraction. In particular, equation (7)
is derived from equality of actual degree-`2n` coefficients of composed jets;
it is not assumed. The passage from holomorphic coordinate maps to these finite
jets, with composition preserved, is a separate general Taylor theorem.
-/

noncomputable section

open Polynomial Finset

namespace Paper27.Geometry.NormalJets

/-- The normal-coordinate change allowed by the normal-form transitions. -/
def normalChange (n : ℕ) (lam : ℂ) (H : ℂ[X]) : ℂ[X] :=
  C lam * X + X ^ (n + 1) * H

/-- The factor remaining after removing the single factor `X`. -/
def normalUnit (n : ℕ) (lam : ℂ) (H : ℂ[X]) : ℂ[X] :=
  C lam + X ^ n * H

/-- The coefficient formulation of a lower order bound, from an actual
polynomial divisibility statement. -/
theorem coeff_below_of_X_pow_dvd {P : ℂ[X]} {n : ℕ} (hP : X ^ n ∣ P)
    (k : ℕ) (hk : k < n) : P.coeff k = 0 := by
  obtain ⟨Q, rfl⟩ := hP
  rw [coeff_X_pow_mul', if_neg (by omega)]

/-- The gap of length `n-1` is preserved under every positive integral power;
this divisibility also covers the zeroth power. -/
theorem normalUnit_power_remainder (n m : ℕ) (lam : ℂ) (H : ℂ[X]) :
    X ^ n ∣ normalUnit n lam H ^ m - C (lam ^ m) := by
  have hbase : X ^ n ∣ normalUnit n lam H - C lam := by
    refine ⟨H, ?_⟩
    simp [normalUnit]
  have hp := dvd_trans hbase
    (sub_dvd_pow_sub_pow (normalUnit n lam H) (C lam) m)
  simpa only [C_pow] using hp

/-- No degree strictly between zero and `n` occurs in the unit factor power. -/
theorem normalUnit_power_gap (n m k : ℕ) (lam : ℂ) (H : ℂ[X])
    (hk0 : 0 < k) (hkn : k < n) :
    (normalUnit n lam H ^ m).coeff k = 0 := by
  have h := coeff_below_of_X_pow_dvd (normalUnit_power_remainder n m lam H) k hkn
  simpa only [coeff_sub, coeff_C, if_neg (Nat.ne_of_gt hk0), sub_zero] using h

/-- The constant coefficient of the unit factor power is the expected power. -/
theorem normalUnit_power_constant {n : ℕ} (hn : 0 < n) (m : ℕ)
    (lam : ℂ) (H : ℂ[X]) : (normalUnit n lam H ^ m).coeff 0 = lam ^ m := by
  have h := coeff_below_of_X_pow_dvd (normalUnit_power_remainder n m lam H) 0 hn
  simpa only [coeff_sub, coeff_C_zero, sub_eq_zero] using h

/-- The normal-coordinate change has a single factor `X`. -/
theorem normalChange_factor (n : ℕ) (lam : ℂ) (H : ℂ[X]) :
    normalChange n lam H = X * normalUnit n lam H := by
  simp only [normalChange, normalUnit, pow_succ]
  ring

/-- A complete coefficient shift formula for every power of the change. -/
theorem normalChange_power_coeff (n m d : ℕ) (lam : ℂ) (H : ℂ[X]) :
    (normalChange n lam H ^ m).coeff d =
      if m ≤ d then (normalUnit n lam H ^ m).coeff (d - m) else 0 := by
  rw [normalChange_factor, mul_pow, coeff_X_pow_mul']

/-- All intermediate exponents of the third retraction make zero contribution
in degree `2n` after the coordinate change. -/
theorem normalChange_power_middle {n m : ℕ} (lam : ℂ) (H : ℂ[X])
    (hnm : n < m) (hmn : m < 2 * n) :
    (normalChange n lam H ^ m).coeff (2 * n) = 0 := by
  rw [normalChange_power_coeff, if_pos (le_of_lt hmn)]
  apply normalUnit_power_gap
  · omega
  · omega

/-- The power with exponent `2n` contributes exactly `lam^(2n)`. -/
theorem normalChange_power_double {n : ℕ} (hn : 0 < n)
    (lam : ℂ) (H : ℂ[X]) :
    (normalChange n lam H ^ (2 * n)).coeff (2 * n) = lam ^ (2 * n) := by
  rw [normalChange_power_coeff, if_pos le_rfl, Nat.sub_self]
  exact normalUnit_power_constant hn _ lam H

/-- Exponents greater than `2n` cannot contribute to its coefficient. -/
theorem normalChange_power_above {n m : ℕ} (lam : ℂ) (H : ℂ[X])
    (hm : 2 * n < m) : (normalChange n lam H ^ m).coeff (2 * n) = 0 := by
  rw [normalChange_power_coeff, if_neg (by omega)]

/-- The leading normal-form coefficient transforms by `lam^n`. -/
theorem normalChange_power_leading {n : ℕ} (hn : 0 < n)
    (lam : ℂ) (H : ℂ[X]) : (normalChange n lam H ^ n).coeff n = lam ^ n := by
  rw [normalChange_power_coeff, if_pos le_rfl, Nat.sub_self]
  exact normalUnit_power_constant hn _ lam H

/-- For a general polynomial with order at least `n`, the entire degree-`2n`
coefficient of the composition has only its degree-`n` and degree-`2n`
contributions. Arbitrary coefficients between them are allowed. -/
theorem composition_coefficient_double {n : ℕ} (hn : 2 ≤ n)
    (P' : ℂ[X]) (lam : ℂ) (H : ℂ[X]) (a : ℂ)
    (hbelow : ∀ m < n, P'.coeff m = 0) (hleading : P'.coeff n = a) :
    (P'.comp (normalChange n lam H)).coeff (2 * n) =
      a * (normalChange n lam H ^ n).coeff (2 * n) +
        P'.coeff (2 * n) * lam ^ (2 * n) := by
  have hn0 : 0 < n := by omega
  have hne : n ≠ 2 * n := by omega
  rw [comp_eq_sum_left, coeff_sum, Polynomial.sum_def]
  simp only [coeff_C_mul]
  have hsummand : ∀ m : ℕ,
      P'.coeff m * (normalChange n lam H ^ m).coeff (2 * n) =
        (if m = n then P'.coeff n * (normalChange n lam H ^ n).coeff (2 * n)
          else 0) +
        (if m = 2 * n then P'.coeff (2 * n) * lam ^ (2 * n) else 0) := by
    intro m
    by_cases hmn : m = n
    · subst m
      simp [hne]
    by_cases hm2n : m = 2 * n
    · subst m
      simp [hne.symm, normalChange_power_double hn0]
    by_cases hlow : m < n
    · simp [hmn, hm2n, hbelow m hlow]
    by_cases hmiddle : m < 2 * n
    · have hnm : n < m := by omega
      simp [hmn, hm2n, normalChange_power_middle lam H hnm hmiddle]
    · have habove : 2 * n < m := by omega
      simp [hmn, hm2n, normalChange_power_above lam H habove]
  have hsum :
      (∑ m ∈ P'.support,
        P'.coeff m * (normalChange n lam H ^ m).coeff (2 * n)) =
      ∑ m ∈ P'.support,
        ((if m = n then P'.coeff n * (normalChange n lam H ^ n).coeff (2 * n)
          else 0) +
        (if m = 2 * n then P'.coeff (2 * n) * lam ^ (2 * n) else 0)) := by
    apply Finset.sum_congr rfl
    intro m hm
    exact hsummand m
  rw [hsum]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Polynomial.mem_support_iff]
  by_cases hcn : P'.coeff n = 0 <;>
    by_cases hc2n : P'.coeff (2 * n) = 0 <;>
      simp [hcn, hc2n, ← hleading]

/-- The coefficient comparison actually implies equation (7). Inputs are the
jet composition equality and the usual lower order and leading coefficients,
not a rearranged form of equation (7). The assumptions `X^n ∣ P` and `X^n ∣ P'`
are genuine polynomial lower order bounds. -/
theorem equation_seven_from_jet_compatibility {n : ℕ} (hn : 2 ≤ n)
    (P P' H : ℂ[X]) (lam a p q : ℂ)
    (hP : X ^ n ∣ P) (hP' : X ^ n ∣ P')
    (ha : P.coeff n = a) (ha' : P'.coeff n = a)
    (hlam : lam ^ n = p)
    (hchange : (normalChange n lam H ^ n).coeff (2 * n) = q / 2)
    (hjet : (P'.comp (normalChange n lam H)).coeff (2 * n) =
      (C p * P + C (q / 2) * P ^ 2).coeff (2 * n)) :
    P'.coeff (2 * n) * p ^ 2 =
      p * P.coeff (2 * n) + (a ^ 2 - a) / 2 * q := by
  have hbelow : ∀ j < n, P.coeff j = 0 :=
    fun j hj => coeff_below_of_X_pow_dvd hP j hj
  have hbelow' : ∀ j < n, P'.coeff j = 0 :=
    fun j hj => coeff_below_of_X_pow_dvd hP' j hj
  have hlam2 : lam ^ (2 * n) = p ^ 2 := by
    rw [Nat.mul_comm 2 n, pow_mul, hlam]
  rw [composition_coefficient_double hn P' lam H a hbelow' ha',
    hchange, hlam2, JetCalculation.target_composition_coeff P n p q hbelow,
    ha] at hjet
  linear_combination hjet

end Paper27.Geometry.NormalJets
