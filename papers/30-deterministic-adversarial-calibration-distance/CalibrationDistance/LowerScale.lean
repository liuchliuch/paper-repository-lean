import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace CalibrationDistance

/-- The logarithmic integer exponent selected in (5.3). -/
noncomputable def lowerExponent (T : ℝ) : ℕ := ⌈(1 / 2 : ℝ) * Real.logb 4 T⌉₊

/-- The energy scale `R` in (5.8). -/
noncomputable def lowerScale (T : ℝ) (a : ℕ) : ℝ :=
  T ^ (((a : ℝ) - 1) / (2 * a))

theorem lowerExponent_pos {T : ℝ} (hT : 2 ≤ T) : 1 ≤ lowerExponent T := by
  apply Nat.one_le_ceil_iff.mpr
  have hlog := Real.logb_pos (by norm_num : (1 : ℝ) < 4) (by linarith : 1 < T)
  positivity

theorem lowerExponent_le {T : ℝ} (hT : 2 ≤ T) :
    (lowerExponent T : ℝ) < (1 / 2 : ℝ) * Real.logb 4 T + 1 := by
  apply Nat.ceil_lt_add_one
  have hlog := Real.logb_pos (by norm_num : (1 : ℝ) < 4) (by linarith : 1 < T)
  positivity

theorem lowerExponent_balances {T : ℝ} (hT : 2 ≤ T) :
    T ≤ (4 : ℝ) ^ (2 * (lowerExponent T : ℝ)) := by
  apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 4)
    (by linarith : 0 < T)).mp
  have hc := Nat.le_ceil ((1 / 2 : ℝ) * Real.logb 4 T)
  change (1 / 2 : ℝ) * Real.logb 4 T ≤ (lowerExponent T : ℝ) at hc
  linarith

/-- The ceiling estimate used to control the number of bad rounds in (A.1). -/
theorem lowerExponent_bad_factor {T : ℝ} (hT : 2 ≤ T) :
    (4 : ℝ) ^ (lowerExponent T + 1) ≤ 16 * Real.sqrt T := by
  have hc := lowerExponent_le hT
  have he : ((lowerExponent T : ℝ) + 1) ≤
      (1 / 2 : ℝ) * Real.logb 4 T + 2 := by linarith
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) he
  have hid : (4 : ℝ) ^ ((1 / 2 : ℝ) * Real.logb 4 T + 2) =
      16 * Real.sqrt T := by
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 4)]
    have hx : (4 : ℝ) ^ ((1 / 2 : ℝ) * Real.logb 4 T) = Real.sqrt T := by
      rw [mul_comm, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4),
        Real.rpow_logb (by norm_num : (0 : ℝ) < 4) (by norm_num : (4 : ℝ) ≠ 1)
          (by linarith : 0 < T), Real.sqrt_eq_rpow]
    rw [hx]
    norm_num
    ring
  rw [hid] at hp
  have hp' : (4 : ℝ) ^ (((lowerExponent T + 1 : ℕ) : ℝ)) ≤ 16 * Real.sqrt T := by
    simpa only [Nat.cast_add, Nat.cast_one] using hp
  simpa only [Real.rpow_natCast] using hp'

theorem lowerScale_nonneg {T : ℝ} (hT : 0 ≤ T) (a : ℕ) : 0 ≤ lowerScale T a :=
  Real.rpow_nonneg hT _

theorem lowerScale_le_sqrt {T : ℝ} (hT : 1 ≤ T) {a : ℕ} (ha : 1 ≤ a) :
    lowerScale T a ≤ Real.sqrt T := by
  rw [lowerScale, Real.sqrt_eq_rpow]
  apply Real.rpow_le_rpow_of_exponent_le hT
  have hap : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * a)).mpr
  linarith

/-- Multiplication identity for the complementary exponents in (5.8). -/
theorem lowerScale_mul_complement {T : ℝ} (hT : 0 < T) {a : ℕ} (ha : 1 ≤ a) :
    lowerScale T a * T ^ (1 / (2 * (a : ℝ))) = Real.sqrt T := by
  rw [lowerScale, ← Real.rpow_add hT, Real.sqrt_eq_rpow]
  congr 1
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
  field_simp
  ring

/-- The full two-sided scale comparison (5.8). -/
theorem lowerScale_bounds {T : ℝ} (hT : 2 ≤ T) :
    Real.sqrt T / 4 ≤ lowerScale T (lowerExponent T) ∧
      lowerScale T (lowerExponent T) ≤ Real.sqrt T := by
  have ha := lowerExponent_pos hT
  have ha0 : (0 : ℝ) < lowerExponent T := by exact_mod_cast (by omega : 0 < lowerExponent T)
  have hcomp : T ^ (1 / (2 * (lowerExponent T : ℝ))) ≤ 4 := by
    have hp := Real.rpow_le_rpow (by linarith : (0 : ℝ) ≤ T)
      (lowerExponent_balances hT) (by positivity : (0 : ℝ) ≤ 1 / (2 * (lowerExponent T : ℝ)))
    have hid : ((4 : ℝ) ^ (2 * (lowerExponent T : ℝ))) ^
        (1 / (2 * (lowerExponent T : ℝ))) = 4 := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
      have hexp : (2 * (lowerExponent T : ℝ)) *
          (1 / (2 * (lowerExponent T : ℝ))) = 1 := by field_simp
      rw [hexp, Real.rpow_one]
    rwa [hid] at hp
  constructor
  · have hh := mul_le_mul_of_nonneg_left hcomp
      (lowerScale_nonneg (T := T) (by linarith) (lowerExponent T))
    rw [lowerScale_mul_complement (by linarith) ha] at hh
    linarith
  · exact lowerScale_le_sqrt (by linarith) ha

/-- The exponent identity behind the drift estimate (A.5), including all
casts and the positivity side conditions for real powers. -/
theorem lowerScale_drift_identity {T : ℝ} (hT : 0 < T) {a : ℕ} (ha : 1 ≤ a) :
    T ^ (1 / ((a : ℝ) + 1)) * lowerScale T a ^ ((a : ℝ) / (a + 1)) =
      Real.sqrt T := by
  rw [lowerScale, ← Real.rpow_mul (le_of_lt hT), ← Real.rpow_add hT,
    Real.sqrt_eq_rpow]
  congr 1
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
  have hap1 : (a : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- The last scalar Hölder/Jensen step in (A.5). The pathwise and integral
Hölder/Jensen estimates are proved separately in the probability component. -/
theorem lowerScale_drift_bound {T c E D : ℝ} (hT : 0 < T)
    {a : ℕ} (ha : 1 ≤ a) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hE0 : 0 ≤ E) (hE : E ≤ c * lowerScale T a)
    (hD : D ≤ T ^ (1 / ((a : ℝ) + 1)) * E ^ ((a : ℝ) / (a + 1))) :
    D ≤ Real.sqrt c * Real.sqrt T := by
  have har : (1 / 2 : ℝ) ≤ (a : ℝ) / (a + 1) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (a : ℝ) + 1)).mpr
    have haa : (1 : ℝ) ≤ a := by exact_mod_cast ha
    linarith
  have he : E ^ ((a : ℝ) / (a + 1)) ≤
      (c * lowerScale T a) ^ ((a : ℝ) / (a + 1)) :=
    Real.rpow_le_rpow hE0 hE (by positivity)
  have hc : c ^ ((a : ℝ) / (a + 1)) ≤ Real.sqrt c := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge' hc0 hc1 (by norm_num) har
  calc
    D ≤ T ^ (1 / ((a : ℝ) + 1)) * (c * lowerScale T a) ^
        ((a : ℝ) / (a + 1)) := hD.trans (mul_le_mul_of_nonneg_left he (by positivity))
    _ = c ^ ((a : ℝ) / (a + 1)) * Real.sqrt T := by
      rw [Real.mul_rpow hc0 (lowerScale_nonneg (le_of_lt hT) a)]
      rw [← mul_assoc, mul_comm (T ^ _), mul_assoc, lowerScale_drift_identity hT ha]
    _ ≤ Real.sqrt c * Real.sqrt T :=
      mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _)

end CalibrationDistance
