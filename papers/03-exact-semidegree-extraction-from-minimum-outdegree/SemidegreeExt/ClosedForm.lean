import SemidegreeExt.Basic
import Mathlib.Tactic
open Real
namespace SemidegreeExt

lemma discriminant_nonneg (n d : ℕ) (hd : d < n) :
    0 ≤ (2 * (n : ℝ) - 1)^2 - 4 * d * (d + 1) := by
  have hdn : (d : ℝ) + 1 ≤ n := by exact_mod_cast hd
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ n - d - 1)
    (by positivity : (0 : ℝ) ≤ n + d)]

lemma CReal_bounds (n d : ℕ) (hn : 0 < n) (hd : d < n) :
    0 ≤ CReal n d ∧ CReal n d ≤ d := by
  have hdn : (d : ℝ) + 1 ≤ n := by exact_mod_cast hd
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hs0 := Real.sqrt_nonneg ((2 * (n : ℝ) - 1)^2 - 4 * d * (d + 1))
  have hs2 := Real.sq_sqrt (discriminant_nonneg n d hd)
  have hsa : Real.sqrt ((2 * (n : ℝ) - 1)^2 - 4 * d * (d + 1)) ≤ 2*n-1 := by
    apply (Real.sqrt_le_left (by linarith)).mpr
    nlinarith
  have has : 2*(n : ℝ)-1-2*d ≤ Real.sqrt ((2 * (n : ℝ) - 1)^2 - 4 * d * (d + 1)) := by
    apply (Real.le_sqrt (by linarith) (discriminant_nonneg n d hd)).mpr
    nlinarith [mul_nonneg hd0 (by linarith : (0 : ℝ) ≤ n-d-1)]
  unfold CReal
  constructor <;> linarith

lemma CReal_le_iff (n d : ℕ) (hn : 0 < n) (hd : d < n)
    (x : ℝ) (hx : x ≤ d) :
    CReal n d ≤ x ↔ (d : ℝ) * (d + 1) + x * (x + 1) ≤ 2*x*n := by
  have hdn : (d : ℝ) + 1 ≤ n := by exact_mod_cast hd
  have harg : 0 ≤ 2*(n : ℝ)-1-2*x := by linarith
  have he : CReal n d ≤ x ↔ 2*(n : ℝ)-1-2*x ≤
      Real.sqrt ((2 * (n : ℝ) - 1)^2 - 4 * d * (d + 1)) := by
    unfold CReal
    constructor <;> intro h <;> linarith
  rw [he, Real.le_sqrt harg (discriminant_nonneg n d hd)]
  constructor <;> intro h <;> nlinarith

/-- The square-root expression in Theorem 1.1, including integer rounding. -/
theorem C_closed_form (n d : ℕ) (hn : 0 < n) (hd : d < n) :
    (C n d : ℝ) = Nat.ceil (CReal n d) := by
  have hb := CReal_bounds n d hn hd
  have hceil : Nat.ceil (CReal n d) ≤ d := Nat.ceil_le.mpr hb.2
  have hceilR : (Nat.ceil (CReal n d) : ℝ) ≤ d := by exact_mod_cast hceil
  have hspec : (d : ℝ)*(d+1) + (C n d : ℝ)*(C n d+1) ≤ 2*(C n d)*n := by
    exact_mod_cast C_spec n d hd
  have hCle : (C n d : ℝ) ≤ d := by exact_mod_cast C_le_d n d hd
  have hl : Nat.ceil (CReal n d) ≤ C n d := Nat.ceil_le.mpr
    ((CReal_le_iff n d hn hd _ hCle).mpr hspec)
  have hr : C n d ≤ Nat.ceil (CReal n d) := by
    apply C_is_least n d hd
    have h := (CReal_le_iff n d hn hd _ hceilR).mp (Nat.le_ceil _)
    exact_mod_cast h
  exact_mod_cast Nat.le_antisymm hr hl
end SemidegreeExt
