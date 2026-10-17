import Paper10.Gaussian
import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

noncomputable section
open Polynomial MeasureTheory ProbabilityTheory
namespace Paper10
namespace Hermite

/-- Probabilists' Hermite polynomials with real coefficients. -/
def hp (n : ℕ) : Polynomial ℝ := (Polynomial.hermite n).map (Int.castRingHom ℝ)

@[simp] theorem hp_zero : hp 0 = 1 := by simp [hp]
@[simp] theorem hp_one : hp 1 = Polynomial.X := by simp [hp, Polynomial.hermite_one]
@[simp] theorem hp_succ (n : ℕ) : hp (n + 1) = Polynomial.X * hp n - (hp n).derivative := by
  simp [hp, Polynomial.hermite_succ, Polynomial.derivative_map]

theorem hp_derivative (n : ℕ) : (hp (n + 1)).derivative = Polynomial.C (n + 1 : ℝ) * hp n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hp_succ (n + 1), Polynomial.derivative_sub, Polynomial.derivative_mul,
      Polynomial.derivative_X, one_mul, ih, Polynomial.derivative_mul]
    simp only [Polynomial.derivative_C, zero_mul, zero_add]
    calc
      _ = hp (n + 1) + Polynomial.C (n + 1 : ℝ) *
          (Polynomial.X * hp n - (hp n).derivative) := by ring
      _ = _ := by
        rw [← hp_succ n]
        simp only [Nat.cast_add, Nat.cast_one, Polynomial.C_add, Polynomial.C_1]
        ring

theorem integrable_eval (p : Polynomial ℝ) : Integrable (fun x : ℝ => p.eval x) (gaussianReal 0 1) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa using hp.add hq
  | monomial n a => simpa using (integrable_std_pow n).const_mul a

private def weight (x : ℝ) : ℝ := Real.exp (-(x ^ 2 / 2))

private theorem integrable_weighted (p : Polynomial ℝ) : Integrable (fun x : ℝ => p.eval x * weight x) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add, add_mul] using hp.add hq
  | monomial n a =>
    have h := integrable_rpow_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)
      (s := (n : ℝ)) (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
    have he : (fun x : ℝ => x ^ (n : ℝ) * Real.exp (-(1 / 2) * x ^ 2)) =
        fun x : ℝ => x ^ n * weight x := by
      funext x
      rw [Real.rpow_natCast]
      congr 2
      dsimp [weight]
      congr 1
      ring
    rw [he] at h
    simpa only [Polynomial.eval_monomial, mul_assoc] using h.const_mul a

/-- Gaussian integration by parts, proved for every polynomial from an integrable derivative. -/
theorem stein (p : Polynomial ℝ) :
    (∫ x, x * p.eval x ∂gaussianReal 0 1) = ∫ x, p.derivative.eval x ∂gaussianReal 0 1 := by
  have hd : ∀ x : ℝ, HasDerivAt (fun y : ℝ => p.eval y * weight y)
      ((p.derivative.eval x - x * p.eval x) * weight x) x := by
    intro x
    have hw : HasDerivAt weight (-x * weight x) x := by
      have hh := (((hasDerivAt_id x).pow 2).div_const 2).neg.exp
      convert hh using 1 <;> dsimp [weight] <;> ring
    convert (p.hasDerivAt x).mul hw using 1 <;> ring
  have hi := integrable_weighted (p.derivative - Polynomial.X * p)
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X] at hi
  have hz := integral_eq_zero_of_hasDerivAt_of_integrable hd hi (integrable_weighted p)
  have hc : ∀ x : ℝ, gaussianPDFReal 0 1 x = (Real.sqrt (2 * Real.pi))⁻¹ * weight x := by
    intro x
    simp [gaussianPDFReal, weight, neg_div]
  have hp := integrable_weighted p.derivative
  have hxp := integrable_weighted (Polynomial.X * p)
  simp only [Polynomial.eval_mul, Polynomial.eval_X] at hxp
  simp_rw [sub_mul] at hz
  rw [integral_sub hp hxp] at hz
  rw [integral_gaussianReal_eq_integral_smul (v := 1) (by norm_num),
    integral_gaussianReal_eq_integral_smul (v := 1) (by norm_num)]
  simp_rw [hc, smul_eq_mul, mul_assoc, mul_comm (weight _) (_ : ℝ)]
  rw [integral_const_mul, integral_const_mul]
  congr 1
  linarith

/-- Raising a Hermite index is adjoint to differentiating the other polynomial. -/
theorem raising (n : ℕ) (p : Polynomial ℝ) :
    (∫ x, (hp (n + 1)).eval x * p.eval x ∂gaussianReal 0 1) =
      ∫ x, (hp n).eval x * p.derivative.eval x ∂gaussianReal 0 1 := by
  have h := stein (hp n * p)
  simp only [Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul] at h
  have hi1 := integrable_eval ((hp n).derivative * p)
  have hi2 := integrable_eval (hp n * p.derivative)
  have hi3 := integrable_eval (Polynomial.X * hp n * p)
  simp only [Polynomial.eval_mul, Polynomial.eval_X] at hi1 hi2 hi3
  rw [integral_add hi1 hi2] at h
  simp only [hp_succ, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X, sub_mul]
  rw [integral_sub hi3 hi1]
  simp only [mul_assoc] at *
  linarith

@[simp] theorem hp_integral (n : ℕ) :
    (∫ x, (hp n).eval x ∂gaussianReal 0 1) = if n = 0 then 1 else 0 := by
  cases n with
  | zero => simp
  | succ n =>
    have h := raising n 1
    simpa using h

/-- Actual Gaussian L² orthogonality, including the exact factorial normalization. -/
theorem orthogonal (n k : ℕ) :
    (∫ x, (hp n).eval x * (hp k).eval x ∂gaussianReal 0 1) =
      if n = k then (n.factorial : ℝ) else 0 := by
  induction n generalizing k with
  | zero =>
    simp only [hp_zero, Polynomial.eval_one, one_mul, hp_integral]
    by_cases hk : k = 0 <;> simp [hk, eq_comm]
  | succ n ih =>
    rw [raising]
    cases k with
    | zero => simp
    | succ k =>
      simp only [hp_derivative, Polynomial.eval_mul, Polynomial.eval_C]
      simp_rw [mul_left_comm ((hp n).eval _) (k + 1 : ℝ)]
      rw [integral_const_mul, ih]
      by_cases hnk : n = k
      · subst k
        simp [Nat.factorial_succ]
      · simp [hnk]

theorem hp_derivative_all (n : ℕ) : (hp n).derivative = Polynomial.C (n : ℝ) * hp (n - 1) := by
  cases n with
  | zero => simp
  | succ n => simpa using hp_derivative n

/-- Exact Gaussian inner product of Hermite derivatives. -/
theorem derivative_orthogonal (n k : ℕ) :
    (∫ x, (hp n).derivative.eval x * (hp k).derivative.eval x ∂gaussianReal 0 1) =
      if n = k then (n : ℝ) * n.factorial else 0 := by
  cases n with
  | zero => simp
  | succ n =>
    cases k with
    | zero => simp
    | succ k =>
      simp only [hp_derivative, Polynomial.eval_mul, Polynomial.eval_C]
      have he : ∀ x : ℝ, ((n + 1 : ℝ) * (hp n).eval x) * ((k + 1 : ℝ) * (hp k).eval x) =
          ((n + 1 : ℝ) * (k + 1 : ℝ)) * ((hp n).eval x * (hp k).eval x) := by intro x; ring
      simp_rw [he]
      rw [integral_const_mul, orthogonal]
      by_cases hnk : n = k
      · subst k
        simp [Nat.factorial_succ]
        ring
      · simp [hnk]

end Hermite
end Paper10
