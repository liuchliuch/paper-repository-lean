import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# The quadratic Taylor coefficient in Appendix A

A polynomial is used only as a finite Taylor jet. The coefficient calculation
allows arbitrary intermediate coefficients of the third retraction. Obtaining
these jets from the actual holomorphic coordinate changes and gluing the
resulting connection are geometric obligations, not assumptions hidden here.
-/

noncomputable section
namespace Paper27.JetCalculation
open Polynomial

/-- When the first possible coefficient is in degree `n`, the coefficient in
`F²` at degree `2n` is the square of the coefficient in degree `n`. -/
theorem square_coeff_double (F : ℂ[X]) (n : ℕ)
    (hF : ∀ j < n, F.coeff j = 0) : (F ^ 2).coeff (2 * n) = (F.coeff n) ^ 2 := by
  rw [pow_two, coeff_mul]
  calc
    ∑ p ∈ Finset.antidiagonal (2 * n), F.coeff p.1 * F.coeff p.2 =
        F.coeff n * F.coeff n := by
      apply Finset.sum_eq_single (n, n)
      · intro p hp hpn
        have hp' : p.1 + p.2 = 2 * n := Finset.mem_antidiagonal.mp hp
        by_cases h₁ : p.1 < n
        · rw [hF _ h₁, zero_mul]
        · have h₂ : p.2 < n := by
            have hn : p.1 ≠ n ∨ p.2 ≠ n := by
              by_contra h
              push_neg at h
              exact hpn (Prod.ext h.1 h.2)
            omega
          rw [hF _ h₂, mul_zero]
      · intro hn
        exact False.elim (hn (Finset.mem_antidiagonal.mpr (by omega)))
    _ = (F.coeff n) ^ 2 := (pow_two _).symm

/-- The degree-`2n` coefficient of the second order Taylor polynomial of a
coordinate change composed with a perturbation of order at least `n`. -/
theorem target_composition_coeff (F : ℂ[X]) (n : ℕ) (p q : ℂ)
    (hF : ∀ j < n, F.coeff j = 0) :
    (C p * F + C (q / 2) * F ^ 2).coeff (2 * n) =
      p * F.coeff (2 * n) + q / 2 * (F.coeff n) ^ 2 := by
  simp only [coeff_add, coeff_C_mul, square_coeff_double F n hF]

/-- Both sides of the coordinate compatibility have this quadratic coefficient.
This is the scalar rearrangement from the displayed comparison to (7). -/
theorem equation_seven (a p q b b' : ℂ)
    (h : a / 2 * q + b' * p ^ 2 = p * b + a ^ 2 / 2 * q) :
    b' * p ^ 2 = p * b + (a ^ 2 - a) / 2 * q := by
  linear_combination h

/-- The denominator used to define the local connection coefficients is a unit. -/
theorem connection_denominator_ne_zero (a : ℂ) (h₀ : a ≠ 0) (h₁ : a ≠ 1) :
    a ^ 2 - a ≠ 0 := by
  rw [show a ^ 2 - a = a * (a - 1) by ring]
  exact mul_ne_zero h₀ (sub_ne_zero.mpr h₁)

/-- Equation (7) yields exactly the transformation law for Γ in Appendix A.
This does not assume or assert that a holomorphic connection has been glued. -/
theorem connection_coefficient_law (a p q b b' : ℂ) (h₀ : a ≠ 0) (h₁ : a ≠ 1)
    (h : b' * p ^ 2 = p * b + (a ^ 2 - a) / 2 * q) :
    (-2 * b' / (a ^ 2 - a)) * p ^ 2 =
      p * (-2 * b / (a ^ 2 - a)) - q := by
  have hne := connection_denominator_ne_zero a h₀ h₁
  have heq : (-2 * b') * p ^ 2 = p * (-2 * b) - q * (a ^ 2 - a) := by
    linear_combination -2 * h
  calc
    (-2 * b' / (a ^ 2 - a)) * p ^ 2 = (-2 * b' * p ^ 2) / (a ^ 2 - a) := by ring
    _ = (p * (-2 * b) - q * (a ^ 2 - a)) / (a ^ 2 - a) := congrArg (· / (a ^ 2 - a)) heq
    _ = p * (-2 * b / (a ^ 2 - a)) - q := by
      rw [sub_div, mul_div_assoc, mul_div_cancel_right₀ _ hne]

end Paper27.JetCalculation
