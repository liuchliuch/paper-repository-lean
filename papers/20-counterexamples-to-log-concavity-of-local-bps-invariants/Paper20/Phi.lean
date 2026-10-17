import Paper20.Polynomial

/-! Polynomial numerator identities underlying (19)--(21). We use the
existing Chebyshev polynomials to prove the source differential equations
algebraically, without assuming the desired BPS coefficient formula. -/
namespace Paper20.Phi
open Polynomial
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

abbrev T (n : ℤ) : ℚ[X] := Polynomial.Chebyshev.T ℚ n
abbrev U (n : ℤ) : ℚ[X] := Polynomial.Chebyshev.U ℚ n

theorem T_ode (n : ℤ) :
    (1-X^2)*(T n).derivative.derivative - X*(T n).derivative +
      (n:ℚ[X])^2*T n = 0 := by
  have hd : (T n).derivative = (n:ℚ[X])*U (n-1) :=
    Polynomial.Chebyshev.T_derivative_eq_U n
  have hdd : (T n).derivative.derivative = (n:ℚ[X])*(U (n-1)).derivative := by
    rw [hd, derivative_mul]
    simp
  have h := Polynomial.Chebyshev.add_one_mul_T_eq_poly_in_U (R := ℚ) (n-1)
  rw [sub_add_cancel] at h
  push_cast at h
  rw [hdd,hd]
  dsimp only [T,U] at h ⊢
  linear_combination (norm := ring_nf) (n:ℚ[X])*h

lemma U_derivative_relation (n : ℤ) :
    (1-X^2)*(U n).derivative = -(n:ℚ[X])*X*U n + (n+1:ℚ[X])*U (n-1) := by
  have ht : T (n+1) = X*U n-U (n-1) := by
    have h1 := Polynomial.Chebyshev.U_eq_X_mul_U_add_T ℚ n
    have h2 := Polynomial.Chebyshev.U_eq ℚ (n+1)
    rw [show n+1-1=n by omega, show n+1-2=n-1 by omega] at h2
    linear_combination (norm := ring_nf) h2-h1
  have h := Polynomial.Chebyshev.add_one_mul_T_eq_poly_in_U (R := ℚ) n
  dsimp only [T,U] at ht
  rw [ht] at h
  dsimp only [T,U] at h ⊢
  linear_combination (norm := (push_cast; ring_nf)) h

lemma one_sub_X_ne : (1-(X:ℚ[X])) ≠ 0 := by
  intro h
  have hc := congrArg (fun p : ℚ[X] => p.coeff 1) h
  norm_num [Polynomial.coeff_one] at hc

lemma one_add_X_ne : (1+(X:ℚ[X])) ≠ 0 := by
  intro h
  have hc := congrArg (fun p : ℚ[X] => p.coeff 1) h
  norm_num [Polynomial.coeff_one] at hc

/-- First-order identity for the normalized odd numerator. -/
theorem odd_first_order (n : ℤ) :
    (1+X)*(U n-U (n-1)).derivative =
      (n:ℚ[X])*U n+(n+1:ℚ[X])*U (n-1) := by
  have ha := U_derivative_relation n
  have hb := U_derivative_relation (n-1)
  rw [show n-1-1=n-2 by omega] at hb
  have hu := Polynomial.Chebyshev.U_eq ℚ n
  have ht := Polynomial.Chebyshev.T_eq_U_sub_X_mul_U ℚ n
  -- Rewrite the lower neighboring U polynomial using the three-term recurrence.
  have hb' : (1-X^2)*(U (n-1)).derivative =
      -(n:ℚ[X])*U n+(n+1:ℚ[X])*X*U (n-1) := by
    dsimp only [T,U] at hb hu ⊢
    linear_combination (norm := (push_cast; ring_nf)) hb+(n:ℚ[X])*hu
  have hc : (1-X)*((1+X)*(U n-U (n-1)).derivative -
      ((n:ℚ[X])*U n+(n+1:ℚ[X])*U (n-1))) = 0 := by
    simp only [derivative_sub]
    dsimp only [T,U] at ha hb' ⊢
    linear_combination (norm := ring_nf) ha-hb'
  exact sub_eq_zero.mp ((mul_eq_zero.mp hc).resolve_left one_sub_X_ne)

/-- Differential equation for the normalized odd numerator before the affine
change of variable `y=1+w/2`. -/
theorem odd_ode (n : ℤ) :
    (1-X^2)*(U n-U (n-1)).derivative.derivative +
      (1-2*X)*(U n-U (n-1)).derivative +
      (n:ℚ[X])*(n+1:ℚ[X])*(U n-U (n-1)) = 0 := by
  have hp := odd_first_order n
  have hdp := congrArg Polynomial.derivative hp
  simp only [derivative_mul, derivative_add, derivative_one, derivative_X,
    zero_add, one_mul, derivative_intCast, zero_mul, zero_add] at hdp
  have ha := U_derivative_relation n
  have hb := U_derivative_relation (n-1)
  have hu := Polynomial.Chebyshev.U_eq ℚ n
  have hb' : (1-X^2)*(U (n-1)).derivative =
      -(n:ℚ[X])*U n+(n+1:ℚ[X])*X*U (n-1) := by
    rw [show n-1-1=n-2 by omega] at hb
    dsimp only [T,U] at hb hu ⊢
    linear_combination (norm := (push_cast; ring_nf)) hb+(n:ℚ[X])*hu
  have hc : (1+X)*((1-X^2)*(U n-U (n-1)).derivative.derivative +
      (1-2*X)*(U n-U (n-1)).derivative +
      (n:ℚ[X])*(n+1:ℚ[X])*(U n-U (n-1))) = 0 := by
    dsimp only [T,U] at hdp ha hb' hp ⊢
    linear_combination (norm := ring_nf)
      (1-(X:ℚ[X])^2)*hdp+(n:ℚ[X])*ha+(n+1:ℚ[X])*hb'-X*hp
  exact (mul_eq_zero.mp hc).resolve_left one_add_X_ne

/-- The affine variable in which normalized quantum numerators are polynomials. -/
def affine : ℚ[X] := 1+C (1/2 : ℚ)*X

def even (n : ℕ) : ℚ[X] := (T (n:ℤ)).comp affine

def odd (n : ℕ) : ℚ[X] := (U (n:ℤ)-U ((n:ℤ)-1)).comp affine

@[simp] theorem even_zero_value (n : ℕ) : (even n).eval 0 = 1 := by
  simp [even, affine, Polynomial.eval_comp, Polynomial.Chebyshev.T_eval_one]

@[simp] theorem odd_zero_value (n : ℕ) : (odd n).eval 0 = 1 := by
  simp [odd, affine, Polynomial.eval_comp, Polynomial.Chebyshev.U_eval_one]
  all_goals (push_cast; ring)

end
end Paper20.Phi
