import Paper20.Phi

namespace Paper20.Phi
open Polynomial
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

lemma C_two : C (2:ℚ) = (2:ℚ[X]) := by
  calc
    _ = C ((1:ℚ)+1) := by congr 1; norm_num
    _ = C 1+C 1 := map_add C 1 1
    _ = 2 := by rw [map_one]; exact one_add_one_eq_two

lemma derivative_affine : affine.derivative = C (1/2 : ℚ) := by
  simp [affine]

lemma derivative_comp_affine (P : ℚ[X]) :
    (P.comp affine).derivative = C (1/2 : ℚ) * P.derivative.comp affine := by
  rw [derivative_comp, derivative_affine]

lemma derivative_twice_comp_affine (P : ℚ[X]) :
    (P.comp affine).derivative.derivative =
      C (1/4 : ℚ) * P.derivative.derivative.comp affine := by
  rw [derivative_comp_affine, derivative_mul, derivative_C, zero_mul, zero_add,
    derivative_comp_affine]
  rw [← mul_assoc, ← C_mul]
  norm_num

/-- The change of variable in the normalized quantum numerator equation. -/
theorem affine_ode (P : ℚ[X]) (e κ : ℚ)
    (h : (1-X^2)*P.derivative.derivative +
      (C e-C (e+1)*X)*P.derivative + C κ*P = 0) :
    X*(X+4)*(P.comp affine).derivative.derivative +
      (C (e+1)*X+2)*(P.comp affine).derivative - C κ*P.comp affine = 0 := by
  have hc := congrArg (fun p : ℚ[X] => p.comp affine) h
  simp only [add_comp, sub_comp, mul_comp, pow_comp, one_comp, X_comp, C_comp,
    zero_comp] at hc
  rw [derivative_twice_comp_affine, derivative_comp_affine]
  dsimp only [affine] at hc ⊢
  have he : C (e+1) = C e + (1 : ℚ[X]) := by simp
  rw [he] at hc ⊢
  have hh : 2*C (1/2:ℚ)-1 = (0:ℚ[X]) := by
    have hh' : C (2:ℚ)*C (1/2:ℚ) = C (1:ℚ) := by rw [← C_mul]; norm_num
    rw [C_two, map_one] at hh'
    exact sub_eq_zero.mpr hh'
  have hq : C (1/4:ℚ)-C (1/2:ℚ)^2 = (0:ℚ[X]) := by
    norm_num [← C_pow, ← C_sub]
  linear_combination (norm := ring_nf) -hc +
    (4*X*(P.derivative.derivative.comp (1+C (1/2:ℚ)*X)) +
      X^2*(P.derivative.derivative.comp (1+C (1/2:ℚ)*X)))*hq +
    (2*C (1/2:ℚ)*X*(P.derivative.derivative.comp (1+C (1/2:ℚ)*X)) +
      P.derivative.comp (1+C (1/2:ℚ)*X))*hh

theorem even_ode (n : ℕ) :
    X*(X+4)*(even n).derivative.derivative +
      (X+2)*(even n).derivative - C ((n:ℚ)^2)*even n = 0 := by
  have h := affine_ode (T (n:ℤ)) 0 ((n:ℚ)^2) (by simpa using T_ode (n:ℤ))
  simpa [even] using h

theorem odd_affine_ode (n : ℕ) :
    X*(X+4)*(odd n).derivative.derivative +
      (2*X+2)*(odd n).derivative - C ((n:ℚ)*(n+1))*odd n = 0 := by
  have h := affine_ode (U (n:ℤ)-U ((n:ℤ)-1)) 1 ((n:ℚ)*(n+1))
    (by convert odd_ode (n:ℤ) using 1 <;> norm_num [C_two])
  convert h using 1 <;> norm_num [odd, C_two]

lemma coeff_X_derivative (P : ℚ[X]) (j : ℕ) :
    (X*P.derivative).coeff j = (j:ℚ)*P.coeff j := by
  cases j with
  | zero => simp
  | succ j => rw [coeff_X_mul, coeff_derivative]; push_cast; ring

lemma coeff_X_sq_derivative_twice (P : ℚ[X]) (j : ℕ) :
    (X^2*P.derivative.derivative).coeff j =
      (j:ℚ)*((j:ℚ)-1)*P.coeff j := by
  rcases j with _ | _ | j
  · simp
  · simp [coeff_X_pow_mul']
  · rw [show j+1+1=j+2 by omega, coeff_X_pow_mul, coeff_derivative,
      coeff_derivative]
    push_cast
    ring

/-- Exact coefficient recurrence from the polynomial differential equation. -/
theorem ode_coeff_recurrence (P : ℚ[X]) (e κ : ℚ)
    (h : X*(X+4)*P.derivative.derivative +
      (C (e+1)*X+2)*P.derivative - C κ*P = 0) (j : ℕ) :
    2*(j+1:ℚ)*(2*j+1)*P.coeff (j+1) =
      (κ-(j:ℚ)*((j:ℚ)+e))*P.coeff j := by
  have hc := congrArg (fun p : ℚ[X] => p.coeff j) h
  have hs : X*(X+4)*P.derivative.derivative +
      (C (e+1)*X+2)*P.derivative - C κ*P =
      X^2*P.derivative.derivative + 4*(X*P.derivative.derivative) +
      C (e+1)*(X*P.derivative) + 2*P.derivative - C κ*P := by ring
  rw [hs] at hc
  simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
    coeff_X_sq_derivative_twice, coeff_X_derivative, coeff_derivative, coeff_zero] at hc
  push_cast at hc ⊢
  linear_combination (norm := ring_nf) hc

theorem even_coeff_recurrence (n j : ℕ) :
    2*(j+1:ℚ)*(2*j+1)*(even n).coeff (j+1) =
      ((n:ℚ)^2-(j:ℚ)^2)*(even n).coeff j := by
  have h := ode_coeff_recurrence (even n) 0 ((n:ℚ)^2) (by simpa using even_ode n) j
  convert h using 1 <;> ring

theorem odd_coeff_recurrence (n j : ℕ) :
    2*(j+1:ℚ)*(2*j+1)*(odd n).coeff (j+1) =
      ((n:ℚ)*(n+1)-(j:ℚ)*(j+1))*(odd n).coeff j := by
  exact ode_coeff_recurrence (odd n) 1 ((n:ℚ)*(n+1))
    (by convert odd_affine_ode n using 1 <;> norm_num [C_two]) j

end
end Paper20.Phi
