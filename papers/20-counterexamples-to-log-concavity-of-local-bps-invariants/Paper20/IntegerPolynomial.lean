import Paper20.PolynomialEval

namespace Paper20.IntegerPolynomial
open Polynomial
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

def add : List ℤ → List ℤ → List ℤ
  | [], b => b
  | a, [] => a
  | x::xs, y::ys => (x+y)::add xs ys

def scale (s : ℤ) : List ℤ → List ℤ
  | [] => []
  | x::xs => s*x::scale s xs

def mul : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | x::xs, b => add (scale x b) (0::mul xs b)

def polynomial : List ℤ → ℚ[X]
  | [] => 0
  | x::xs => C (x:ℚ)+X*polynomial xs

theorem polynomial_add (a b : List ℤ) :
    polynomial (add a b) = polynomial a+polynomial b := by
  induction a generalizing b with
  | nil => simp [add,polynomial]
  | cons x xs ih =>
    cases b with
    | nil => simp [add,polynomial]
    | cons y ys => simp only [add,polynomial,ih,Int.cast_add,map_add]; ring

theorem polynomial_scale (s : ℤ) (a : List ℤ) :
    polynomial (scale s a) = C (s:ℚ)*polynomial a := by
  induction a with
  | nil => simp [scale,polynomial]
  | cons x xs ih => simp only [scale,polynomial,ih,Int.cast_mul,map_mul]; ring

theorem polynomial_mul (a b : List ℤ) :
    polynomial (mul a b) = polynomial a*polynomial b := by
  induction a with
  | nil => simp [mul,polynomial]
  | cons x xs ih =>
    rw [mul,polynomial_add,polynomial_scale]
    simp only [polynomial,Int.cast_zero,map_zero,zero_add,ih]
    ring

@[simp] theorem polynomial_coeff (a : List ℤ) (j : ℕ) :
    (polynomial a).coeff j = (a.getD j 0:ℚ) := by
  induction a generalizing j with
  | nil => simp [polynomial]
  | cons x xs ih =>
    cases j with
    | zero => simp [polynomial]
    | succ j =>
      rw [polynomial,coeff_add,coeff_C,if_neg (by omega),zero_add,coeff_X_mul,ih]
      rfl

def numeratorFactor (c2 : ℤ) (ev : Bool) (j : ℕ) : List ℤ :=
  [c2-((At ev j:ℕ):ℤ)^2,4*c2]

def numeratorA (c2 : ℤ) (ev : Bool) : ℕ → List ℤ
  | 0 => [1]
  | j+1 => mul (numeratorA c2 ev j) (numeratorFactor c2 ev (j+1))

def denominatorA (j : ℕ) : ℕ := 4^j*(2*j).factorial

theorem denominatorA_pos (j : ℕ) : 0 < denominatorA j := by
  unfold denominatorA
  positivity

theorem denominatorA_succ (j : ℕ) :
    denominatorA (j+1) = denominatorA j*(4*(2*(j+1))*(2*(j+1)-1)) := by
  unfold denominatorA
  rw [show 2*(j+1)=2*j+2 by omega, show 2*j+2-1=2*j+1 by omega,
    Nat.factorial_succ, Nat.factorial_succ, pow_succ]
  ring

theorem factor_scaled (c2 : ℤ) (ev : Bool) (j : ℕ) (hj : 0 < j) :
    C ((4*(2*j)*(2*j-1):ℕ):ℚ)*listPolynomial (Afactor c2 ev j) =
      polynomial (numeratorFactor c2 ev j) := by
  have ht : 0 < 2*j-1 := by omega
  have hden : ((4*(2*j)*(2*j-1):ℕ):ℚ) ≠ 0 := by positivity
  ext i
  by_cases hi : i=0
  · subst i
    simp only [coeff_C_mul,coeff_listPolynomial,cget_Afactor_zero,numeratorFactor,
      polynomial_coeff,List.getD_cons_zero]
    field_simp [hden] <;> push_cast <;> ring
  · by_cases hi1 : i=1
    · subst i
      simp only [coeff_C_mul,coeff_listPolynomial,cget_Afactor_one,numeratorFactor,
      polynomial_coeff,List.getD_cons_succ,List.getD_cons_zero]
      field_simp [hden] <;> push_cast <;> ring
    · rw [coeff_C_mul,coeff_listPolynomial,cget_Afactor_ge_two _ _ _ _ (by omega)]
      rw [polynomial_coeff]
      have hlen : (numeratorFactor c2 ev j).length=2 := rfl
      rw [List.getD_eq_default _ _ (by omega), Int.cast_zero, mul_zero]

/-- The integer numerator recurrence is exactly the actual Apoly after
scaling by `4^j (2j)!`; it does not define a substitute polynomial. -/
theorem numeratorA_correct (c2 : ℤ) (ev : Bool) (j : ℕ) :
    polynomial (numeratorA c2 ev j) =
      C (denominatorA j:ℚ)*listPolynomial (Apoly c2 ev j) := by
  induction j with
  | zero => simp [numeratorA,denominatorA,polynomial,listPolynomial,Apoly]
  | succ j ih =>
    rw [numeratorA,polynomial_mul,ih,← factor_scaled c2 ev (j+1) (by omega),
      Apoly_succ,listPolynomial_pmul,denominatorA_succ]
    push_cast
    simp only [map_mul]
    ring

theorem numeratorA_coeff (c2 : ℤ) (ev : Bool) (j i : ℕ) :
    ((numeratorA c2 ev j).getD i 0:ℚ) =
      (denominatorA j:ℚ)*cget (Apoly c2 ev j) i := by
  have h := congrArg (fun p : ℚ[X] => p.coeff i) (numeratorA_correct c2 ev j)
  simpa only [polynomial_coeff,coeff_C_mul,coeff_listPolynomial] using h

end
end Paper20.IntegerPolynomial
