import Paper20.Polynomial

namespace Paper20
open Polynomial
noncomputable section
set_option maxHeartbeats 1000000

/-- The executable coefficient lists interpreted as ordinary polynomials. -/
def listPolynomial : List ℚ → ℚ[X]
  | [] => 0
  | a :: as => C a + X * listPolynomial as

@[simp] theorem coeff_listPolynomial (cs : List ℚ) (j : ℕ) :
    (listPolynomial cs).coeff j = cget cs j := by
  induction cs generalizing j with
  | nil => simp [listPolynomial]
  | cons a as ih =>
    cases j with
    | zero => simp [listPolynomial]
    | succ j => simp [listPolynomial, coeff_X_mul, ih]

@[simp] theorem eval_listPolynomial (cs : List ℚ) (x : ℚ) :
    (listPolynomial cs).eval x = peval cs x := by
  induction cs with
  | nil => simp [listPolynomial]
  | cons a as ih => simp [listPolynomial, peval, ih]

theorem listPolynomial_padd (a b : List ℚ) :
    listPolynomial (padd a b) = listPolynomial a + listPolynomial b := by
  ext j
  simp [cget_padd]

theorem listPolynomial_psmul (s : ℚ) (a : List ℚ) :
    listPolynomial (psmul s a) = C s * listPolynomial a := by
  ext j
  simp [cget_psmul, coeff_C_mul]

theorem listPolynomial_pmul (a b : List ℚ) :
    listPolynomial (pmul a b) = listPolynomial a * listPolynomial b := by
  ext j
  rw [coeff_listPolynomial, cget_pmul, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i k => (listPolynomial a).coeff i * (listPolynomial b).coeff k) j]
  simp only [coeff_listPolynomial]
  have hs : ∀ m, ((List.range m).map (fun i => cget a i*cget b (j-i))).sum =
      ∑ i ∈ Finset.range m, cget a i*cget b (j-i) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => simp [List.range_succ, Finset.sum_range_succ, ih]
  exact hs _

theorem peval_padd (a b : List ℚ) (x : ℚ) :
    peval (padd a b) x = peval a x + peval b x := by
  simpa using congrArg (fun p : ℚ[X] => p.eval x) (listPolynomial_padd a b)

theorem peval_psmul (s : ℚ) (a : List ℚ) (x : ℚ) :
    peval (psmul s a) x = s * peval a x := by
  simpa using congrArg (fun p : ℚ[X] => p.eval x) (listPolynomial_psmul s a)

theorem peval_pmul (a b : List ℚ) (x : ℚ) :
    peval (pmul a b) x = peval a x * peval b x := by
  simpa using congrArg (fun p : ℚ[X] => p.eval x) (listPolynomial_pmul a b)

theorem peval_Afactor (c2 : ℤ) (ev : Bool) (j : ℕ) (x : ℚ) :
    peval (Afactor c2 ev j) x =
      ((c2:ℚ)*(4*x+1)-(At ev j:ℚ)^2) /
        (4*(2*j:ℕ)*(2*j-1):ℕ) := by
  simp only [Afactor, peval_cons, peval_nil, mul_zero, add_zero]
  push_cast
  ring

/-- Evaluation of the exact executable recurrence (19). -/
theorem peval_Apoly_succ (c2 : ℤ) (ev : Bool) (j : ℕ) (x : ℚ) :
    peval (Apoly c2 ev (j+1)) x = peval (Apoly c2 ev j) x *
      (((c2:ℚ)*(4*x+1)-(At ev (j+1):ℚ)^2) /
        (4*(2*(j+1):ℕ)*(2*(j+1)-1):ℕ)) := by
  rw [Apoly_succ, peval_pmul, peval_Afactor]

end
end Paper20
