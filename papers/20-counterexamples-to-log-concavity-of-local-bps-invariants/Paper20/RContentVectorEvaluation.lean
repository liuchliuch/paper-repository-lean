import Paper20.RContentReconstruction

namespace Paper20.RContent36
open Polynomial Finset
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

lemma integer_add_getD (xs ys : List ℤ) (i : ℕ) :
    (IntegerPolynomial.add xs ys).getD i 0=xs.getD i 0+ys.getD i 0 := by
  have he := congrArg (fun p : ℚ[X] => p.coeff i) (IntegerPolynomial.polynomial_add xs ys)
  simpa only [Polynomial.coeff_add,IntegerPolynomial.polynomial_coeff,← Int.cast_add,
    Int.cast_inj] using he

lemma integer_scale_getD (a : ℤ) (xs : List ℤ) (i : ℕ) :
    (IntegerPolynomial.scale a xs).getD i 0=a*xs.getD i 0 := by
  have he := congrArg (fun p : ℚ[X] => p.coeff i) (IntegerPolynomial.polynomial_scale a xs)
  simpa only [Polynomial.coeff_C_mul,IntegerPolynomial.polynomial_coeff,← Int.cast_mul,
    Int.cast_inj] using he

/-- Streaming integer evaluation: advance A_j once while accumulating the
whole coefficient vector for a single actual content/R row. -/
def vectorState (c : ℕ) (rs : List ℤ) (h : ℕ) : ℕ → List ℤ × List ℤ
  | 0 => ([1],[])
  | j+1 =>
    let p := vectorState c rs h j
    (IntegerPolynomial.mul p.1
        (IntegerPolynomial.numeratorFactor ((c:ℤ)^2) (decide (c%2=0)) (j+1)),
      IntegerPolynomial.add p.2
        (IntegerPolynomial.scale (rs.getD (h-j) 0*(FastQ36.cofactor h j:ℤ)) p.1))

lemma vectorState_first (c : ℕ) (rs : List ℤ) (h j : ℕ) :
    (vectorState c rs h j).1=
      IntegerPolynomial.numeratorA ((c:ℤ)^2) (decide (c%2=0)) j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [vectorState,IntegerPolynomial.numeratorA,ih]

lemma vectorState_second (c : ℕ) (rs : List ℤ) (h j i : ℕ) :
    (vectorState c rs h j).2.getD i 0 =
      ∑ t ∈ range j, rs.getD (h-t) 0*aWeight h i t c := by
  induction j with
  | zero => simp [vectorState]
  | succ j ih =>
    rw [vectorState,integer_add_getD,integer_scale_getD,vectorState_first,ih,
      Finset.sum_range_succ]
    unfold aWeight
    ring

def rowVector (p : ℕ × List ℤ) (h : ℕ) : List ℤ := (vectorState p.1 p.2 h (h+1)).2

def evaluateVector (s : State) (h : ℕ) : List ℤ :=
  s.foldr (fun p acc => IntegerPolynomial.add (rowVector p h) acc) []

lemma evaluateVector_sum (s : State) (h i : ℕ) :
    (evaluateVector s h).getD i 0=
      (s.map (fun p => ∑ j ∈ range (h+1), p.2.getD (h-j) 0*aWeight h i j p.1)).sum := by
  induction s with
  | nil => simp [evaluateVector]
  | cons p s ih =>
    rw [evaluateVector,List.foldr_cons,integer_add_getD]
    change (rowVector p h).getD i 0+(evaluateVector s h).getD i 0 = _
    rw [rowVector,vectorState_second,ih]
    rfl

/-- The whole-vector evaluator is exactly the already proved complete
partition reconstruction, at every coefficient and without a cache premise. -/
theorem evaluateVector_correct (s : State) (h i : ℕ) :
    (evaluateVector s h).getD i 0=evaluate s h i := by
  rw [evaluateVector_sum,evaluate,sum_map_range_int,range_sum_list_comm]

theorem evaluateVector_scaled (s : State) (hs : Correct root s)
    (hb : ∀ p ∈ s, p.1 ≤ 630) (h i : ℕ) (hh : h ≤ 22) :
    ((evaluateVector s h).getD i 0:ℚ)=
      (FastQ36.denominator h:ℚ)*((36:ℕ).factorial:ℚ)*cget (Qcoeff 36 h) i := by
  rw [evaluateVector_correct]
  exact evaluate_scaled s hs hb h i hh

end
end Paper20.RContent36
