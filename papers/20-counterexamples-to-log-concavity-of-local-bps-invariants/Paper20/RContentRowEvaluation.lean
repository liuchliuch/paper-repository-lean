import Paper20.RContentFastVector

namespace Paper20.RContent36
noncomputable section

/-- Reuse separately checked row vectors under the exact original finite
sum. No arithmetic or partition identity is assumed in this congruence. -/
theorem evaluateFastVector_of_rows (s : State) (h : ℕ) (vs : List (List ℤ))
    (hv : List.Forall₂ (fun p v => fastRowVector p h=v) s vs) :
    evaluateFastVector s h=sumVectors vs id := by
  induction hv with
  | nil => rfl
  | cons hp ht ih =>
    change IntegerPolynomial.add (fastRowVector _ h) (evaluateFastVector _ h)=
      IntegerPolynomial.add _ (sumVectors _ id)
    rw [hp,ih]
    rfl

end
end Paper20.RContent36
