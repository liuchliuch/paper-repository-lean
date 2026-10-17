import Paper20.PolynomialEval

/-! Correctness of the executable logarithmic-derivative recurrence used
in the actual hook series, (28). -/
namespace Paper20.LogSeries
open Finset
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

def polynomialSeries (D : List ℚ) : PowerSeries ℚ := (listPolynomial D : PowerSeries ℚ)

@[simp] theorem coeff_polynomialSeries (D : List ℚ) (i : ℕ) :
    PowerSeries.coeff i (polynomialSeries D) = D.getD i 0 := by
  simp [polynomialSeries, PowerSeries.coeff_coe, cget]

@[simp] theorem constant_polynomialSeries (D : List ℚ) :
    PowerSeries.constantCoeff (polynomialSeries D) = D.getD 0 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_polynomialSeries]

def negativeLog (D : List ℚ) : PowerSeries ℚ :=
  -(PowerSeries.derivative ℚ (polynomialSeries D))*(polynomialSeries D)⁻¹

theorem negativeLog_identity (D : List ℚ) (hD : D.getD 0 0 ≠ 0) :
    polynomialSeries D*negativeLog D =
      -(PowerSeries.derivative ℚ (polynomialSeries D)) := by
  have hi := PowerSeries.mul_inv_cancel (polynomialSeries D) (by simpa using hD)
  calc
    _ = -(PowerSeries.derivative ℚ (polynomialSeries D))*
      (polynomialSeries D*(polynomialSeries D)⁻¹) := by unfold negativeLog; ring
    _ = _ := by rw [hi, mul_one]

lemma sum_map_range (f : ℕ → ℚ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

theorem negativeLog_recurrence (D : List ℚ) (hD : D.getD 0 0 ≠ 0) (j : ℕ) :
    PowerSeries.coeff j (negativeLog D) =
      (-(j+1:ℚ)*D.getD (j+1) 0-
        ((List.range j).map (fun t => D.getD (t+1) 0*
          PowerSeries.coeff (j-1-t) (negativeLog D))).sum) / D.getD 0 0 := by
  have hc := congrArg (PowerSeries.coeff j) (negativeLog_identity D hD)
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    map_neg, PowerSeries.coeff_derivative] at hc
  simp only [coeff_polynomialSeries] at hc
  rw [Finset.sum_range_succ'] at hc
  simp only [Nat.sub_zero] at hc
  have hs : (∑ t ∈ range j, D.getD (t+1) 0*
        PowerSeries.coeff (j-(t+1)) (negativeLog D)) =
      ((List.range j).map (fun t => D.getD (t+1) 0*
        PowerSeries.coeff (j-1-t) (negativeLog D))).sum := by
    rw [sum_map_range]
    apply Finset.sum_congr rfl
    intro t ht
    rw [show j-(t+1)=j-1-t by omega]
  rw [hs] at hc
  apply (eq_div_iff hD).2
  push_cast at hc ⊢
  linear_combination (norm := ring_nf) hc

@[simp] theorem negDLog_length (D : List ℚ) (H : ℕ) : (negDLog D H).length = H := by
  induction H with
  | zero => rfl
  | succ H ih => simp only [negDLog, List.length_append, List.length_cons,
      List.length_nil, ih]

/-- Every retained coefficient of the actual `negDLog` loop is `-D'/D`. -/
theorem negDLog_correct (D : List ℚ) (hD : D.getD 0 0 ≠ 0)
    (H j : ℕ) (hj : j < H) :
    (negDLog D H).getD j 0 = PowerSeries.coeff j (negativeLog D) := by
  induction H generalizing j with
  | zero => omega
  | succ H ih =>
    rw [negDLog]
    by_cases hlt : j < H
    · rw [List.getD_append _ _ _ _ (by simpa using hlt)]
      exact ih j hlt
    · have he : j=H := by omega
      subst j
      rw [List.getD_append_right _ _ _ _ (by simp), negDLog_length,
        Nat.sub_self]
      simp only [List.getD_cons_zero]
      rw [negativeLog_recurrence D hD H]
      congr 2
      apply congrArg List.sum
      apply List.map_congr_left
      intro t ht
      rw [ih (H-1-t) (by have := List.mem_range.mp ht; omega)]

end
end Paper20.LogSeries
