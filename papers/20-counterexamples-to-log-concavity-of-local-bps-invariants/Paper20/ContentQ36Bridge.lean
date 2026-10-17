import Paper20.Certs.ContentQ36Rows.All
import Paper20.QSeries

namespace Paper20.ContentQ36Bridge
open Polynomial Paper20.RContent36 Paper20.Cert.RContent36.Tree
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

lemma coeff_poly_all (l : List ℚ) (i : ℕ) : (Uniform36.poly l).coeff i = l.getD i 0 := by
  rw [Uniform36.coeff_poly]
  split_ifs with h
  · rfl
  · rw [List.getD_eq_default _ _ (by omega)]

lemma getD_cast_int (l : List ℤ) (i : ℕ) :
    (l.map (fun z : ℤ => (z:ℚ))).getD i 0 = ((l.getD i 0:ℤ):ℚ) := by
  simpa only [Int.cast_zero] using
    (List.getD_map (l:=l) (d:=(0:ℤ)) (n:=i) (fun z : ℤ => (z:ℚ)))

lemma scalar_ne (h : ℕ) :
    (FastQ36.denominator h:ℚ)*((36:ℕ).factorial:ℚ) ≠ 0 := by
  exact mul_ne_zero (by exact_mod_cast (Nat.ne_of_gt (FastQ36.denominator_pos h)))
    (by positivity)

lemma finite_identification (h : ℕ) (hh : h ≤ 22) (l : List ℤ) (hl : l.length ≤ 23)
    (hc : ∀ i, i < 23 →
      (FastQ36.denominator h:ℚ)*((36:ℕ).factorial:ℚ)*cget (Qcoeff 36 h) i =
        (FastQ36.denominator h:ℚ)*((36:ℕ).factorial:ℚ)*
          ((1:ℚ)/Uniform36.Dqval)*((l.getD i 0:ℤ):ℚ)) :
    listPolynomial (Qcoeff 36 h) =
      C ((1:ℚ)/Uniform36.Dqval)*Uniform36.poly (l.map (fun z : ℤ => (z:ℚ))) := by
  ext i
  rw [coeff_listPolynomial,coeff_C_mul,coeff_poly_all,getD_cast_int]
  by_cases hi : i < 23
  · apply mul_left_cancel₀ (scalar_ne h)
    simpa only [mul_assoc] using hc i hi
  · rw [Qcoeff_degree 36 h i (by omega),List.getD_eq_default _ _ (by omega)]
    simp

/-- The verified content aggregates determine the same Q20 as the
uniform-family sign certificate. The only premise is the actual finite
partition-tree equality, which is supplied by the checked tree. -/
theorem Q20_of_root (hs : Correct root rootState) :
    listPolynomial (Qcoeff 36 20) = Uniform36.Q20 := by
  unfold Uniform36.Q20 Uniform36.AQ
  apply finite_identification 20 (by decide) Uniform36.AList (by decide)
  intro i hi
  calc
    _ = ((evaluateFastVector rootState 20).getD i 0:ℚ) :=
      (evaluateFastVector_scaled rootState hs root_keys_bound 20 i (by decide)).symm
    _ = (Cert.ContentQ36Rows.numerator20.getD i 0:ℚ) := by
      rw [Cert.ContentQ36Rows.evaluated20_getD i hi]
    _ = _ := Cert.ContentQ36Rows.scaled20_getD i hi

theorem Q21_of_root (hs : Correct root rootState) :
    listPolynomial (Qcoeff 36 21) = Uniform36.Q21 := by
  unfold Uniform36.Q21 Uniform36.BQ
  apply finite_identification 21 (by decide) Uniform36.BList (by decide)
  intro i hi
  calc
    _ = ((evaluateFastVector rootState 21).getD i 0:ℚ) :=
      (evaluateFastVector_scaled rootState hs root_keys_bound 21 i (by decide)).symm
    _ = (Cert.ContentQ36Rows.numerator21.getD i 0:ℚ) := by
      rw [Cert.ContentQ36Rows.evaluated21_getD i hi]
    _ = _ := Cert.ContentQ36Rows.scaled21_getD i hi

theorem Q22_of_root (hs : Correct root rootState) :
    listPolynomial (Qcoeff 36 22) = Uniform36.Q22 := by
  unfold Uniform36.Q22 Uniform36.CQ
  apply finite_identification 22 (by decide) Uniform36.CList (by decide)
  intro i hi
  calc
    _ = ((evaluateFastVector rootState 22).getD i 0:ℚ) :=
      (evaluateFastVector_scaled rootState hs root_keys_bound 22 i (by decide)).symm
    _ = (Cert.ContentQ36Rows.numerator22.getD i 0:ℚ) := by
      rw [Cert.ContentQ36Rows.evaluated22_getD i hi]
    _ = _ := Cert.ContentQ36Rows.scaled22_getD i hi

/-- The strict infinite-family inequality for the very same constructed
Q polynomials. The only input is the complete finite partition aggregate;
the transfer from these polynomials to Hilbert BPS coefficients is separate. -/
theorem constructed_Q_inequality (hs : Correct root rootState) (k : ℕ) (hk : 10 ≤ k) :
    peval (Qcoeff 36 21) ((k:ℚ)*(k+1))^2 <
      peval (Qcoeff 36 20) ((k:ℚ)*(k+1))*peval (Qcoeff 36 22) ((k:ℚ)*(k+1)) := by
  rw [← eval_listPolynomial,← eval_listPolynomial,← eval_listPolynomial,
    Q21_of_root hs,Q20_of_root hs,Q22_of_root hs]
  exact Uniform36.thm12_Q k hk

/-- The actual normalized partition series has the strict coefficient
inequality for all k>=10, using the proved Q-to-series equality. -/
theorem normalized_series_inequality (hs : Correct root rootState) (k : ℕ) (hk : 10 ≤ k) :
    (PowerSeries.coeff 21 (normalizedPartitionSeries 36 k))^2 <
      PowerSeries.coeff 20 (normalizedPartitionSeries 36 k)*
        PowerSeries.coeff 22 (normalizedPartitionSeries 36 k) := by
  rw [← Qcoeff_eq_normalizedPartitionSeries,← Qcoeff_eq_normalizedPartitionSeries,
    ← Qcoeff_eq_normalizedPartitionSeries]
  exact constructed_Q_inequality hs k hk

end
end Paper20.ContentQ36Bridge
