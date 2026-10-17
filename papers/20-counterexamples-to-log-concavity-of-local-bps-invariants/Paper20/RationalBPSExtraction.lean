import Paper20.HilbertSeriesSemantics
import Paper20.Elimination

namespace Paper20.HilbertSeriesProof
open Polynomial Finset Paper20.Semantics Paper20.ArraySemantics
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

lemma rational_coeff_one_sub_X_pow (b ℓ : ℕ) :
    PowerSeries.coeff ℓ ((1-PowerSeries.X)^b : PowerSeries ℚ)=
      (-1:ℚ)^ℓ*(Nat.choose b ℓ:ℚ) := by
  induction b generalizing ℓ with
  | zero =>
    cases ℓ with
    | zero => simp
    | succ ℓ => simp [PowerSeries.coeff_one]
  | succ b ih =>
    have he : ((1-PowerSeries.X)^(b+1) : PowerSeries ℚ)=
        (1-PowerSeries.X)^b-(1-PowerSeries.X)^b*PowerSeries.X := by ring
    rw [he,map_sub]
    cases ℓ with
    | zero => simp [ih]
    | succ ℓ =>
      rw [PowerSeries.coeff_succ_mul_X,ih,ih,Nat.choose_succ_succ]
      push_cast
      rw [pow_succ]
      ring

/-- The actual finite-difference array is the rational residual of the
full original Hilbert partition series at every retained coefficient. -/
theorem fArray_coeff (r k ℓ : ℕ) (hℓ : ℓ ≤ deg r k) :
    ((fArray r k).getD ℓ 0:ℚ)=
      PowerSeries.coeff ℓ ((1-PowerSeries.X)^r*partitionHilbertSeries r k) := by
  rw [fArray_correct r k ℓ hℓ,hilbertResidual,Int.cast_sum,
    PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := mem_range.mp hi
  rw [rational_coeff_one_sub_X_pow,← hilbertArray_coeff r k (ℓ-i) (by omega)]
  push_cast
  rfl

/-- Rational form of the original finite BPS right-hand side; it is the
coefficientwise image of the same integer expansion used by Appendix A. -/
def rationalBPS (d : ℕ) (n : ℕ → ℤ) : PowerSeries ℚ :=
  PowerSeries.map (Int.castRingHom ℚ) (bpsSeries d n)

lemma rationalBPS_expansion (d : ℕ) (n : ℕ → ℤ) :
    rationalBPS d n=∑ j ∈ range (d+1), PowerSeries.C (n j:ℚ)*
      (PowerSeries.X^(d-j)*(1-PowerSeries.X)^(2*j)) := by
  simp only [rationalBPS,bpsSeries,map_sum,map_mul,map_pow,PowerSeries.map_C,
    map_sub,map_one,PowerSeries.map_X]
  rfl

lemma rationalBPS_coeff (d ℓ : ℕ) (n : ℕ → ℤ) :
    PowerSeries.coeff ℓ (rationalBPS d n)=(expansionCoeff d n ℓ:ℚ) := by
  rw [rationalBPS,PowerSeries.coeff_map,coeff_bpsSeries]
  rfl

/-- A genuine original rational power-series BPS expansion determines
the exact integer output of the actual implementation, with no coefficient
identification or positivity premise. -/
theorem rational_expansion_to_program (r k : ℕ) (n : ℕ → ℤ)
    (hexp : (1-PowerSeries.X)^r*partitionHilbertSeries r k=rationalBPS (deg r k) n) :
    ∀ h, h ≤ deg r k → n h=(bpsFromF (fArray r k)).getD h 0 := by
  apply recurrence25_unique (F:=fun ℓ => (fArray r k).getD ℓ 0)
    (m:=fun h => (bpsFromF (fArray r k)).getD h 0) ?_
    (Elimination.bpsFromHilbert_recurrence r k)
  apply (recurrence25_iff_low _ _ _).2
  intro ℓ hℓ
  have he := congrArg (PowerSeries.coeff ℓ) hexp
  rw [← fArray_coeff r k ℓ hℓ,rationalBPS_coeff] at he
  exact_mod_cast he

theorem bpsCoeff_from_rational_expansion (r k : ℕ) (n : ℕ → ℤ)
    (hexp : (1-PowerSeries.X)^r*partitionHilbertSeries r k=rationalBPS (deg r k) n)
    (h : ℕ) (hh : h ≤ deg r k) : bpsCoeff r k h=(n h).toNat := by
  rw [Elimination.bpsCoeff_eq_toNat r k h hh,
    ← rational_expansion_to_program r k n hexp h hh]

end
end Paper20.HilbertSeriesProof
