import Paper20.HilbertAtZero
import Paper20.HeckeSpecializationTrace

namespace Paper20.HilbertHeckeBridge
open Polynomial Finset Paper20.HeckeTraceAlgebra Paper20.HeckeWalkExpansion
open Paper20.BraidWalk Paper20.HilbertAtZero Paper20.HilbertSeriesProof
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

lemma bpsPolynomial_walk (r k : ℕ) :
    bpsPolynomial (deg r k) (fun h => (walkCount r k h:ℤ))=walkBPSPolynomial r k := by
  simp only [bpsPolynomial,walkBPSPolynomial,C_mul_X_pow_eq_monomial]

/-- The remaining character formula is stated on the actual canonical
trace and actual quantum partition expression. No coefficient, positivity
or polynomial-evaluation conclusion is assumed in this bridge. -/
def CharacterFormulaAt (r k : ℕ) (t : QuantumSeriesCoordinates.SeriesField) : Prop :=
  quantumPartitionTrace r k t=
    (canonicalTrace r (omega r^(k+1))).eval₂
      (Int.castRingHom QuantumSeriesCoordinates.SeriesField) (t-t⁻¹)

lemma character_even_polynomial (r k : ℕ) (hr : 1 ≤ r)
    (t : QuantumSeriesCoordinates.SeriesField) (hc : CharacterFormulaAt r k t) :
    quantumPartitionTrace r k t=
      (walkBPSPolynomial r k).eval₂ (Int.castRingHom QuantumSeriesCoordinates.SeriesField)
        ((t-t⁻¹)^2) := by
  rw [CharacterFormulaAt,canonicalTrace_omega_even_variable r k hr,
    eval₂_comp,eval₂_pow,eval₂_X] at hc
  exact hc

/-- The original Hilbert/BPS expansion follows from the genuine canonical
trace character formula, through q=t² at the original Hilbert origin. -/
theorem original_expansion_of_character (r k : ℕ) (hr : 1 ≤ r)
    (hc : CharacterFormulaAt r k HilbertAtZero.v) :
    (1-PowerSeries.X)^r*partitionHilbertSeries r k=
      rationalBPS (deg r k) (fun h => (walkCount r k h:ℤ)) := by
  apply rational_expansion_of_quantum
  rw [bpsPolynomial_walk]
  exact character_even_polynomial r k hr _ hc

/-- Equality reaches the actual public Hilbert-array implementation; it
is derived from the original expansion, rather than an identification
postulated directly on BPS coefficients. -/
theorem bpsCoeff_eq_walk_of_character (r k : ℕ) (hr : 1 ≤ r)
    (hc : CharacterFormulaAt r k HilbertAtZero.v) (h : ℕ) (hh : h ≤ deg r k) :
    bpsCoeff r k h=walkCount r k h := by
  have he := bpsCoeff_from_rational_expansion r k (fun h => (walkCount r k h:ℤ))
    (original_expansion_of_character r k hr hc) h hh
  simpa only [Int.toNat_natCast] using he

theorem bps_bounds_of_character (r k h : ℕ) (hr : 1 ≤ r)
    (hc : CharacterFormulaAt r k HilbertAtZero.v) (hh : h ≤ deg r k) :
    1 ≤ bpsCoeff r k h ∧ bpsCoeff r k h ≤ Nat.choose (2*deg r k) (2*h) := by
  rw [bpsCoeff_eq_walk_of_character r k hr hc h hh]
  exact walk_bounds r k h hh

theorem bps_endpoints_of_character (r k : ℕ) (hr : 1 ≤ r)
    (hc : CharacterFormulaAt r k HilbertAtZero.v) :
    bpsCoeff r k 0=1 ∧ bpsCoeff r k (deg r k)=1 := by
  rw [bpsCoeff_eq_walk_of_character r k hr hc 0 (Nat.zero_le _),
    bpsCoeff_eq_walk_of_character r k hr hc (deg r k) le_rfl]
  exact walk_endpoints r k

/-- At w=0 the proved faithful coordinate converts the same character
formula into equality of the complete actual Q-generating series with the
actual finite walk polynomial. -/
theorem normalized_series_of_character (r k : ℕ) (hr : 1 ≤ r)
    (hc : CharacterFormulaAt r k QuantumSeriesCoordinates.v) :
    normalizedPartitionSeries r k=
      ((walkBPSPolynomial r k).map (Int.castRingHom ℚ):PowerSeries ℚ) := by
  apply QuantumSeriesCoordinates.coordinateMap_injective
  rw [normalized_series_quantum_trace,
    seriesHom_polynomial,QuantumSeriesCoordinates.coordinateMap_X]
  rw [aeval_def,Polynomial.eval₂_map]
  have hm : (algebraMap ℚ QuantumSeriesCoordinates.SeriesField).comp (Int.castRingHom ℚ)=
      Int.castRingHom QuantumSeriesCoordinates.SeriesField := by ext; simp
  rw [hm]
  exact character_even_polynomial r k hr _ hc

/-- The very same constructed Q evaluates to the very same concrete walk
count, conditional only on the canonical trace character formula. -/
theorem Q_evaluation_of_character (r k h : ℕ) (hr : 1 ≤ r)
    (hc : CharacterFormulaAt r k QuantumSeriesCoordinates.v) (hh : h ≤ deg r k) :
    peval (Qcoeff r h) ((k:ℚ)*(k+1))=(walkCount r k h:ℚ) := by
  rw [Qcoeff_eq_normalizedPartitionSeries,normalized_series_of_character r k hr hc,
    Polynomial.coeff_coe,Polynomial.coeff_map,walkBPSPolynomial_coeff,if_pos hh]
  rfl

/-- Both original formal coordinates now have explicit proved bridges;
the same character formula in those coordinates supplies the remaining
semantic input for the actual same-Q BPS evaluation theorem. -/
theorem bps_Q_evaluation_of_character (r k h : ℕ) (hr : 1 ≤ r)
    (hc0 : CharacterFormulaAt r k HilbertAtZero.v)
    (hc1 : CharacterFormulaAt r k QuantumSeriesCoordinates.v) (hh : h ≤ deg r k) :
    (bpsCoeff r k h:ℚ)=peval (Qcoeff r h) ((k:ℚ)*(k+1)) := by
  rw [bpsCoeff_eq_walk_of_character r k hr hc0 h hh,
    Q_evaluation_of_character r k h hr hc1 hh]

end
end Paper20.HilbertHeckeBridge
