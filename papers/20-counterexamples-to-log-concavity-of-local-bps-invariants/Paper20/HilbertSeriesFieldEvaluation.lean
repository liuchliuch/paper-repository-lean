import Paper20.HilbertQuantum
import Paper20.QuantumSeriesCoordinates

namespace Paper20
open Polynomial
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
variable {K : Type*} [Field K] [CharZero K]

lemma hookInverse_field_evaluation (φ : PowerSeries ℚ →ₐ[ℚ] K)
    (a : ℕ) (ha : 0 < a) :
    φ (HilbertSeriesProof.hookInverse a)=(1-(φ PowerSeries.X)^a)⁻¹ := by
  rw [HilbertSeriesProof.hookInverse,seriesHom_inv φ _
    (by rw [HilbertSeriesProof.hook_constant a ha]; norm_num),map_sub,map_one,map_pow]

lemma hookProduct_field_evaluation (φ : PowerSeries ℚ →ₐ[ℚ] K)
    (hooks : List ℕ) (hh : ∀ a ∈ hooks, 0 < a) :
    φ (hooks.map HilbertSeriesProof.hookInverse).prod=
      ((hooks.map (fun a => 1-(φ PowerSeries.X)^a)).prod)⁻¹ := by
  induction hooks with
  | nil => simp
  | cons a hooks ih =>
    rw [List.map_cons,List.prod_cons,map_mul,
      hookInverse_field_evaluation φ a (hh a (by simp)),
      ih (fun b hb => hh b (by simp [hb])),List.map_cons,List.prod_cons,mul_inv_rev]
    ring

/-- Field interpretation of the very same Hilbert power-series summand,
with the original nonnegative shift and every actual hook denominator. -/
theorem HilbertSeriesProof.partitionSummand_field_evaluation
    (φ : PowerSeries ℚ →ₐ[ℚ] K) {r : ℕ} {ps : List ℕ}
    (hp : ps ∈ partitionsOf r) (k : ℕ) :
    φ (partitionSummand r k ps)=rationalHilbertTerm r k (φ PowerSeries.X) ps := by
  rw [partitionSummand,map_mul,seriesHom_C,map_mul,map_pow,
    hookProduct_field_evaluation φ _ (hooksOf_positive_of_mem_partitionsOf hp)]
  simp only [map_natCast,rationalHilbertTerm,div_eq_mul_inv,mul_assoc]

/-- The full formal Hilbert series has exactly the original finite
rational-function expression. Together with hilbertArray_coeff, this
connects the actual program to the rational expression without input data. -/
theorem HilbertSeriesProof.partitionHilbertSeries_field_evaluation
    (φ : PowerSeries ℚ →ₐ[ℚ] K) (r k : ℕ) :
    φ (partitionHilbertSeries r k)=rationalHilbertSeries r k (φ PowerSeries.X) := by
  rw [partitionHilbertSeries,map_list_sum,List.map_map,rationalHilbertSeries]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ps hp
  exact partitionSummand_field_evaluation φ hp k

/-- The genuine normalized Q-generating series, in an explicit faithful
formal coordinate, equals the normalized original r=36 Hilbert rational
expression. The remaining polynomiality and Hecke character bridges are
separate obligations; neither is a premise asserting a BPS coefficient. -/
theorem normalizedPartitionSeries36_rationalHilbert (k : ℕ) :
    QuantumSeriesCoordinates.coordinateMap (normalizedPartitionSeries 36 k) =
      QuantumSeriesCoordinates.v^(-((2*deg 36 k:ℕ):ℤ))*
        (1-QuantumSeriesCoordinates.v^2)^36*
          rationalHilbertSeries 36 k (QuantumSeriesCoordinates.v^2) := by
  rw [QuantumSeriesCoordinates.normalized_series_quantum_trace]
  exact (rationalHilbertSeries_quantum 36 k QuantumSeriesCoordinates.v
    QuantumSeriesCoordinates.v_ne_zero QuantumSeriesCoordinates.quantum_difference_ne_zero).symm

end
end Paper20
