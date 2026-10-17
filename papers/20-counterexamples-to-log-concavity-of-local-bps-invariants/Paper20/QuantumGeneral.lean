import Paper20.HookIntegrality
import Paper20.HilbertSeriesFieldEvaluation

namespace Paper20
open Polynomial
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
variable {K : Type*} [Field K] [CharZero K]

/-- The hook quotient in the common executable partition enumeration is
exact for every rank, derived from the integral determinant proof. -/
theorem dimension_times_hooks {r : ℕ} {ps : List ℕ} (hp : ps ∈ partitionsOf r) :
    dimOf r ps*(hooksOf ps).prod=r.factorial :=
  HookDeterminant.actual_dim_mul_hooks (Part.ofMem ps hp)

/-- Equation (21)'s exact normalization for every actual partition of
every rank. Hook integrality is proved, not an additional premise. -/
theorem quantumPartitionTrace_normalized (r k : ℕ) (v : K)
    (hv : v ≠ 0) (hz : v-v⁻¹ ≠ 0) (hs : v+v⁻¹ ≠ 0) :
    quantumPartitionTrace r k v =
      ∑ p : Part r, ((dimOf r p.parts:K)^2/(r.factorial:K))*
        aeval ((v-v⁻¹)^2) (Phi.contentNumerator (contentOf p.parts).natAbs k)*
          rationalR (hooksOf p.parts) (partsEvenHooks p.parts) ((v-v⁻¹)^2) := by
  rw [quantumPartitionTrace_averaged]
  apply Finset.sum_congr rfl
  intro p hp
  exact pairedTerm_normalized p (HookDeterminant.actual_dim_mul_hooks p) k v hv hz hs

theorem normalizedPartitionSeries_quantumTrace
    (φ : PowerSeries ℚ →ₐ[ℚ] K) (r k : ℕ) (v : K)
    (hv : v ≠ 0) (hz : v-v⁻¹ ≠ 0) (hs : v+v⁻¹ ≠ 0)
    (hX : φ PowerSeries.X=(v-v⁻¹)^2) :
    φ (normalizedPartitionSeries r k)=quantumPartitionTrace r k v := by
  rw [normalizedPartitionSeries_field_evaluation,hX,
    quantumPartitionTrace_normalized r k v hv hz hs]
  exact (Part.sum_over_partitions r _).symm

theorem normalized_series_quantum_trace (r k : ℕ) :
    QuantumSeriesCoordinates.coordinateMap (normalizedPartitionSeries r k)=
      quantumPartitionTrace r k QuantumSeriesCoordinates.v :=
  normalizedPartitionSeries_quantumTrace QuantumSeriesCoordinates.coordinateMap r k
    QuantumSeriesCoordinates.v QuantumSeriesCoordinates.v_ne_zero
    QuantumSeriesCoordinates.quantum_difference_ne_zero
    QuantumSeriesCoordinates.quantum_sum_ne_zero QuantumSeriesCoordinates.coordinateMap_X

/-- For every rank, the same Q-generating series agrees with the original
normalized Hilbert rational expression under the proved faithful explicit
coordinate. No BPS, trace-character, positivity or polynomiality premise is
inserted into this identity. -/
theorem normalizedPartitionSeries_rationalHilbert (r k : ℕ) :
    QuantumSeriesCoordinates.coordinateMap (normalizedPartitionSeries r k) =
      QuantumSeriesCoordinates.v^(-((2*deg r k:ℕ):ℤ))*
        (1-QuantumSeriesCoordinates.v^2)^r*
          rationalHilbertSeries r k (QuantumSeriesCoordinates.v^2) := by
  rw [normalized_series_quantum_trace]
  exact (rationalHilbertSeries_quantum r k QuantumSeriesCoordinates.v
    QuantumSeriesCoordinates.v_ne_zero QuantumSeriesCoordinates.quantum_difference_ne_zero).symm

end
end Paper20
