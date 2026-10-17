import Paper20.QuantumNormalization
import Paper20.QSeries
import Paper20.QuantumTermNormalization

namespace Paper20
open Polynomial
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
variable {K : Type*} [Field K] [CharZero K]

lemma seriesHom_C (φ : PowerSeries ℚ →ₐ[ℚ] K) (a : ℚ) :
    φ (PowerSeries.C a)=algebraMap ℚ K a := φ.commutes a

/-- Every algebra homomorphism preserves the inverse of an actual power
series unit. No analytic evaluation or convergence assumption is used. -/
lemma seriesHom_inv (φ : PowerSeries ℚ →ₐ[ℚ] K) (F : PowerSeries ℚ)
    (hF : PowerSeries.constantCoeff F ≠ 0) : φ F⁻¹=(φ F)⁻¹ := by
  have hm := congrArg φ (PowerSeries.mul_inv_cancel F hF)
  simp only [map_mul,map_one] at hm
  have hn : φ F ≠ 0 := by
    intro h
    rw [h,zero_mul] at hm
    exact zero_ne_one hm
  apply (mul_eq_one_iff_eq_inv₀ hn).1
  simpa only [mul_comm] using hm

lemma seriesHom_polynomial (φ : PowerSeries ℚ →ₐ[ℚ] K) (p : ℚ[X]) :
    φ (p : PowerSeries ℚ)=aeval (φ PowerSeries.X) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.coe_add,map_add,hp,hq]
  | monomial n a =>
    simp only [← C_mul_X_pow_eq_monomial,Polynomial.coe_mul,Polynomial.coe_C,
      Polynomial.coe_pow,Polynomial.coe_X,map_mul,map_pow,seriesHom_C,
      aeval_C,aeval_X]

lemma seriesHom_affineBase (φ : PowerSeries ℚ →ₐ[ℚ] K) :
    φ LogSeries.affineBase=1+φ PowerSeries.X/4 := by
  rw [LogSeries.affineBase,map_add,map_one,map_mul,seriesHom_C]
  norm_num
  ring

/-- The actual equation (18) power-series product maps to precisely its
rational D-product, under any field-valued homomorphism. -/
theorem Rproduct_field_evaluation (φ : PowerSeries ℚ →ₐ[ℚ] K)
    (hs : List ℕ) (e : ℕ) (hh : ∀ a ∈ hs, 0 < a) :
    φ (LogSeries.Rproduct hs e)=rationalR hs e (φ PowerSeries.X) := by
  rw [LogSeries.Rproduct,map_mul,map_pow,
    seriesHom_inv φ LogSeries.affineBase (by simp),seriesHom_affineBase]
  unfold rationalR
  congr 1
  rw [map_list_prod,List.map_map,List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro a ha
  dsimp only [Function.comp_def]
  rw [LogSeries.normalizedFactor,map_mul,seriesHom_C,
    seriesHom_inv φ (LogSeries.polynomialSeries (Dpoly a))
      (by
        rw [LogSeries.constant_polynomialSeries]
        exact Dconst_ne_zero a (hh a ha))]
  rw [LogSeries.polynomialSeries,seriesHom_polynomial]
  simp only [Dconst,cget,div_eq_mul_inv]

/-- The normalized series whose coefficients are the actual Q evaluations
has exactly the rational normalized partition expression in every field. -/
theorem normalizedPartitionSeries_field_evaluation (φ : PowerSeries ℚ →ₐ[ℚ] K)
    (r k : ℕ) :
    φ (normalizedPartitionSeries r k) =
      ((partitionsOf r).map (fun ps =>
        ((dimOf r ps:K)^2/(r.factorial:K))*
          aeval (φ PowerSeries.X) (Phi.contentNumerator (contentOf ps).natAbs k)*
            rationalR (hooksOf ps) (partsEvenHooks ps) (φ PowerSeries.X))).sum := by
  rw [normalizedPartitionSeries,map_mul,seriesHom_C,map_list_sum,List.map_map]
  have hr : algebraMap ℚ K (1/(r.factorial:ℚ))=1/(r.factorial:K) := by simp
  rw [hr]
  rw [← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ps hp
  dsimp only [Function.comp_def]
  rw [map_mul,map_mul,seriesHom_C,seriesHom_polynomial,
    Rproduct_field_evaluation φ _ _ (hooksOf_positive_of_mem_partitionsOf hp)]
  simp only [map_pow,map_natCast,Nat.cast_pow]
  ring

/-- Equation (21) over the actual complete r=36 partition set. The
field parameter records the substitution w=(v-v^-1)^2 explicitly. -/
theorem normalizedPartitionSeries36_quantumTrace
    (φ : PowerSeries ℚ →ₐ[ℚ] K) (k : ℕ) (v : K)
    (hv : v ≠ 0) (hz : v-v⁻¹ ≠ 0) (hs : v+v⁻¹ ≠ 0)
    (hX : φ PowerSeries.X=(v-v⁻¹)^2) :
    φ (normalizedPartitionSeries 36 k)=quantumPartitionTrace 36 k v := by
  rw [normalizedPartitionSeries_field_evaluation,hX,
    quantumPartitionTrace36_normalized k v hv hz hs]
  exact (Part.sum_over_partitions 36 _).symm

end
end Paper20
