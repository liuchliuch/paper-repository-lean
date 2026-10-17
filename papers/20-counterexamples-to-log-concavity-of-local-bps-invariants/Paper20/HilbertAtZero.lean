import Paper20.QuantumGeneral
import Paper20.RationalBPSExtraction

namespace Paper20.HilbertAtZero
open Polynomial Finset Paper20.QuantumSeriesCoordinates Paper20.HilbertSeriesProof
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

def squareHasSubst : PowerSeries.HasSubst (PowerSeries.X^2 : PowerSeries ℚ) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)

/-- The faithful original Hilbert coordinate q=t², expanded at q=0. -/
def qMap : PowerSeries ℚ →ₐ[ℚ] SeriesField :=
  embedding.comp (PowerSeries.substAlgHom (R:=ℚ) squareHasSubst)

theorem qMap_injective : Function.Injective qMap :=
  embedding_injective.comp (subst_injective _ squareHasSubst (pow_ne_zero 2 PowerSeries.X_ne_zero))

def v : SeriesField := embedding PowerSeries.X

lemma v_ne_zero : v ≠ 0 := by
  exact (map_ne_zero_iff embedding embedding_injective).2 PowerSeries.X_ne_zero

lemma qMap_X : qMap PowerSeries.X=v^2 := by
  rw [qMap,AlgHom.comp_apply,PowerSeries.substAlgHom_X,map_pow]
  rfl

lemma qMap_C (a : ℚ) : qMap (PowerSeries.C a)=algebraMap ℚ SeriesField a :=
  seriesHom_C qMap a

lemma hilbert_evaluation (r k : ℕ) :
    qMap (partitionHilbertSeries r k)=rationalHilbertSeries r k (v^2) := by
  rw [partitionHilbertSeries_field_evaluation,qMap_X]

/-- Integer coefficients of the same finite BPS polynomial. -/
def bpsPolynomial (d : ℕ) (n : ℕ → ℤ) : ℤ[X] :=
  ∑ h ∈ range (d+1), Polynomial.C (n h)*X^h

lemma bpsPolynomial_eval {K : Type*} [CommRing K] (d : ℕ) (n : ℕ → ℤ) (w : K) :
    (bpsPolynomial d n).eval₂ (Int.castRingHom K) w=
      ∑ h ∈ range (d+1), (n h:K)*w^h := by
  simp only [bpsPolynomial,eval₂_finset_sum,eval₂_mul,eval₂_C,eval₂_pow,eval₂_X]
  rfl

lemma bps_factor {K : Type*} [Field K] (d h : ℕ) (hh : h ≤ d) (t : K) (ht : t ≠ 0) :
    (t^2)^(d-h)*(1-t^2)^(2*h)=t^(2*d)*((t-t⁻¹)^2)^h := by
  have hb : 1-t^2=-t*(t-t⁻¹) := by field_simp; ring
  have hn : 2*(d-h)+2*h=2*d := by omega
  rw [hb,mul_pow,Even.neg_pow (even_two_mul h),← pow_mul,← pow_mul]
  rw [← mul_assoc,← pow_add,hn]

lemma qMap_rationalBPS (d : ℕ) (n : ℕ → ℤ) :
    qMap (rationalBPS d n)=v^(2*d)*
      (bpsPolynomial d n).eval₂ (Int.castRingHom SeriesField) ((v-v⁻¹)^2) := by
  rw [rationalBPS_expansion,map_sum,bpsPolynomial_eval,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  simp only [map_mul,map_pow,map_sub,map_one,qMap_X,qMap_C]
  rw [bps_factor d h (by have := mem_range.mp hh; omega) v v_ne_zero]
  simp only [map_intCast]
  ring

/-- An actual quantum partition identity with a finite integer polynomial
implies the ORIGINAL Hilbert BPS power-series expansion at q=0. The proof
uses an independent injective coordinate, not the w=0 Q-series expansion. -/
theorem rational_expansion_of_quantum (r k : ℕ) (n : ℕ → ℤ)
    (hquantum : quantumPartitionTrace r k v=
      (bpsPolynomial (deg r k) n).eval₂ (Int.castRingHom SeriesField) ((v-v⁻¹)^2)) :
    (1-PowerSeries.X)^r*partitionHilbertSeries r k=rationalBPS (deg r k) n := by
  apply qMap_injective
  rw [map_mul,map_pow,map_sub,map_one,qMap_X,hilbert_evaluation,qMap_rationalBPS]
  have hs : v^2 ≠ 1 := by
    intro ht
    have hp : embedding ((PowerSeries.X:PowerSeries ℚ)^2)=embedding 1 := by
      simpa only [map_pow,map_one,v] using ht
    have hc := congrArg PowerSeries.constantCoeff (embedding_injective hp)
    norm_num at hc
  have hd : v-v⁻¹ ≠ 0 := by
    intro hz
    apply hs
    have hm : v^2-1=0 := by
      calc
        _ = (v-v⁻¹)*v := by rw [sub_mul,inv_mul_cancel₀ v_ne_zero,pow_two]
        _ = 0 := by rw [hz,zero_mul]
    exact sub_eq_zero.mp hm
  have he := rationalHilbertSeries_quantum r k v v_ne_zero hd
  rw [hquantum,zpow_neg,zpow_natCast] at he
  have hn := pow_ne_zero (2*deg r k) v_ne_zero
  have hex : (v^(2*deg r k))⁻¹*((1-v^2)^r*rationalHilbertSeries r k (v^2))=
      (bpsPolynomial (deg r k) n).eval₂ (Int.castRingHom SeriesField) ((v-v⁻¹)^2) := by
    simpa only [mul_assoc] using he
  calc
    _ = v^(2*deg r k)*((v^(2*deg r k))⁻¹*
        ((1-v^2)^r*rationalHilbertSeries r k (v^2))) := by
      rw [← mul_assoc,mul_inv_cancel₀ hn,one_mul]
    _ = _ := by rw [hex]

/-- The genuine quantum-to-Hilbert bridge reaches the actual array
extraction without a BPS-coefficient assumption. -/
theorem bpsCoeff_of_quantum (r k : ℕ) (n : ℕ → ℤ)
    (hquantum : quantumPartitionTrace r k v=
      (bpsPolynomial (deg r k) n).eval₂ (Int.castRingHom SeriesField) ((v-v⁻¹)^2))
    (h : ℕ) (hh : h ≤ deg r k) : bpsCoeff r k h=(n h).toNat :=
  bpsCoeff_from_rational_expansion r k n (rational_expansion_of_quantum r k n hquantum) h hh

end
end Paper20.HilbertAtZero
