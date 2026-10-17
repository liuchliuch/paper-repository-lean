import Paper20.QuantumNormalization
import Paper20.Certs.Dimension36

namespace Paper20
open Polynomial
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
variable {K : Type*} [Field K] [CharZero K]

lemma squareBase (s : K) (m : ℕ) :
    (1+(s^2-4)/4)⁻¹^m=(2:K)^(2*m)/s^(2*m) := by
  have hb : 1+(s^2-4)/4=s^2/(2:K)^2 := by field_simp; ring
  rw [hb,inv_div,div_pow,← pow_mul,← pow_mul]

lemma parityNormalization (s : K) (hs : s ≠ 0) (e : ℕ) :
    (if e%2=0 then (2:K) else s)/(2*s^e) =
      (1+(s^2-4)/4)⁻¹^(e/2)/(2:K)^e := by
  rw [squareBase]
  by_cases he : e%2=0
  · rw [if_pos he]
    have hn : e=2*(e/2) := by omega
    conv_lhs => rw [hn]
    conv_rhs => arg 2; rw [hn]
    field_simp
  · rw [if_neg he]
    have hn : e=2*(e/2)+1 := by omega
    conv_lhs => rw [hn]
    conv_rhs => arg 2; rw [hn]
    rw [pow_succ,pow_succ]
    field_simp

lemma normalization_scalars (f F C B A D : K) (e : ℕ) (hF : F ≠ 0)
    (hprod : f*C*(2:K)^e=F) :
    f*A*(B/(2:K)^e)/D = (f^2/F)*A*(B*C/D) := by
  by_cases hD : D=0
  · simp [hD]
  · field_simp
    rw [← hprod]
    ring

/-- Exact normalization of one conjugate-paired genuine quantum partition
term, assuming only the hook-length dimension identity for that partition. -/
theorem pairedTerm_normalized (p : Part r)
    (hdim : dimOf r p.parts*(hooksOf p.parts).prod=r.factorial)
    (k : ℕ) (v : K) (hv : v ≠ 0) (hz : v-v⁻¹ ≠ 0) (hs : v+v⁻¹ ≠ 0) :
    (dimOf r p.parts:K)*
      (v^((2*k+1)*(contentOf p.parts).natAbs)+
        (v⁻¹)^((2*k+1)*(contentOf p.parts).natAbs))/
      (2*quantumDenominator p.parts v) =
        ((dimOf r p.parts:K)^2/(r.factorial:K))*
          aeval ((v-v⁻¹)^2) (Phi.contentNumerator (contentOf p.parts).natAbs k)*
            rationalR (hooksOf p.parts) (partsEvenHooks p.parts) ((v-v⁻¹)^2) := by
  have hhooks := hooksOf_positive_of_mem_partitionsOf p.mem_partitionsOf
  have hq := contentNumerator_quantum (contentOf p.parts).natAbs k v hv
  have hp : partsEvenHooks p.parts%2=(contentOf p.parts).natAbs%2 := by
    have he := p.hook_content_parity
    have hc := Phi.content_parity (contentOf p.parts)
    omega
  have hw : (v-v⁻¹)^2=(v+v⁻¹)^2-4 := by field_simp; ring
  have hc := Dconst_product (hooksOf p.parts) hhooks
  have hck := congrArg (algebraMap ℚ K) hc
  have hdimk := congrArg (fun n : ℕ => (n:K)) hdim
  have hprod : (dimOf r p.parts:K)*algebraMap ℚ K ((hooksOf p.parts).map Dconst).prod*
      (2:K)^(partsEvenHooks p.parts)=(r.factorial:K) := by
    have ht : algebraMap ℚ K ((hooksOf p.parts).map Dconst).prod*
        (2:K)^(partsEvenHooks p.parts)=((hooksOf p.parts).prod:K) := by
      simpa only [map_mul,map_pow,map_ofNat,map_natCast,partsEvenHooks_eq_evenHooksOf,evenHooksOf] using hck
    rw [mul_assoc,ht]
    simpa only [Nat.cast_mul] using hdimk
  rw [← hq,quantumDenominator_Dpoly p.parts hhooks v hv hz,← hp]
  rw [rationalR_as_product,hw]
  calc
    _ = (dimOf r p.parts:K)*
        aeval ((v+v⁻¹)^2-4) (Phi.contentNumerator (contentOf p.parts).natAbs k)*
        ((if partsEvenHooks p.parts%2=0 then (2:K) else v+v⁻¹)/
          (2*(v+v⁻¹)^(partsEvenHooks p.parts)))/
        ((hooksOf p.parts).map (fun a =>
          aeval ((v+v⁻¹)^2-4) (listPolynomial (Dpoly a)))).prod := by ring
    _ = _ := by
      rw [parityNormalization (v+v⁻¹) hs]
      exact normalization_scalars _ _ _ _ _ _ _ (by exact_mod_cast Nat.factorial_ne_zero r) hprod

/-- For r=36 the hook-length premise is discharged by the complete
kernel-checked partition enumeration, not supplied as an extra hypothesis. -/
theorem quantumPartitionTrace36_normalized (k : ℕ) (v : K)
    (hv : v ≠ 0) (hz : v-v⁻¹ ≠ 0) (hs : v+v⁻¹ ≠ 0) :
    quantumPartitionTrace 36 k v =
      ∑ p : Part 36, ((dimOf 36 p.parts:K)^2/((36:ℕ).factorial:K))*
        aeval ((v-v⁻¹)^2) (Phi.contentNumerator (contentOf p.parts).natAbs k)*
          rationalR (hooksOf p.parts) (partsEvenHooks p.parts) ((v-v⁻¹)^2) := by
  rw [quantumPartitionTrace_averaged]
  apply Finset.sum_congr rfl
  intro p hp
  exact pairedTerm_normalized p
    (Cert.Dimension36.dimension_times_hooks p.parts p.mem_partitionsOf) k v hv hz hs

end
end Paper20
