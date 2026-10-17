import Paper20.QuantumNormalization
import Paper20.HilbertSeriesSemantics
import Paper20.HookSum

namespace Paper20
open Polynomial
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
variable {K : Type*} [Field K] [CharZero K]

lemma quantumHookFactor (a : ℕ) (v : K) (hv : v ≠ 0) (hz : v-v⁻¹ ≠ 0) :
    1-(v^2)^a = -v^a*(v-v⁻¹)*quantumInteger a v := by
  have hi : v^a*(v⁻¹)^a=1 := by rw [← mul_pow,mul_inv_cancel₀ hv,one_pow]
  have hp : (v^2)^a=(v^a)^2 := by rw [← pow_mul,← pow_mul,Nat.mul_comm 2 a]
  unfold quantumInteger
  rw [hp]
  have he : -v^a*(v-v⁻¹)*((v^a-(v⁻¹)^a)/(v-v⁻¹)) =
      -v^a*(v^a-(v⁻¹)^a) := by
    calc
      _ = -v^a*(((v^a-(v⁻¹)^a)/(v-v⁻¹))*(v-v⁻¹)) := by ring
      _ = _ := by rw [div_mul_cancel₀ _ hz]
  rw [he]
  calc
    1-(v^a)^2 = v^a*(v⁻¹)^a-(v^a)^2 := by rw [hi]
    _ = _ := by ring

/-- Exact denominator conversion from q=v² to quantum integers. -/
theorem quantumHookProduct (hooks : List ℕ) (v : K) (hv : v ≠ 0) (hz : v-v⁻¹ ≠ 0) :
    (hooks.map (fun a => 1-(v^2)^a)).prod =
      (-1:K)^hooks.length*v^hooks.sum*(v-v⁻¹)^hooks.length*
        (hooks.map (fun a => quantumInteger a v)).prod := by
  induction hooks with
  | nil => simp
  | cons a hooks ih =>
    rw [List.map_cons,List.prod_cons,quantumHookFactor a v hv hz,ih]
    simp only [List.length_cons,List.sum_cons,pow_succ,pow_add,List.map_cons,List.prod_cons]
    ring

/-- Rational-function interpretation of the exact full Hilbert partition
formula (13), with its proved nonnegative shift. -/
def rationalHilbertTerm (r k : ℕ) (q : K) (ps : List ℕ) : K :=
  (dimOf r ps:K)*q^(shiftE ps k (deg r k)).toNat/
    ((hooksOf ps).map (fun a => 1-q^a)).prod

def rationalHilbertSeries (r k : ℕ) (q : K) : K :=
  ((partitionsOf r).map (rationalHilbertTerm r k q)).sum

lemma normalizeHilbertFactor (d E r s : ℕ) (F D v : K)
    (hv : v ≠ 0) (hz : v-v⁻¹ ≠ 0) :
    v^(-((2*d:ℕ):ℤ))*(1-v^2)^r*
      (F*(v^2)^E/((-1:K)^r*v^s*(v-v⁻¹)^r*D)) =
        F*(v^(-((2*d:ℕ):ℤ))*v^(2*E+r)/v^s)/D := by
  have hb : 1-v^2=(-1:K)*v*(v-v⁻¹) := by field_simp; ring
  generalize hZ : v-v⁻¹=Z at hz ⊢
  rw [hZ] at hb
  by_cases hD : D=0
  · simp [hD]
  · simp only [hb,mul_pow,pow_add,pow_mul,zpow_neg,zpow_natCast]
    field_simp

lemma Part.quantum_exponent (p : Part r) (k : ℕ) :
    -((2*deg r k:ℕ):ℤ)+((2*(shiftE p.parts k (deg r k)).toNat+r:ℕ):ℤ)-
      ((hooksOf p.parts).sum:ℤ) = ((2*k+1:ℕ):ℤ)*contentOf p.parts := by
  have hE := Int.toNat_of_nonneg (p.shiftE_nonnegative k)
  have hsum := congrArg (fun n : ℕ => (n:ℤ)) p.hook_sum
  dsimp only at hsum
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  rw [hE,hsum]
  unfold shiftE
  rw [p.contentOf_eq_nu_difference]
  push_cast
  ring

/-- The original rational Hilbert summand, after clearing its BPS
normalization, is exactly the genuine quantum partition term. -/
theorem rationalHilbertTerm_quantum (p : Part r) (k : ℕ) (v : K)
    (hv : v ≠ 0) (hz : v-v⁻¹ ≠ 0) :
    v^(-((2*deg r k:ℕ):ℤ))*(1-v^2)^r*rationalHilbertTerm r k (v^2) p.parts =
      quantumTerm r k v p := by
  rw [rationalHilbertTerm,quantumHookProduct _ v hv hz,
    hooksOf_length_of_mem_partitionsOf p.mem_partitionsOf,
    normalizeHilbertFactor _ _ _ _ _ _ v hv hz]
  unfold quantumTerm quantumDenominator
  apply congrArg (fun x : K => (dimOf r p.parts:K)*x /
    ((hooksOf p.parts).map (fun a => quantumInteger a v)).prod)
  have he := p.quantum_exponent k
  calc
    _ = v^(-((2*deg r k:ℕ):ℤ)+((2*(shiftE p.parts k (deg r k)).toNat+r:ℕ):ℤ)-
        ((hooksOf p.parts).sum:ℤ)) := by
      rw [zpow_sub₀ hv,zpow_add₀ hv]
      simp only [zpow_natCast]
    _ = _ := by rw [he]

/-- Formula (15), derived directly from the very same complete rational
partition formula (13), using the actual hook sum and content identity. -/
theorem rationalHilbertSeries_quantum (r k : ℕ) (v : K)
    (hv : v ≠ 0) (hz : v-v⁻¹ ≠ 0) :
    v^(-((2*deg r k:ℕ):ℤ))*(1-v^2)^r*rationalHilbertSeries r k (v^2) =
      quantumPartitionTrace r k v := by
  classical
  rw [rationalHilbertSeries,← Part.sum_over_partitions r (rationalHilbertTerm r k (v^2)),
    Finset.mul_sum,quantumPartitionTrace]
  apply Finset.sum_congr rfl
  intro p hp
  exact rationalHilbertTerm_quantum p k v hv hz

end
end Paper20
