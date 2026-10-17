import Paper20.CanonicalTableauRepresentation
import Paper20.HilbertQuantum

namespace Paper20.ExternalNormalization
open Polynomial Paper20.YoungShapes Paper20.Seminormal
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

section Field
variable {K : Type*} [Field K] [CharZero K]

/-- The original type-A q-hook Schur element, in the convention
(G_i-q)(G_i+1)=0 and normalized canonical trace tau(G_w)=delta_(w,e).
This is a definition, not a postulate of the external character theorem. -/
def schurElement (q : K) (ps : List ℕ) : K :=
  q^(-((nuOf ps:ℕ):ℤ))*((hooksOf ps).map (fun h => (1-q^h)/(1-q))).prod

lemma hookQuotientProduct (q : K) (hs : List ℕ) :
    (hs.map (fun h => (1-q^h)/(1-q))).prod=
      (hs.map (fun h => 1-q^h)).prod/(1-q)^hs.length := by
  induction hs with
  | nil => simp
  | cons h hs ih =>
    simp only [List.map_cons,List.prod_cons,List.length_cons,ih]
    rw [div_mul_div_comm,pow_succ,mul_comm (1-q) ((1-q)^hs.length)]

/-- The exact normalization from the original q-hook Schur element to
v^content times the already constructed quantum-hook denominator. This is
proved from the actual hook sum and actual content identities, not assumed
as part of the external character input. -/
theorem schurElement_quantum {r : ℕ} (p : Part r) (v : K)
    (hv : v≠0) (hz : v-v⁻¹≠0) :
    schurElement (v^2) p.parts=v^(contentOf p.parts)*quantumDenominator p.parts v := by
  rw [schurElement,hookQuotientProduct,quantumHookProduct _ v hv hz,
    hooksOf_length_of_mem_partitionsOf p.mem_partitionsOf,p.hook_sum,
    p.contentOf_eq_nu_difference,zpow_sub₀ hv]
  unfold quantumDenominator
  have hb : 1-v^2=(-1:K)*v*(v-v⁻¹) := by field_simp <;> ring
  generalize hZ : v-v⁻¹=Z at hz ⊢
  rw [hZ] at hb
  rw [hb]
  simp only [zpow_neg,zpow_natCast,pow_add,mul_pow,pow_mul]
  field_simp
  simp only [← pow_mul, Nat.mul_comm]

end Field
end
end Paper20.ExternalNormalization
