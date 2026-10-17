import Paper20.DQuantum
import Paper20.PhiEvaluation
import Paper20.PartitionAveraging
import Paper20.HookParity

namespace Paper20
open Polynomial
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
variable {K : Type*} [Field K] [CharZero K]

/-- The actual normalized content numerator has precisely the even/odd
quantum-power normalization used when pairing conjugate partitions. -/
theorem contentNumerator_quantum (a k : ℕ) (v : K) (hv : v ≠ 0) :
    (if a%2=0 then (2:K) else v+v⁻¹)*
      aeval ((v-v⁻¹)^2) (Phi.contentNumerator a k) =
        v^((2*k+1)*a)+(v⁻¹)^((2*k+1)*a) := by
  unfold Phi.contentNumerator
  split_ifs with ha
  · have he : a=2*(a/2) := by omega
    have hn : (2*k+1)*a=2*((2*k+1)*(a/2)) := by nlinarith [he]
    rw [hn]
    exact Phi.even_quantum _ v hv
  · have he : a=2*(a/2)+1 := by omega
    have hn : (2*k+1)*a=2*((2*k+1)*(a/2)+k)+1 := by nlinarith [he]
    rw [hn]
    exact Phi.odd_quantum _ v hv

/-- The genuine quantum integer equals the same constructed D polynomial,
with the prescribed even-hook factor. -/
theorem quantumInteger_Dpoly (a : ℕ) (ha : 0 < a) (v : K)
    (hv : v ≠ 0) (hz : v-v⁻¹ ≠ 0) :
    quantumInteger a v =
      (if a%2=0 then v+v⁻¹ else 1)*aeval ((v-v⁻¹)^2) (listPolynomial (Dpoly a)) := by
  unfold quantumInteger
  apply (div_eq_iff hz).2
  have he := Dpoly_quantum a ha v hv
  simpa only [mul_assoc,mul_left_comm,mul_comm] using he.symm

lemma evenHookFactors (hs : List ℕ) (s : K) :
    (hs.map (fun a => if a%2=0 then s else 1)).prod =
      s^(hs.countP (fun a => a%2==0)) := by
  induction hs with
  | nil => simp
  | cons a hs ih =>
    by_cases ha : a%2=0
    · simp [ha,ih,pow_succ,mul_comm]
    · simp [ha,ih]

/-- The full denominator is the actual hook product of D polynomials,
with one s factor for each even hook. -/
theorem quantumDenominator_Dpoly (ps : List ℕ) (hh : ∀ a ∈ hooksOf ps, 0 < a)
    (v : K) (hv : v ≠ 0) (hz : v-v⁻¹ ≠ 0) :
    quantumDenominator ps v = (v+v⁻¹)^(partsEvenHooks ps)*
      ((hooksOf ps).map (fun a => aeval ((v-v⁻¹)^2) (listPolynomial (Dpoly a)))).prod := by
  unfold quantumDenominator
  have he : (hooksOf ps).map (fun a => quantumInteger a v) =
      (hooksOf ps).map (fun a => (if a%2=0 then v+v⁻¹ else 1)*
        aeval ((v-v⁻¹)^2) (listPolynomial (Dpoly a))) := by
    apply List.map_congr_left
    intro a ha
    exact quantumInteger_Dpoly a (hh a ha) v hv hz
  rw [he,List.prod_map_mul,evenHookFactors]
  rfl

/-- The hook-dependent powers of two in (18) are exact for the original
D_a constant coefficients. -/
theorem Dconst_normalization (a : ℕ) (ha : 0 < a) :
    Dconst a*(if a%2=0 then (2:ℚ) else 1)=(a:ℚ) := by
  unfold Dconst
  rw [cget_Dpoly_zero a ha]
  by_cases he : a%2=0
  · have ho : a%2 ≠ 1 := by omega
    simp [he,ho]
  · have ho : a%2=1 := by omega
    simp [he,ho]

theorem Dconst_product (hs : List ℕ) (hh : ∀ a ∈ hs, 0 < a) :
    (hs.map Dconst).prod*(2:ℚ)^(hs.countP (fun a => a%2==0)) = (hs.prod:ℚ) := by
  rw [← evenHookFactors hs (2:ℚ),← List.prod_map_mul]
  rw [Nat.cast_list_prod]
  apply congrArg List.prod
  apply List.map_congr_left
  intro a ha
  exact Dconst_normalization a (hh a ha)

/-- Rational evaluation of precisely the product in equation (18). -/
def rationalR (hs : List ℕ) (e : ℕ) (w : K) : K :=
  (1+w/4)⁻¹^(e/2)*
    (hs.map (fun a => (algebraMap ℚ K (Dconst a))/
      aeval w (listPolynomial (Dpoly a)))).prod

lemma rationalR_as_product (hs : List ℕ) (e : ℕ) (w : K) :
    rationalR hs e w = (1+w/4)⁻¹^(e/2)*
      algebraMap ℚ K (hs.map Dconst).prod/
        (hs.map (fun a => aeval w (listPolynomial (Dpoly a)))).prod := by
  have he : (hs.map (fun a => (algebraMap ℚ K (Dconst a))/
      aeval w (listPolynomial (Dpoly a)))).prod =
        algebraMap ℚ K (hs.map Dconst).prod/
          (hs.map (fun a => aeval w (listPolynomial (Dpoly a)))).prod := by
    induction hs with
    | nil => simp
    | cons a hs ih => simp only [List.map_cons,List.prod_cons,map_mul,ih]; ring
  rw [rationalR,he]
  ring

end
end Paper20
