import Paper20.HeckeParameterPolynomial

namespace Paper20.HeckeParameterPolynomial
open Polynomial Matrix Finset Paper20.HeckeTraceAlgebra Paper20.HeckeMatrices
open Paper20.HeckeSpecialization Paper20.HalfTwistMatrix
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

lemma pochhammer_top (m : ℕ) : (descPochhammer ℚ m).coeff m=1 := by
  have he := (monic_descPochhammer ℚ m).coeff_natDegree
  simpa only [descPochhammer_natDegree] using he

/-- The top coefficient of the actual exponent polynomial is determined
by the constant specialization of the first-order full-twist quotient. -/
theorem exponentPolynomial_top (r m : ℕ) :
    (exponentPolynomial r m).coeff m=
      (((incrementQuotient r^m) 1 1).coeff 0:ℚ)/(m.factorial:ℚ) := by
  rw [exponentPolynomial,finset_sum_coeff]
  simp only [coeff_C_mul]
  rw [Finset.sum_eq_single m]
  · rw [Nat.sub_self,pochhammer_top,mul_one]
  · intro j hj hjm
    have hj' : j < m := by have := mem_range.mp hj; omega
    have hc : (descPochhammer ℚ j).coeff m=0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [descPochhammer_natDegree]; exact hj')
    rw [hc,mul_zero]
  · intro hn
    exact False.elim (hn (mem_range.mpr (by omega)))

/-- The genuine infinitesimal full-twist matrix, using actual linear
coefficients of the original Hecke matrices. -/
def infinitesimalFullTwist (r : ℕ) : Matrix (State r) (State r) ℤ :=
  fun s t => (fullTwist r s t).coeff 1

lemma specialize_incrementQuotient (r : ℕ) :
    specialize r (incrementQuotient r)=infinitesimalFullTwist r := by
  classical
  apply Matrix.ext
  intro s t
  rw [specialize_apply,incrementQuotient,Polynomial.coeff_divX]
  change (fullTwist r s t-(1:Mat r) s t).coeff 1=(fullTwist r s t).coeff 1
  rw [coeff_sub]
  by_cases hst : s=t <;> simp [Matrix.one_apply,hst,Polynomial.coeff_one]

/-- An exact matrix-moment leading coefficient for all ranks and all
orders. Identifying this actual infinitesimal matrix with the transposition
sum is a separate concrete combinatorial obligation. -/
theorem exponentPolynomial_top_matrix (r m : ℕ) :
    (exponentPolynomial r m).coeff m=
      (((infinitesimalFullTwist r^m) 1 1):ℚ)/(m.factorial:ℚ) := by
  rw [exponentPolynomial_top]
  have he := congrFun (congrFun (map_pow (specialize r) (incrementQuotient r) m) 1) 1
  rw [specialize_apply,specialize_incrementQuotient] at he
  rw [he]

/-- The actual trace normalization gives the polynomial's entire value
at n=1, rather than merely its constant-term degree bound. -/
theorem exponentPolynomial_eval_one (r m : ℕ) (hr : 1 ≤ r) :
    (exponentPolynomial r m).eval 1=if m=0 then 1 else 0 := by
  have he := exponentPolynomial_eval r m 1 hr
  have ht := canonicalTrace_omega_one r hr
  change (fullTwist r 1 1)=1 at ht
  simpa only [Nat.cast_one,pow_one,ht,coeff_one,Int.cast_ite,Int.cast_one,Int.cast_zero] using he

/-- The degree-zero genuine trace coefficient is identically one. -/
theorem exponentPolynomial_zero (r : ℕ) : exponentPolynomial r 0=1 := by
  classical
  simp [exponentPolynomial]

end
end Paper20.HeckeParameterPolynomial
