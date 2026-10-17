import Paper20.HeckeSaturation

namespace Paper20.HeckeTraceAlgebra
open Polynomial Matrix Finset Paper20.HeckeMatrices Paper20.HeckeWalkExpansion
open Paper20.HeckeSpecialization Paper20.HeckeParameterPolynomial
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

lemma permutationMatrix_diagonal {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (p s : G) : permutationMatrix p s s=if p=1 then 1 else 0 := by
  have he : s=p⁻¹*s ↔ p=1 := by
    constructor
    · intro h
      have hi : (1:G)=p⁻¹ := mul_right_cancel (by simpa only [one_mul] using h)
      exact inv_eq_one.mp hi.symm
    · intro h; simp [h]
  simp only [permutationMatrix,he]

/-- On every ordinary group-specialized Hecke element, all diagonal
entries equal the actual canonical identity coefficient. -/
theorem specialization_diagonal (r : ℕ) (A : Mat r) (hA : A ∈ algebra r) (s : State r) :
    specialize r A s s=(A 1 1).coeff 0 := by
  classical
  have he := congrArg (fun M : Mat r => (specialize r M) s s)
    (identity_column_expansion r A hA)
  dsimp only at he
  rw [map_sum] at he
  simp only [Matrix.sum_apply] at he
  have ht (p : State r) :
      specialize r (A p 1 • basisMatrix r p) s s=
        (A p 1).coeff 0*(if p=1 then 1 else 0) := by
    rw [specialize_apply]
    change (A p 1*basisMatrix r p s s).coeff 0=_
    rw [Polynomial.mul_coeff_zero]
    rw [← specialize_apply r (basisMatrix r p) s s,specialize_basis,permutationMatrix_diagonal]
  simp_rw [ht] at he
  simpa only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',mem_univ,ite_true] using he

/-- The genuine canonical trace becomes the ordinary normalized regular
matrix trace at z=0, on the entire actual Hecke algebra. -/
theorem specialization_regular_trace (r : ℕ) (A : Mat r) (hA : A ∈ algebra r) :
    Matrix.trace (specialize r A)=(r.factorial:ℤ)*(A 1 1).coeff 0 := by
  unfold Matrix.trace Matrix.diag
  simp_rw [specialization_diagonal r A hA]
  simp only [Finset.sum_const,card_univ,nsmul_eq_mul,standardBasis_index_card]

/-- The top coefficient of the true Hecke exponent polynomial is an
ordinary normalized matrix moment of the genuine infinitesimal twist.
The transposition identification remains a separate actual equality. -/
theorem exponentPolynomial_top_regular_trace (r m : ℕ) (hr : 1 ≤ r) :
    (exponentPolynomial r m).coeff m=
      ((Matrix.trace (infinitesimalFullTwist r^m):ℤ):ℚ)/
        ((r.factorial:ℚ)*(m.factorial:ℚ)) := by
  rw [exponentPolynomial_top]
  have ht := specialization_regular_trace r (incrementQuotient r^m)
    ((algebra r).pow_mem (incrementQuotient_mem r hr) m)
  rw [map_pow,specialize_incrementQuotient] at ht
  have hq := congrArg (fun z : ℤ => (z:ℚ)) ht
  simp only [Int.cast_mul,Int.cast_natCast] at hq
  rw [hq]
  have hn : (r.factorial:ℚ) ≠ 0 := by positivity
  field_simp

end
end Paper20.HeckeTraceAlgebra
