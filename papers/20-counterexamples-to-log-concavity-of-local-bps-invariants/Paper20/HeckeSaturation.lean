import Paper20.HeckeParameterLeading

namespace Paper20.HeckeTraceAlgebra
open Polynomial Matrix Finset Paper20.HeckeMatrices Paper20.HeckeWalkExpansion
open Paper20.HeckeSpecialization Paper20.HeckeParameterPolynomial
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

lemma sum_basis_mem (r : ℕ) (f : State r → ℤ[X]) :
    (∑ p : State r, f p • basisMatrix r p) ∈ algebra r := by
  apply (algebra r).sum_mem
  intro p hp
  exact (algebra r).smul_mem (basisMatrix_mem r p) (f p)

lemma sum_basis_column (r : ℕ) (f : State r → ℤ[X]) :
    (∑ p : State r, f p • basisMatrix r p).mulVec (delta (1 : State r))=f := by
  classical
  rw [Matrix.sum_mulVec]
  simp_rw [Matrix.smul_mulVec,basisMatrix_delta]
  funext s
  simp [Finset.sum_apply,Pi.smul_apply,delta,smul_eq_mul,mul_ite]

/-- Coordinates of every genuine Hecke element in the proved free
permutation basis are precisely its identity-column entries. -/
theorem identity_column_expansion (r : ℕ) (A : Mat r) (hA : A ∈ algebra r) :
    A=∑ p : State r, A p 1 • basisMatrix r p := by
  apply eq_of_identity_column r _ _ hA (sum_basis_mem r _)
  rw [sum_basis_column]
  funext s
  rw [mulVec_delta]

/-- The actual free Hecke subalgebra is saturated under division by its
parameter whenever the constant specialization vanishes. -/
theorem algebra_divX_mem (r : ℕ) (A : Mat r) (hA : A ∈ algebra r)
    (h0 : specialize r A=0) : (fun s t => (A s t).divX) ∈ algebra r := by
  classical
  let B : Mat r := ∑ p : State r, (A p 1).divX • basisMatrix r p
  have hB : B ∈ algebra r := sum_basis_mem r _
  have hc (s t : State r) : (A s t).coeff 0=0 := by
    have he := congrFun (congrFun h0 s) t
    simpa only [specialize_apply,Matrix.zero_apply] using he
  have hx (s t : State r) : X*(A s t).divX=A s t := by
    have he := X_mul_divX_add (A s t)
    simpa only [hc,map_zero,add_zero] using he
  have hBA : (Polynomial.X:ℤ[X]) • B=A := by
    apply eq_of_identity_column r _ _ ((algebra r).smul_mem hB Polynomial.X) hA
    rw [Matrix.smul_mulVec]
    change (Polynomial.X:ℤ[X]) •
      (∑ p : State r, (A p 1).divX • basisMatrix r p).mulVec (delta (1 : State r))=_
    rw [sum_basis_column]
    funext s
    simp only [Pi.smul_apply,smul_eq_mul,mulVec_delta]
    exact hx s 1
  have he : B=(fun s t => (A s t).divX) := by
    apply Matrix.ext
    intro s t
    apply mul_left_cancel₀ (Polynomial.X_ne_zero : (X:ℤ[X]) ≠ 0)
    have hb := congrFun (congrFun hBA s) t
    change X*B s t=A s t at hb
    exact hb.trans (hx s t).symm
  rwa [← he]

/-- The concrete first-order quotient of the genuine full twist is itself
an actual element of the same free Hecke algebra. -/
theorem incrementQuotient_mem (r : ℕ) (hr : 1 ≤ r) : incrementQuotient r ∈ algebra r := by
  apply algebra_divX_mem r (Paper20.HalfTwistMatrix.fullTwist r-1)
    ((algebra r).sub_mem (fullTwist_mem r) (algebra r).one_mem)
  rw [map_sub,specialize_fullTwist r hr,map_one,sub_self]

end
end Paper20.HeckeTraceAlgebra
