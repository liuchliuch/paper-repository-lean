import Paper20.HalfTwistBasis

namespace Paper20.HeckeFullTwistTrace
open Polynomial Matrix Paper20.HeckeMatrices Paper20.HeckeWalkExpansion
open Paper20.HalfTwistMatrix Paper20.BraidWalk
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

section Generic
variable {S R : Type*} [Fintype S] [DecidableEq S] [CommRing R]

lemma sandwich_entry (A B : Matrix S S R) (e top : S)
    (hsym : A.transpose=A) (he : A.mulVec (delta e)=delta top) :
    (A*B*A) e e=B top top := by
  classical
  have hc : ∀ s, A s e=delta top s := by
    intro s
    have h := congrFun he s
    simpa only [mulVec_delta] using h
  have hr : ∀ s, A e s=delta top s := by
    intro s
    have h := congrFun (congrFun hsym s) e
    exact h.trans (hc s)
  simp only [Matrix.mul_apply,hc,hr,delta,ite_mul,mul_ite,one_mul,zero_mul,mul_one,mul_zero]
  simp

/-- Moving the two outer symmetric half twists converts the identity
coefficient to the longest-state diagonal coefficient. -/
theorem square_power_identity_entry (A : Matrix S S R) (e top : S)
    (hsym : A.transpose=A) (he : A.mulVec (delta e)=delta top) (k : ℕ) :
    ((A^2)^(k+1)) e e=((A^2)^k) top top := by
  have hp : (A^2)^(k+1)=A*((A^2)^k)*A := by
    simp only [← pow_mul]
    calc
      A^(2*(k+1))=A^(1+2*k+1) := by congr 1; omega
      _ = A*A^(2*k)*A := by rw [pow_add,pow_add,pow_one]
  rw [hp,sandwich_entry A _ e top hsym he]

end Generic

/-- The actual standard-basis identity entry of the (k+1)-st full twist
is exactly the source's closed-walk polynomial. The equality is proved
from actual matrices and explicit half-twist ascent/reversal calculations. -/
theorem fullTwist_identity_entry (r k : ℕ) (hr : 1 ≤ r) :
    ((fullTwist r)^(k+1)) 1 1=closedHeckePolynomial r k := by
  rw [fullTwist,square_power_identity_entry (halfTwist r) 1 Fin.revPerm
    (halfTwist_transpose r) (halfTwist_delta r hr)]
  rw [← pow_mul,← wordMatrix_palindrome,wordMatrix_diagonal]
  rfl

/-- In the paper's even variable, the identity entry is the same actual
walk-count polynomial, rather than a separately embedded coefficient list. -/
theorem fullTwist_identity_polynomial (r k : ℕ) (hr : 1 ≤ r) :
    ((fullTwist r)^(k+1)) 1 1=(walkBPSPolynomial r k).comp (X^2) := by
  rw [fullTwist_identity_entry r k hr,closedHeckePolynomial_eq_comp]

theorem fullTwist_identity_coeff (r k h : ℕ) (hr : 1 ≤ r) :
    (((fullTwist r)^(k+1)) 1 1).coeff (2*h)=(walkCount r k h:ℤ) := by
  rw [fullTwist_identity_entry r k hr,closedHeckePolynomial_coeff]

end
end Paper20.HeckeFullTwistTrace
