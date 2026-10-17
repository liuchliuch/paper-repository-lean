import Paper20.HeckeStandardBasis

namespace Paper20.HeckeTraceAlgebra
open Polynomial Matrix Paper20.HeckeMatrices Paper20.HalfTwistMatrix
open Paper20.HeckeWalkExpansion Paper20.BraidWalk
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

lemma wordMatrix_mem (r : ℕ) (word : List (Fin (r-1))) :
    wordMatrix adjacentMove descent (Polynomial.X:ℤ[X]) word ∈ algebra r := by
  induction word with
  | nil => exact (algebra r).one_mem
  | cons i word ih =>
    rw [wordMatrix_cons]
    exact (algebra r).mul_mem (Algebra.subset_adjoin (Set.mem_range_self i)) ih

lemma halfTwist_mem (r : ℕ) : halfTwist r ∈ algebra r := wordMatrix_mem r _

lemma fullTwist_mem (r : ℕ) : fullTwist r ∈ algebra r :=
  (algebra r).pow_mem (halfTwist_mem r) 2

/-- The genuine full-twist element of the concrete Hecke algebra, with
its free permutation basis and normalized cyclic canonical trace. -/
def omega (r : ℕ) : algebra r := ⟨fullTwist r,fullTwist_mem r⟩

/-- The actual canonical symmetrizing trace of Omega^(k+1) is exactly the
walk polynomial from the source. The Hilbert/BPS identification is not a
premise of this Hecke identity. -/
theorem canonicalTrace_omega (r k : ℕ) (hr : 1 ≤ r) :
    canonicalTrace r (omega r^(k+1))=closedHeckePolynomial r k :=
  Paper20.HeckeFullTwistTrace.fullTwist_identity_entry r k hr

theorem canonicalTrace_omega_even_variable (r k : ℕ) (hr : 1 ≤ r) :
    canonicalTrace r (omega r^(k+1))=(walkBPSPolynomial r k).comp (X^2) := by
  rw [canonicalTrace_omega r k hr,closedHeckePolynomial_eq_comp]

theorem canonicalTrace_omega_coeff (r k h : ℕ) (hr : 1 ≤ r) :
    (canonicalTrace r (omega r^(k+1))).coeff (2*h)=(walkCount r k h:ℤ) := by
  rw [canonicalTrace_omega r k hr,closedHeckePolynomial_coeff]

/-- Canonical trace normalization for a single full twist, proved via the
actual degree-zero walk polynomial and its unique all-move walk. -/
theorem canonicalTrace_omega_one (r : ℕ) (hr : 1 ≤ r) : canonicalTrace r (omega r)=1 := by
  have he := canonicalTrace_omega r 0 hr
  simp only [Nat.zero_add,pow_one] at he
  rw [he,closedHeckePolynomial_eq_comp]
  have hp : walkBPSPolynomial r 0=1 := by
    apply Polynomial.ext
    intro i
    rw [walkBPSPolynomial_coeff]
    have hd : deg r 0=0 := by simp [deg]
    rw [hd]
    by_cases hi : i=0
    · subst i
      simp only [le_refl,↓reduceIte,coeff_one,ite_true]
      have hc := walk_endpoints r 0 |>.1
      exact_mod_cast hc
    · rw [if_neg (by omega),coeff_one,if_neg hi]
  rw [hp,one_comp]

end
end Paper20.HeckeTraceAlgebra
