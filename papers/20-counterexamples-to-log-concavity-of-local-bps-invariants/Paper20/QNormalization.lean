import Paper20.YoungDimensionNorm
import Paper20.PolynomialEval
import Verification.Objects

namespace Paper20
open Polynomial
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

/-- The same constructed polynomial has the required zero-order value,
with the dimension-square identity now proved at every rank. -/
theorem Qcoeff_zero_order_at_zero (r : ℕ) : peval (Qcoeff r 0) 0=1 :=
  Qcoeff_r0_one r (dimSquareSum_eq_factorial r)

/-- The whole zero-order polynomial, interpreted as a polynomial, is 1. -/
theorem Qcoeff_zero_order_polynomial (r : ℕ) : listPolynomial (Qcoeff r 0)=1 := by
  ext i
  rw [coeff_listPolynomial]
  by_cases hi : i=0
  · subst i
    simpa only [peval_zero,Polynomial.coeff_one_zero] using Qcoeff_zero_order_at_zero r
  · rw [Qcoeff_degree r 0 i (by omega),Polynomial.coeff_one,if_neg hi]

/-- The zero-order evaluation is one for every polynomial argument. -/
theorem Qcoeff_zero_order_eval (r : ℕ) (u : ℚ) : peval (Qcoeff r 0) u=1 := by
  rw [← eval_listPolynomial,Qcoeff_zero_order_polynomial,Polynomial.eval_one]

/-- The actual content moment of order zero is 1, with no assumed
irreducible-dimension or trace-character identity. -/
theorem transpositionMoment_zero (r : ℕ) : transpositionMoment r 0=1 := by
  have he : transpositionMomentInt r 0=dimSquareSum r := by
    simp only [transpositionMomentInt,dimSquareSum,Nat.mul_zero,pow_zero,mul_one]
  rw [transpositionMoment,he,dimSquareSum_eq_factorial]
  exact div_self (by positivity)

/-- The spectral expression agrees with the independently defined empty
transposition return count. Positive moments still require their own bridge. -/
theorem transpositionMoment_zero_returns (r : ℕ) :
    transpositionMoment r 0=(P20Objects.transpositionReturns r 0:ℚ) := by
  rw [transpositionMoment_zero,P20Objects.transpositionReturns_zero,Nat.cast_one]

end
end Paper20
