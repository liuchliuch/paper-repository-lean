import Paper20.Uniform36

/-! Exact ancillary computations of §5 and Appendix A. These results concern
the embedded polynomial certificate; identification with (20) is separate. -/
namespace Paper20.Uniform36

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The displayed denominator factorization (31). -/
theorem denominator_factorization :
    Dval = 2^63 * 3^32 * 5^16 * 7^10 * 11^7 * 13^6 * 17^4 * 19^4 *
      (23*29*31*37*41)^2 * 43 := by decide

/-- Table 1, preserving its row order and decimal exponents. -/
def tableBounds : List (ℕ × ℕ) :=
  [(300722,242),(450959,242),(146709,242),
   (253819,241),(292356,240),(248562,239),
   (165463,238),(895750,236),(404867,235),
   (155743,234),(517344,232),(150076,231),
   (383600,229),(870127,227),(176170,226),
   (319860,224),(522779,222),(771483,220),
   (103046,219),(124805,217),(137250,215),
   (137166,213),(124629,211),(102950,209),
   (772822,206),(526728,204),(325506,202),
   (182048,200),(919200,197),(417723,195),
   (170198,193),(618795,190),(199581,188),
   (566917,185),(140542,183),(300596,180),
   (546495,177),(827970,174),(101710,172),
   (973272,168),(680591,165),(309354,162),(685924,158)]

/-- All 43 exact inequalities printed in Table 1. -/
theorem table1_verified : ∀ j < 43,
    let de := tableBounds.getD j (0,0)
    (de.1 : ℤ) * 10^de.2 ≤ bOf j ∧ bOf j < (de.1+1 : ℤ)*10^de.2 := by
  decide

/-- The three displayed moments agree with the leading coefficients of the
embedded contact polynomials, as checked in Appendix A. -/
theorem leading20 : Q20.coeff 20 = (T20 : ℚ) / (Nat.factorial 40 : ℚ) := by
  rw [Q20, Polynomial.coeff_C_mul, coeff_poly]
  norm_num [AQ, AList, A20, Dqval, T20, List.getD]

theorem leading21 : Q21.coeff 21 = (T21 : ℚ) / (Nat.factorial 42 : ℚ) := by
  rw [Q21, Polynomial.coeff_C_mul, coeff_poly]
  norm_num [BQ, BList, B21, Dqval, T21, List.getD]

theorem leading22 : Q22.coeff 22 = (T22 : ℚ) / (Nat.factorial 44 : ℚ) := by
  rw [Q22, Polynomial.coeff_C_mul, coeff_poly]
  norm_num [CQ, CList, C22, Dqval, T22, List.getD]

end Paper20.Uniform36
