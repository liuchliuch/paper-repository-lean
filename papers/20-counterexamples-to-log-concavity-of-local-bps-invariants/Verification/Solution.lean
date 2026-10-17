import Paper20.Polynomial
import Paper20.Counterexample43

/-!
Required-scope solution exports. Missing declarations are intentional evidence
of the remaining obligations, not placeholders in a production proof.
Superseded contracts existentially choosing unrelated polynomials are not
used as paper coverage. The fixed current challenge retains the actual coefficients.
-/
namespace P20Required
open Paper20

/-- Full actual executable Theorem 1.1, using the complete partition sum
and original Hilbert-array BPS extraction, with no coefficient premise. -/
theorem thm_1_1 :
    bpsCoeff 43 1 23 = 46743830419465000460525749853426296821511513919267 ∧
    bpsCoeff 43 1 24 = 4478706954001198396797888969114794682889954544660295 ∧
    bpsCoeff 43 1 25 = 429147501803199891064835526788080765663004079176388506 ∧
    20000*(bpsCoeff 43 1 24)^2 < 19999*bpsCoeff 43 1 23*bpsCoeff 43 1 25 ∧
    (∀ h ≤ 903, 0 < bpsCoeff 43 1 h) := Paper20.Counterexample43.theorem1_1

theorem prop_3_2_spectral (r h : ℕ) :
    cget (Qcoeff r h) h = transpositionMoment r h / ((2*h).factorial : ℚ) :=
  Paper20.prop_3_2 r h

end P20Required
