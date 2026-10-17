import Paper20.Hilbert
import Paper20.Polynomial
import Verification.Objects

/-!
The required paper-facing statements for the executable Hilbert model.
These deliberately include the actual BPS coefficients and the same `Q`.
Only this isolated specification contains placeholders. No production module
imports it, and the unsolved statements are NOT claimed as proved.
The geometric Hilbert/HOMFLY/Hecke correspondence requires additional work.
-/
namespace P20Required
open Paper20

theorem thm_1_1 :
    bpsCoeff 43 1 23 = 46743830419465000460525749853426296821511513919267 ∧
    bpsCoeff 43 1 24 = 4478706954001198396797888969114794682889954544660295 ∧
    bpsCoeff 43 1 25 = 429147501803199891064835526788080765663004079176388506 ∧
    20000*(bpsCoeff 43 1 24)^2 < 19999*bpsCoeff 43 1 23*bpsCoeff 43 1 25 ∧
    (∀ h ≤ 903, 0 < bpsCoeff 43 1 h) := by sorry

theorem thm_1_2 : ∀ k : ℕ, 10 ≤ k →
    (bpsCoeff 36 k 21)^2 < bpsCoeff 36 k 20*bpsCoeff 36 k 22 ∧
    (∀ h ≤ deg 36 k, 0 < bpsCoeff 36 k h) := by sorry

theorem lemma_2_2 (r k h : ℕ) (hr : 2 ≤ r) (hk : 1 ≤ k) (hh : h ≤ deg r k) :
    1 ≤ bpsCoeff r k h ∧ bpsCoeff r k h ≤ Nat.choose (2*deg r k) (2*h) ∧
    bpsCoeff r k 0 = 1 ∧ bpsCoeff r k (deg r k) = 1 := by sorry

theorem prop_3_1 (r h : ℕ) (hr : 2 ≤ r) :
    (∀ i, h < i → cget (Qcoeff r h) i = 0) ∧
    (∀ k, 1 ≤ k → h ≤ deg r k →
      (bpsCoeff r k h : ℚ) = peval (Qcoeff r h) ((k:ℚ)*(k+1))) ∧
    peval (Qcoeff r h) 0 = if h = 0 then 1 else 0 := by sorry

/-- The proven spectral-sum clause must concern this same constructed Q.
The additional identification of the content moment with transposition
return walks remains a required character-theoretic bridge. -/
theorem prop_3_2_spectral (r h : ℕ) :
    cget (Qcoeff r h) h = transpositionMoment r h / ((2*h).factorial : ℚ) := by sorry

/-- Full Proposition 3.2, using genuine permutation return walks, not a
spectral expression substituted for their definition. -/
theorem prop_3_2 (r h : ℕ) (hr : 2 ≤ r) :
    cget (Qcoeff r h) h = (P20Objects.transpositionReturns r h : ℚ) /
      ((2*h).factorial : ℚ) := by sorry

end P20Required
