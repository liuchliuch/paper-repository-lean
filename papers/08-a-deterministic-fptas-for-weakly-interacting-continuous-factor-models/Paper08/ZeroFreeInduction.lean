import Paper08.ZeroFreeReplacementBound
import Paper08.ZeroFreeReplacementPath
import Paper08.ZeroFreeTelescoping

/-! # The phase step of the uniform finite-cube cardinality induction

Every premise concerning partial expectations is the induction hypothesis
or the preceding uniform nonzero step. Each replacement is an actual bounded
continuous real-potential interpolation, so its derivative and endpoint
identities are proved integral formulas, not input certificates.
-/
noncomputable section
namespace Paper08.ZeroFreeInduction
open Integral CubeMarginal ComplexSector

variable {n m r c : ℕ} {q θ : ℝ} {z : ℂ}

/-- At the next cardinality, use its already proved uniform nonvanishing to
 follow each continuous replacement path; use smaller-cardinality phases to
 bound the path's logarithmic derivative. Finite telescoping then gives the
 full coordinate phase bound. -/
theorem coordinatePhase_of_good {k : ℕ} (ih : Good n m r c q z θ k)
    (hnz : ∀ N : Model n m r c q, ∀ U : Finset (Fin n), U.card ≤ k+1 →
      ∀ y ∈ cube n, N.partial U z y ≠ 0)
    (hq : 0 ≤ q) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hpow : (1 : ℝ)/2 ≤ Real.cos θ ^ (r-1))
    (hbudget : 2 * (c : ℝ) * ‖z‖ * q ≤ θ)
    (M : Model n m r c q) (S : Finset (Fin n)) (hS : S.card ≤ k+1) :
    CoordinatePhase M S z θ := by
  apply coordinatePhase_of_replacements hq hbudget M S
  intro x hx j hj a ha b hb A e heI heA
  have hp := replacementPath_hasDerivAt_and_continuous M hq j A e ha hb S hx z
  apply replacement_phase_of_path ih hnz hq hθ0 hθ1 hpow M S hS hx j A e heI ha hb
    (replacementPath M j A e ha hb S x z)
    (replacementDerivative M j A e ha hb S x z)
    hp.2.continuousOn (fun t _ => hp.1 t)
  · intro t ht
    exact replacementPath_eq_partial M j A e heA ha hb S x z t ht
  · intro t ht
    exact replacementDerivative_eq_avg M j A e heA ha hb S x z t ht
  · exact replacementPath_zero M j A e ha hb S x z
  · exact replacementPath_one M j A e heA ha hb S x z

end Paper08.ZeroFreeInduction
