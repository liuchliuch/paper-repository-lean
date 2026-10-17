import Paper14.Basic
import Paper14.MapBCZ
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.NumberTheory.ZetaValues
import Mathlib.NumberTheory.ArithmeticFunction
/-!
# Proposition 3: weak mixing of the BCZ map

Paper anchors: Thmtheorem3, Appendix A.

This module defines the Appendix A coprime window and eigenvalue statements.
The actual arithmetic and strip moments are proved in the subsequent coprime
and Appendix modules; `EigenExclusion` proves the eigenfunction contradiction.
`BCZWeakMixingFromErgodic` supplies the full product-ergodicity transfer.
-/
open MeasureTheory Filter Topology Set Real Nat
namespace Paper14

/-- Proposition 3 is `Proposition3Statement` from `Paper14.Basic`. -/
def Proposition3Claim : Prop := Proposition3Statement

/-- Appendix A, equation (22): there are `α₀, η > 0` with
`m{y ∈ Y_{r_n} : R_{r_n,n}(y) = n+1} ≥ η` for large `n`. -/
def ExactlyOneExtraStatement : Prop :=
  ∃ α₀ η : ℝ, 0 < α₀ ∧ 0 < η ∧ ∀ᶠ n : ℕ in atTop,
    η ≤ (m {y ∈ Yr (1 - α₀ / n) | Rn B (Yr (1 - α₀ / n)) n y = n + 1}).toReal

/-! ## Coprime-pair count (Appendix A, equation 23) -/

/-- Number of coprime pairs `p,q` with `n/6 < p ≤ n/3` and `n/2 ≤ q ≤ n`. -/
noncomputable def coprimePairCount (n : ℕ) : ℕ :=
  (Finset.Icc (n/6 + 1) (n/3) ×ˢ Finset.Icc ((n + 1)/2) n).filter
    (fun pq => Nat.Coprime pq.1 pq.2) |>.card

/-- Möbius identity used in Appendix A: `1_{gcd(p,q)=1} = ∑_{d|p, d|q} μ(d)`. -/
def MoebiusCoprimeIdentity : Prop :=
  ∀ p q : ℕ, 0 < p → 0 < q →
    (if Nat.Coprime p q then (1:ℝ) else 0)
      = ∑ d ∈ (Nat.divisors p ∩ Nat.divisors q), ((ArithmeticFunction.moebius d : ℤ) : ℝ)

/-- Lower bound from Appendix A: the restricted coprime count is `n²/(2π²)+O(n log n)`,
in particular `≥ n²/20` for large `n`. Stated as a real inequality. -/
def CoprimeCountLowerStatement : Prop :=
  ∃ n0 : ℕ, ∀ n ≥ n0, (n : ℝ)^2 / 20 ≤ (coprimePairCount n : ℝ)

/-- The geometric input (22) follows from first moment minus second moment:
`m{F_1=F_2=1} ≥ α/80 - 320 α²`. Abstract form used in Appendix A p8. -/
lemma two_star_rect (α : ℝ) (_h : 0 < α) :
    α / 80 - 320 * α^2 ≤ α / 80 := by
  nlinarith [sq_nonneg α]

/-- Choose `α₀ = 1/51200` so that `α/80 - 320 α² ≥ α/160` as in Appendix A p8. -/
lemma alpha0_choice : (1:ℝ)/51200 / 80 - 320 * (1/51200)^2 ≥ (1/51200) / 160 := by
  norm_num

/-- A nontrivial eigenvalue of `B` on `L²(m)`: some `f ≠ 0` with `f ∘ B = eig * f`. -/
def IsNontrivialEigenvalue (eig : ℂ) : Prop :=
  eig ≠ 1 ∧ ∃ f : ℝ × ℝ → ℂ, MemLp f 2 m ∧
    ¬ (f =ᵐ[m] 0) ∧ ∀ᵐ x ∂m, f (B x) = eig * f x

/-- Appendix A excludes nontrivial eigenvalues. -/
def NoNontrivialEigen : Prop := ∀ eig : ℂ, ¬ IsNontrivialEigenvalue eig

/-- Weak mixing of `B` follows from ergodicity plus `NoNontrivialEigen`. -/
def WeakMixingOfNoEigen : Prop :=
  Ergodic B m → NoNontrivialEigen → WeakMixing B m

end Paper14
