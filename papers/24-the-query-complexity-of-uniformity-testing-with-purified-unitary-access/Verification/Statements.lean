import PUT.Basic
import Verification.BridgeStatements
import Verification.PaperStatements
import PUT.Collision
import PUT.Main

/-!
# Auxiliary specifications for paper 24

These legacy numerical specifications are algebraic prerequisites only.
They are not the source Theorem 1 or Lemmas 1–2. The actual semantic
bridges are specified in `Verification.BridgeStatements`; principal source
contracts are specified independently in `Verification.PaperStatements`.
Each `def` is a `Prop` naming one auxiliary obligation.  The Comparator contract expects these exact names and types to be
proved in `Verification.Solution` and mirrored (as `sorry`) in
`Verification.Challenge`.
-/

noncomputable section
open PUT

namespace Verification.Specification

/-- Algebraic constants for Lemma 2; this contains no Dirichlet event mass.
The variance lower bound `σ² ≥ 1/(4ad²)` and the Paley–Zygmund constants
`E[Z] ≥ 1/(12√a)`, `E[Z²] ≤ 1/(4a)`, `ℙ[Z ≥ 1/(24√a)] ≥ 1/144`. -/
def Lemma2_Main : Prop :=
  ∀ (d : ℕ) (a : ℝ), 2 ≤ d → 1 ≤ a →
    (1 / (4 * a * (d : ℝ) ^ 2) : ℝ) ≤ ((d : ℝ) - 1) / ((d : ℝ) ^ 2 * (a * d + 1)) ∧
      q0 = (1 / 144 : ℝ) ∧
        lemma2Threshold a = 1 / (24 * Real.sqrt a) ∧
          ((1 / (12 * Real.sqrt a)) ^ 2 / (4 * (1 / (4 * a))) : ℝ) = q0

/-- Nonnegativity and definitional expansion of the Lemma 1 scalar envelope;
this contains no query-difference operator. The three terms of the proposed
bound are nonnegative and assemble into `lemma1RHS`. -/
def Lemma1_Bound : Prop :=
  ∀ (d a A M : ℝ), 2 ≤ d → 0 < a → 1 ≤ A → 16 * A ^ 2 * LA A ≤ M →
    0 ≤ Real.sqrt (1 + A / d) ∧
      0 ≤ A ^ (3 / 2 : ℝ) / (a * Real.sqrt d) ∧
        0 ≤ A / Real.sqrt (a * d) ∧
          lemma1RHS A a d = 20 * (Real.sqrt (1 + A / d) + A ^ (3 / 2 : ℝ) / (a * Real.sqrt d)
            + A / Real.sqrt (a * d))

/-- Theorem 1 constant. -/
def Theorem1_Constant : Prop := 0 < c0

/-- Algebraic target expression for Theorem 1: positivity of the expression,
the constant-accuracy absorption `min(d^{1/3}ε^{-4/3}, √d/ε) ≤ 48^{4/3} d^{1/3}`,
and the substitution inequality that makes `c₀ = 1/3000` work. -/
def Theorem1_Target : Prop :=
  (∀ (d : ℕ) (ε : ℝ), 2 ≤ d → 0 < ε → ε < 1 / 2 → 0 < theorem1Bound c0 d ε) ∧
    (∀ (d ε : ℝ), 2 ≤ d → 1 / 48 < ε → ε < 1 / 2 →
      theorem1Bound 1 d ε ≤ 48 ^ (4 / 3 : ℝ) * d ^ (1 / 3 : ℝ)) ∧
      (∀ (d ε : ℝ), 0 < d → 0 < ε →
        theorem1Bound c0 d ε
          ≤ min (d ^ (1 / 3 : ℝ) * (dirichletScale ε) ^ (2 / 3 : ℝ))
              (Real.sqrt (d * dirichletScale ε)))

/-- Fourier cutoff identities: `K(k) = ∑ k_i ≤ ∑ k_i² = R(k)`. -/
def Cutoff_Theory : Prop :=
  ∀ (d : ℕ) (k : Fin d → ℕ), degK k ≤ degR k

/-- Dirichlet moment formula. -/
def Moments_Formula : Prop :=
  ∀ (a : ℝ) {d : ℕ} (k : Fin d → ℕ),
    dirMoment a k = (∏ i, risingFactorial a (k i)) / risingFactorial (a * d) (degK k)

/-- Collision TV separation: the four-to-one instance is more than `1/2`
from uniform whenever `d ≥ 8`. -/
def Collision_TV : Prop :=
  ∀ d : ℕ, 8 ≤ d → (1 / 2 : ℝ) < collTV d

/-- Progress-measure lower bound: a fractional decrease `q₀/8` after `T`
queries forces `T ≥ q₀ A /(8B)`. -/
def Progress_Lower : Prop :=
  ∀ (A B q0 T : ℝ), 0 < A → 0 < B → 0 < q0 → 0 ≤ T →
    A * (1 - q0 / 8) ≥ A - T * B → q0 * A / (8 * B) ≤ T

/-- Dirichlet scale choice: `a = (48ε)⁻² ≥ 1` in the small-accuracy range. -/
def Scale_Choice : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 48 → 1 ≤ dirichletScale ε

end Verification.Specification
