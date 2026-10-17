import PUT.Basic
import PUT.QueryModel
import PUT.DirichletMeasure

/-!
# Source-level specifications

These propositions keep the actual objects and quantifiers separate from
proofs. The principal lower bound is proved in `PUT.Paper`, relative to the
explicit published standard inputs; auxiliary positivity calculations are
not substituted for that result.

The circuit family below uses the usual fixed-query pure unitary normal
form. The finite adaptive protocol model and its precise standard normalization
input are given in `PUT.AdaptiveModel`.
-/

noncomputable section
namespace PUT.SourceTargets

open MeasureTheory PUT.QueryModel

/-- The label/garbage register, a query-control qubit, and arbitrary finite
workspace. Every forward/inverse controlled oracle call has unit cost. -/
abbrev TestSpace (d M W : ℕ) :=
  Register (Fin W) (Register Bool (PurificationSpace d M))

/-- An oracle-independent family of circuits which must work for every
finite garbage size. Workspace size may depend on that size. The query
count is the actual run length, and is not part of this definition. -/
structure TesterFamily (d : ℕ) where
  workspace : ℕ → ℕ
  circuit : ∀ M, Circuit (TestSpace d M (workspace M))

def TesterFamily.oracle {d : ℕ} (C : TesterFamily d) {M : ℕ}
    (U : PreparationOracle d M) :
    TestSpace d M (C.workspace M) ≃ₗᵢ[ℂ] TestSpace d M (C.workspace M) :=
  withWorkspace (ι := Fin (C.workspace M)) (controlled U.unitary)

/-- Actual success on every promised full preparation unitary of every
finite garbage dimension, with `Q` actual calls. Arbitrary behavior away
from the promise is permitted, as in the source. -/
def TesterFamily.Tests {d : ℕ} (C : TesterFamily d) (ε : ℝ) (Q : ℕ) : Prop :=
  ∀ (M : ℕ) (U : PreparationOracle d M),
    ((∀ i, U.probability i = (1 : ℝ) / d) →
      (C.circuit M).rejectProbability (C.oracle U) Q ≤ 1 / 100) ∧
    (ε < tvDist U.probability (uniform d) →
      99 / 100 ≤ (C.circuit M).rejectProbability (C.oracle U) Q)

/-- The source Theorem 1 lower bound in the explicit controlled-circuit
normal form. `PUT.Paper.theorem1` proves this proposition with visible
standard external inputs; the legacy `PUT.theorem1` proves target positivity. -/
def Theorem1 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ) (ε : ℝ),
    2 ≤ d → 0 < ε → ε < 1 / 2 →
    ∀ (C : TesterFamily d) (Q : ℕ), C.Tests ε Q →
      theorem1Bound c d ε ≤ (Q : ℝ)

/-- Equation (6) for actual continuous Dirichlet integrals, including
integrability. Defining `dirMoment` by a quotient does not prove this. -/
def DirichletMoments : Prop :=
  ∀ (d : ℕ) (a : ℝ) (k : Fin d → ℕ), 2 ≤ d → 0 < a →
    Integrable (fun p : Fin d → ℝ => ∏ i, p i ^ k i) (dirichletMeasure d a) ∧
      (∫ p, (∏ i, p i ^ k i) ∂dirichletMeasure d a) = dirMoment a k

/-- Source Lemma 2, with the actual continuous prior and event. -/
def Lemma2 : Prop := paperLemma2

end PUT.SourceTargets
