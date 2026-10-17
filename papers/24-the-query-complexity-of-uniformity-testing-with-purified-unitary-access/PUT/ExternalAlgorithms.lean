import PUT.SourceTargets
import PUT.TestingLowerBound

/-!
# Explicit standard quantum error-reduction input

This interface is the nine-independent-run specialization of standard
unitary purification and bounded-error amplification. It concerns arbitrary
actual oracle-independent circuit families and actual preparation unitaries;
it says nothing about Dirichlet priors, adversaries or query lower bounds.

Reference: John Watrous, "Quantum Computational Complexity", Sections III.3
and IV.2 (Proposition 3), https://cs.uwaterloo.ca/~watrous/Papers/QuantumComputationalComplexity.pdf .
The exact nine-run constant is the elementary union bound
`2^9 * (1/100)^5`, proved numerically in TestingLowerBound. This module is
only an explicitly supplied external proposition; no existence is asserted
as a theorem and no axiom/sorry is installed.
-/
noncomputable section
namespace PUT.External
open PUT.SourceTargets PUT.QueryModel PUT.TestingLowerBound

/-- Independent repetition preserves the full permitted oracle access model,
uses exactly nine times as many calls, and reduces both promised errors.
The circuit may increase its finite workspace, independently of the oracle. -/
def NinefoldAmplificationLaw : Prop :=
  ∀ (d : ℕ) (C : TesterFamily d) (Q : ℕ), ∃ amplified : TesterFamily d,
    ∀ (M : ℕ) (U : PreparationOracle d M),
      ((C.circuit M).rejectProbability (C.oracle U) Q ≤ 1 / 100 →
        (amplified.circuit M).rejectProbability (amplified.oracle U) (9 * Q) ≤ ninefoldError) ∧
      (99 / 100 ≤ (C.circuit M).rejectProbability (C.oracle U) Q →
        1 - ninefoldError ≤
          (amplified.circuit M).rejectProbability (amplified.oracle U) (9 * Q))

end PUT.External
