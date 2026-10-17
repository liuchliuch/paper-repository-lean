import Paper23.SourceTopology

/-!
# Fixed full Theorem 1 specification, not a proof

The only axiom below is an explicitly trusted challenge hole, confined to
Verification. No production module imports this file. Its purpose is to fix
the complete original result type for the official Comparator, including the
two consequences stated in the source. The theorem target has theorem kind,
which is required to compare it with a future genuine solution theorem.

`MainSolutionSkeleton` does not declare that target. Consequently the full
paper Comparator has no positive solution at present. Auxiliary certificate
algebra checks do not discharge this specification.
-/

namespace P23MainSpecification

/-- Trusted statement hole only; no concrete source homology class is supplied. -/
axiom theoremOneSpecification :
    ∃ z : Paper23.SourceHomology,
      addOrderOf z = 6 ∧
      addOrderOf ((2 : ℕ) • z) = 3 ∧
      addOrderOf ((3 : ℕ) • z) = 2

end P23MainSpecification

namespace P23MainResult

/-- The complete Theorem 1 type for `H₂(F₄(G); ℤ)`, fixed for comparison only. -/
theorem theorem_one :
    ∃ z : Paper23.SourceHomology,
      addOrderOf z = 6 ∧
      addOrderOf ((2 : ℕ) • z) = 3 ∧
      addOrderOf ((3 : ℕ) • z) = 2 :=
  P23MainSpecification.theoremOneSpecification

end P23MainResult
