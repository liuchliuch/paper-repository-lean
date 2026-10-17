import Paper23.ExternalTopology

/-! Fixed relative specification.  The challenge hole is confined to
Verification and is never imported by production or the solution.  The two
external inputs are exactly the registered established topology dependencies;
there is no certificate or order-six assumption in the theorem type. -/
namespace P23RelativeSpecification
open Paper23 Paper23.ExternalTopology

axiom theoremOneSpecification (ps : PrueScrimshawH2Input)
    (cw : OrderedCubicalComparisonInput) :
    ∃ z : SourceHomology, addOrderOf z = 6 ∧
      addOrderOf ((2 : ℕ) • z) = 3 ∧ addOrderOf ((3 : ℕ) • z) = 2

end P23RelativeSpecification

namespace P23RelativeResult
open Paper23 Paper23.ExternalTopology

theorem theorem_one (ps : PrueScrimshawH2Input)
    (cw : OrderedCubicalComparisonInput) :
    ∃ z : SourceHomology, addOrderOf z = 6 ∧
      addOrderOf ((2 : ℕ) • z) = 3 ∧ addOrderOf ((3 : ℕ) • z) = 2 :=
  P23RelativeSpecification.theoremOneSpecification ps cw

end P23RelativeResult
