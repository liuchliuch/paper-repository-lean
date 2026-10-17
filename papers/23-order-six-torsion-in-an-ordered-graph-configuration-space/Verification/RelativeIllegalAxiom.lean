import Paper23.ExternalTopology

/-! Deliberately invalid Comparator control: the statement agrees, but the
proof depends on a forbidden new axiom. -/
namespace P23RelativeResult
open Paper23 Paper23.ExternalTopology

axiom forbidden : False

theorem theorem_one (ps : PrueScrimshawH2Input)
    (cw : OrderedCubicalComparisonInput) :
    ∃ z : SourceHomology, addOrderOf z = 6 ∧
      addOrderOf ((2 : ℕ) • z) = 3 ∧ addOrderOf ((3 : ℕ) • z) = 2 :=
  False.elim forbidden

end P23RelativeResult
