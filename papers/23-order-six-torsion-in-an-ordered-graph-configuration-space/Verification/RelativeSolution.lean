import Paper23.MainResult

/-! Solution wrapper.  It imports no challenge or specification axiom. -/
namespace P23RelativeResult
open Paper23 Paper23.ExternalTopology

theorem theorem_one (ps : PrueScrimshawH2Input)
    (cw : OrderedCubicalComparisonInput) :
    ∃ z : SourceHomology, addOrderOf z = 6 ∧
      addOrderOf ((2 : ℕ) • z) = 3 ∧ addOrderOf ((3 : ℕ) • z) = 2 :=
  Paper23.main_result ps cw

end P23RelativeResult
