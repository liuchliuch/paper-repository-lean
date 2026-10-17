import Paper23.MainResult

/-! Deliberately invalid Comparator control: an extra premise changes the
fixed theorem type, even though the premise happens to be inhabited. -/
namespace P23RelativeResult
open Paper23 Paper23.ExternalTopology

theorem theorem_one (ps : PrueScrimshawH2Input)
    (cw : OrderedCubicalComparisonInput) (_extra : True) :
    ∃ z : SourceHomology, addOrderOf z = 6 ∧
      addOrderOf ((2 : ℕ) • z) = 3 ∧ addOrderOf ((3 : ℕ) • z) = 2 :=
  Paper23.main_result ps cw

end P23RelativeResult
