import Paper29.QueryModel

noncomputable section
open MeasureTheory
namespace Paper29.QueryModel

/-- A probability law cannot have an empty private-seed space. -/
theorem seed_nonempty {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    Nonempty Ω := by
  by_contra h
  haveI : IsEmpty Ω := not_nonempty_iff.mp h
  have he : (Set.univ : Set Ω)=∅ := by ext ω; exact isEmptyElim ω
  have hh := measure_univ (μ:=μ)
  rw [he,measure_empty] at hh
  exact zero_ne_one hh

end Paper29.QueryModel
