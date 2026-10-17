import Paper15.AssembleGap
import Paper15.CertifiedRepresentatives
import Paper15.CertifiedNeighbours

namespace Paper15
open OrbitCheck

/-- Full orbit coverage, proved from every kernel-checked neighbour row. -/
theorem all_response_tables_covered : ∀T : DetTriangle,
    ∃r∈representatives.toFinset,∃g : Symmetry,g.apply (DetTriangle.ofPattern r)=T :=
  all_response_tables_covered_of_checked all_neighbours_checked

/-- Lemma 5, all nonexceptional tables and all boundary source laws. -/
theorem lemma5_certified_gap (T : DetTriangle) (hT : ¬inExceptionalOrbit T) : GapHolds T :=
  gap_of_checked_trees all_representatives_classified all_neighbours_checked T hT

theorem certifiedGapHypothesis : GapHypothesis := lemma5_certified_gap
end Paper15
