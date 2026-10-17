import K44K35Free.LowerBound
import K44K35Free.FurtherCounts

/-!
# All results of Copies of K₄,₄ in K₃,₅-free graphs

Each source-result alias below is a proved theorem about the actual finite
field geometry or graph. The lower bound discharges the geometric, averaging,
preliminary alteration and local pruning steps before graph padding. There
are no pending statement-only packages or certificates in this module.
-/
namespace K44K35Free

/-- Theorem 1: actual n-vertex bipartite graph existence, for all sufficiently large n. -/
alias theorem_1 := theorem_1_lower_bound

/-- Theorem 1: cubic order for the actual generalized extremal function. -/
alias theorem_1_theta := theorem_1_cubic_order

/-- Lemma 2: eight side-triples per unlabelled copy. -/
alias lemma_2 := lemma_2_upper_bound

/-- The paper's numerical upper-bound form. -/
alias theorem_1_upper_consequence := lemma_2_paper_form

/-- Lemma 3 in coordinates. -/
alias lemma_3 := lemma_3_cap_property

/-- Lemma 3 as actual projective noncollinearity. -/
alias lemma_3_projective := Geometry.point_triple_linearIndependent

/-- Proposition 4: classification, both exact family counts, total incidences,
section bound, identity section size and identity incidence at each point. -/
alias proposition_4 := Geometry.proposition_4

/-- Remark 5 for subsets of the actual cap, using actual identity planes. -/
alias remark_5 := Geometry.remark_5_point_deletion

/-- Lemma 6 with absolute positive constant and field-size threshold. -/
alias lemma_6 := Construction.lemma_6_uniform

/-- Lemma 7 for edges of the actual incidence graph. -/
alias lemma_7 := Construction.designatedPairs_through_edge_le

/-- Lemma 7's uniform O(q⁴) estimate. -/
alias lemma_7_bound := gaussianBinom2_le

/-- Lemma 8 for the actual projective pairing and exceptional planes. -/
alias lemma_8 := Geometry.lemma_8_controlled_intersections

/-- Proposition 9: every actual pruning realization is K₃,₅-free. -/
alias proposition_9 := Construction.proposition9

/-- Proposition 10: a realization retains the stated 6^(-16L)c₂q⁹ copies,
with (25) supplied by the actual preliminary alteration theorem. -/
alias proposition_10 := Construction.proposition10_paper_bound

/-- The preliminary bound (25), obtained jointly for a single pairing. -/
alias preliminary_lower_bound := Construction.exists_preliminary_many_copies

/-- Distinct surviving designated pairs yield distinct unlabelled graph copies. -/
alias designated_copies_le_graph_copies := Construction.survivingPairs_card_le_numK44

end K44K35Free
