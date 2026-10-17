import Paper29.CheckedExpanded
import Paper29.PilotFull
import Paper29.NumberedContracts
import Paper29.LowerProof
import Paper29.MinimaxProof
import Paper29.GeneralSourceTranscript
import Paper29.MeasurableSelection

namespace Paper29.Checked

theorem theorem22 : ExpandedSpecification.theorem22 := QueryModel.theorem2_2

theorem corollary23 : ExpandedSpecification.corollary23 := QueryModel.corollary2_3

theorem lemma32 : ExpandedSpecification.lemma32 := by
  refine ⟨WeightConstruction.constructed_scheme,?_⟩
  intro α C hα hC external n d A hA hrows a b hab hlength scheme
  exact ⟨(fun j => Leverage.leverage_sum_of_rank_eq A (scheme.w j) hA (scheme.w j).property),
    external n d A hA hrows a b hab hlength scheme⟩

theorem lemma33 : ExpandedSpecification.lemma33 := Chaining.endpoint_cover_all_radii

theorem lemma35 : ExpandedSpecification.lemma35 := ProcessTools.unshifted_expectation_bound

theorem lemma36 : ExpandedSpecification.lemma36 := ProcessTools.centered_affine_transfer_scores

theorem lemma39 : ExpandedSpecification.lemma39 := ProcessTools.pilot_full_guarantee

theorem lemma43 : ExpandedSpecification.lemma43 := GeneralTranscript.lemma4_3

theorem appendixA3 : ExpandedSpecification.appendixA3 := Attainment.minimumNormSelection_regularization

end Paper29.Checked
