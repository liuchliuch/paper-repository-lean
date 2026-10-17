import Paper35
import Lean

/-! PREPARED ONLY: verification_deferred_by_user.
Printing exact current theorem types must wait for the user's heavy run.
The generated text still requires independent correspondence review.
-/
open Lean Elab Command
set_option pp.fullNames true
set_option pp.explicit true
set_option pp.coercions true
set_option pp.universes true
set_option pp.notation false
set_option pp.fieldNotation false
set_option pp.funBinderTypes true
set_option pp.proofs true
set_option pp.proofs.threshold 100000000
set_option pp.deepTerms true
set_option pp.deepTerms.threshold 100000000
set_option pp.maxSteps 100000000
set_option maxRecDepth 32768

run_cmd do
  let env ← getEnv
  let names : Array Name := #[`Paper35.Counterexamples.atomic_bias_densities_unbounded,
    `Paper35.Counterexamples.atomic_bias_source_density,
    `Paper35.Counterexamples.dependentBiasLaw_density,
    `Paper35.Counterexamples.dependent_conditional_bias_not_absolutelyContinuous,
    `Paper35.Counterexamples.proposition_5_2,
    `Paper35.Deep.gaussianMaxSecondMoment_le_lengthCorrection,
    `Paper35.Deep.gaussian_rank_second_moment_lower,
    `Paper35.DeepModel.Network.LayerSource.lengthFactor_le_rank_secondMoment,
    `Paper35.DeepModel.Network.LayerSource.sourceA_coe_original,
    `Paper35.DeepModel.Network.LayerSource.sourceD_eq_original,
    `Paper35.DeepModel.Network.LayerSource.sourceD_le_covariance_sup,
    `Paper35.DeepModel.Network.ae_breakSet_network_subset,
    `Paper35.DeepModel.Network.lengthFactor_le_spectral,
    `Paper35.DeepModel.Network.ordinary_expectations_of_source,
    `Paper35.DeepModel.Network.source_network_length_bound_original,
    `Paper35.DeepModel.Network.source_network_switch_bound_original,
    `Paper35.DistributionFree.heterogeneous_bound,
    `Paper35.DistributionFree.weighted_covariance,
    `Paper35.DistributionFree.weighted_visibility,
    `Paper35.GaussianAnisotropic.normalizedVelocity_sq,
    `Paper35.GaussianIndependent.anisotropic_supremum,
    `Paper35.GaussianIndependent.covarianceMax_eigenvector_of_dimension,
    `Paper35.GaussianIndependent.eigenvalue_le_covarianceMax,
    `Paper35.GaussianIndependent.expectedDensity_le_anisotropic,
    `Paper35.GaussianIndependent.expectedDensity_le_isotropic,
    `Paper35.GaussianIndependent.isotropic_universal_coefficient_iff,
    `Paper35.GaussianLayer.Layer.source_curve_length_bound,
    `Paper35.GaussianLift.Model.sampleLaw_eq_map,
    `Paper35.GaussianLift.jointlyGaussian_interval_count_lt_whole,
    `Paper35.GaussianLift.jointlyGaussian_interval_supremum_7_8,
    `Paper35.GaussianLift.jointlyGaussian_polyline_arccos,
    `Paper35.GaussianLift.jointlyGaussian_segment_arccos,
    `Paper35.GaussianLift.jointlyGaussian_spherical_length,
    `Paper35.GaussianLift.jointlyGaussian_whole_line_7_8,
    `Paper35.GaussianLift.psi_probe_absolutelyContinuous,
    `Paper35.GaussianMarked.ClassicalCroftonLaw,
    `Paper35.GaussianMarked.ClassicalCroftonRegularityLaw,
    `Paper35.GaussianMarked.ae_spherical_endpoints_nonzero,
    `Paper35.GaussianMarked.gaussian_segment_expectedSwitchCount,
    `Paper35.GaussianMarked.gaussian_upper_envelope_all_dimensions,
    `Paper35.GaussianMarked.marked_coefficient_eq_gaussianRankCoefficient,
    `Paper35.GaussianMarked.marked_pair_crofton,
    `Paper35.GaussianMarked.normalized_segment_variation,
    `Paper35.GaussianMarked.spherical_endpoints_null,
    `Paper35.GaussianMomentTail.gaussianLengthCorrection_theta_log,
    `Paper35.GaussianMomentTail.gaussianLengthCorrection_upper_unconditional,
    `Paper35.GaussianNetwork.Model.curve_length_bound,
    `Paper35.GaussianNetwork.Model.length_propagation,
    `Paper35.GaussianNetwork.Model.ordinary_expectations,
    `Paper35.GaussianNetwork.Model.switch_propagation,
    `Paper35.GaussianRankFamily.Family.eventual_lower_bounds,
    `Paper35.GaussianRankFamily.Family.eventual_upper_bounds,
    `Paper35.GaussianRankFamily.Family.uniform_factors_isBigO,
    `Paper35.GaussianRankFamily.Family.uniform_factors_isTheta,
    `Paper35.GaussianSharpness.gaussian_exists_optimal_shrinking_direction,
    `Paper35.GaussianUnitDirectional.expectedCount_le_directional,
    `Paper35.GaussianWinner.GaussianUnit.winner_secondMoment_domination,
    `Paper35.GaussianWinner.GaussianUnit.winner_secondMoment_standard,
    `Paper35.GaussianWinner.independentMarking,
    `Paper35.Gini.sharp_coefficient,
    `Paper35.Gini.sharp_gini_iid,
    `Paper35.Gini.uniform_iid_gini_equality,
    `Paper35.Heterogeneous.common_reference_covariance,
    `Paper35.HeterogeneousSharpness.commonReference_coefficient_optimal,
    `Paper35.HeterogeneousSharpness.expectedDensity_tendsto_two,
    `Paper35.MaximizerChanges.ae_count_eq_index_and_region_changes,
    `Paper35.MaximizerChanges.indexChangeAt_iff_activeSwitch,
    `Paper35.MaximizerChanges.regionChangeAt_iff_activeSwitch,
    `Paper35.ParallelChanges.ae_jointSwitchCount_eq_tupleChangeCount,
    `Paper35.ParallelChanges.corollary_2_7_tuple,
    `Paper35.PlanarPolytope.expected_vertices_two,
    `Paper35.PlanarPolytope.integrable_perimeter,
    `Paper35.PlanarPolytope.planar_gaussian_polytope_identities,
    `Paper35.RandomCount.measurable_randomProbeSwitchCount,
    `Paper35.RandomProbes.parallel_covariance_bound,
    `Paper35.RandomProbes.randomProbe_covariance_bound,
    `Paper35.RankAsymptotics.gaussianRankCoefficient_leading,
    `Paper35.RankAsymptotics.gaussianRankCoefficient_second_order,
    `Paper35.RankBounds.gaussianMaxMean_quantile_bounds,
    `Paper35.RankBounds.gaussianQuantile_spec,
    `Paper35.Sharpness.origin_visibility_equality,
    `Paper35.Sharpness.sharp_expectedDensity_limit,
    `Paper35.Sharpness.uniformWeights_coordinate_density,
    `Paper35.Sharpness.uniformWeights_coordinates_iid,
    `Paper35.Source.CrossingRegularity.ae_all_pairs_regular,
    `Paper35.Source.CrossingRegularity.ae_no_triple_ties_closed,
    `Paper35.Source.CrossingRegularity.ae_switchSet_finite,
    `Paper35.Source.ExactCrossing.heterogeneous_crossing_identity,
    `Paper35.Source.ExactCrossing.iid_crossing_identity,
    `Paper35.Source.WeightedModel.covarianceMatrix_apply_of_constant,
    `Paper35.Source.WeightedModel.matrixLambdaMax_covarianceMatrix,
    `Paper35.SourceSupremum.full_admissible_supremum,
    `Paper35.SourceSupremum.universal_rank_linear_coefficient_iff,
    `Paper35.SourceTheorems.corollary_2_5_sharp_family,
    `Paper35.SourceTheorems.corollary_2_5_universal_optimal,
    `Paper35.SourceTheorems.corollary_2_5_upper,
    `Paper35.SourceTheorems.corollary_2_7_parallel,
    `Paper35.SourceTheorems.corollary_2_7_random,
    `Paper35.SourceTheorems.theorem_2_3_lambdaMax,
    `Paper35.SourceTheorems.theorem_2_3_spectral,
    `Paper35.VisibilityKernel.visibilityLemmaClaim,
    `Paper35.VisibilityKernel.weighted_visibility,
    `Paper35.VisibleCrossing.aemeasurable_pairSwitchCount,
    `Paper35.gaussianMaxMean_strictMono,
    `Paper35.gaussianMaxMean_strict_concavity,
    `Paper35.switchCount_rank_one]
  let mut rows : Array Json := #[]
  for name in names do
    let some ci := env.find? name
      | throwError "Coverage target missing from current environment: {name}"
    let ty ← liftTermElabM do Meta.ppExpr ci.type
    rows := rows.push <| Json.mkObj [
      ("name", toJson name.toString),
      ("is_theorem", toJson ci.isTheorem),
      ("universes", toJson (ci.levelParams.map Name.toString)),
      ("type", toJson ty.pretty)]
  liftIO <| IO.FS.writeFile "Verification/full-contract-types.json"
    ((toJson rows).pretty ++ "\n")
  logInfo m!"Exported {rows.size} coverage declaration types; not a Comparator pass."
