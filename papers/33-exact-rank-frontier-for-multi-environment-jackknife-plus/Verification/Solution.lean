import Verification.Statements

/- Positive proofs refer to real production declarations. Official comparison has not been run. -/
namespace Paper33.Checked

theorem s3_exact_failure : Contracts.s3_exact_failure := by
  unfold Contracts.s3_exact_failure
  exact @MEJF.MainResults.exact_failure_law

theorem s3_finite_validity : Contracts.s3_finite_validity := by
  unfold Contracts.s3_finite_validity
  exact @MEJF.MainResults.finite_validity_criterion

theorem s3_zero_floor : Contracts.s3_zero_floor := by
  unfold Contracts.s3_zero_floor
  exact @MEJF.MainResults.zero_floor_impossible

theorem s3_complete_phase : Contracts.s3_complete_phase := by
  unfold Contracts.s3_complete_phase
  exact @MEJF.MainResults.complete_failure_iff

theorem s3_one_outer : Contracts.s3_one_outer := by
  unfold Contracts.s3_one_outer
  exact @MEJF.MainResults.one_outer

theorem s3_one_inner : Contracts.s3_one_inner := by
  unfold Contracts.s3_one_inner
  exact @MEJF.RankFrontier.failureRate_low_inner

theorem s3_zero_rank_axes : Contracts.s3_zero_rank_axes := by
  unfold Contracts.s3_zero_rank_axes
  exact @MEJF.ExtendedRule.gamma_zero

theorem s3_pareto_card : Contracts.s3_pareto_card := by
  unfold Contracts.s3_pareto_card
  exact @MEJF.ActualPareto.ranks_card

theorem s3_inner_ceil : Contracts.s3_inner_ceil := by
  unfold Contracts.s3_inner_ceil
  exact @MEJF.RankFrontier.innerTop_eq_real_ceil

theorem s3_outer_enumeration : Contracts.s3_outer_enumeration := by
  unfold Contracts.s3_outer_enumeration
  exact @MEJF.RankFrontier.pareto_iff_outer

theorem s3_inner_enumeration : Contracts.s3_inner_enumeration := by
  unfold Contracts.s3_inner_enumeration
  exact @MEJF.RankFrontier.pareto_iff_inner

theorem s3_linear_enumeration : Contracts.s3_linear_enumeration := by
  unfold Contracts.s3_linear_enumeration
  exact @MEJF.RankAlgorithm.enumerate_correct

theorem s3_linear_cost : Contracts.s3_linear_cost := by
  unfold Contracts.s3_linear_cost
  exact @MEJF.RankAlgorithm.enumerate_ops_le

theorem s3_actual_asymptotic : Contracts.s3_actual_asymptotic := by
  unfold Contracts.s3_actual_asymptotic
  exact @MEJF.ActualAsymptotic.gamma_asymptotic_min

theorem s3_limiting_budget : Contracts.s3_limiting_budget := by
  unfold Contracts.s3_limiting_budget
  exact @MEJF.ActualAsymptotic.limiting_validity_iff

theorem s3_limiting_complete : Contracts.s3_limiting_complete := by
  unfold Contracts.s3_limiting_complete
  exact @MEJF.ActualAsymptotic.limiting_complete_failure_iff

theorem s3_limiting_pareto : Contracts.s3_limiting_pareto := by
  unfold Contracts.s3_limiting_pareto
  exact @MEJF.LimitingFrontier.pareto_iff

theorem s7_factor_two_asymptotic : Contracts.s7_factor_two_asymptotic := by
  unfold Contracts.s7_factor_two_asymptotic
  exact @MEJF.LimitingFrontier.factor_two_invalid

theorem s4_actual_nonempty : Contracts.s4_actual_nonempty := by
  unfold Contracts.s4_actual_nonempty
  exact @MEJF.DeterministicUpper.learner_aggregate_nonempty

theorem s4_actual_degree : Contracts.s4_actual_degree := by
  unfold Contracts.s4_actual_degree
  exact @MEJF.DeterministicUpper.learner_failure_forces_high_outdegree

theorem s4_oriented_count : Contracts.s4_oriented_count := by
  unfold Contracts.s4_oriented_count
  exact @MEJF.GraphBound.highVertices_card_le

theorem s5_extremal_graph : Contracts.s5_extremal_graph := by
  unfold Contracts.s5_extremal_graph
  exact @MEJF.ExtremalGraph.exists_extremal_oriented_graph

theorem s5_incidence_realization : Contracts.s5_incidence_realization := by
  unfold Contracts.s5_incidence_realization
  exact @MEJF.Incidence.realize_frontier

theorem s5_quantitative_tie_removal : Contracts.s5_quantitative_tie_removal := by
  unfold Contracts.s5_quantitative_tie_removal
  exact @MEJF.TieFreeSharpness.exists_quantitative_tieFree_model

theorem s5_tie_free_attainment : Contracts.s5_tie_free_attainment := by
  unfold Contracts.s5_tie_free_attainment
  exact @MEJF.TieFreeSharpness.exists_tieFree_attaining_model

theorem s6_heterogeneous_sup : Contracts.s6_heterogeneous_sup := by
  unfold Contracts.s6_heterogeneous_sup
  exact @MEJF.HeterogeneousProbability.gamma_eq

theorem s6_heterogeneous_attainment : Contracts.s6_heterogeneous_attainment := by
  unfold Contracts.s6_heterogeneous_attainment
  exact @MEJF.HeterogeneousProbability.exists_attaining_model

theorem s6_conditional_sizes : Contracts.s6_conditional_sizes := by
  unfold Contracts.s6_conditional_sizes
  exact @MEJF.HeterogeneousProbability.conditional_failure_le

theorem s6_random_size_expectation : Contracts.s6_random_size_expectation := by
  unfold Contracts.s6_random_size_expectation
  exact @MEJF.HeterogeneousProbability.failure_probability_le_expectation

theorem s6_hall_sorted_cell : Contracts.s6_hall_sorted_cell := by
  unfold Contracts.s6_hall_sorted_cell
  exact @MEJF.HeterogeneousFrontier.supported_card_iff_sortedCell

theorem s6_true_max_support : Contracts.s6_true_max_support := by
  unfold Contracts.s6_true_max_support
  exact @MEJF.HeterogeneousFrontier.maximumSupported_eq_sStar

theorem s6_quadratic_algorithm : Contracts.s6_quadratic_algorithm := by
  unfold Contracts.s6_quadratic_algorithm
  exact @MEJF.HeterogeneousAlgorithm.computeAfterSorting_correct

theorem s6_quadratic_cost : Contracts.s6_quadratic_cost := by
  unfold Contracts.s6_quadratic_cost
  exact @MEJF.HeterogeneousAlgorithm.computeAfterSorting_ops_le

theorem s6_published_sort_composition : Contracts.s6_published_sort_composition := by
  unfold Contracts.s6_published_sort_composition
  exact @MEJF.HeterogeneousSortingInput.computeWithSorter_correct

theorem s6_sort_and_scan_cost : Contracts.s6_sort_and_scan_cost := by
  unfold Contracts.s6_sort_and_scan_cost
  exact @MEJF.HeterogeneousSortingInput.computeWithSorter_uniform_bound

theorem s6_heterogeneous_tie_free_law : Contracts.s6_heterogeneous_tie_free_law := by
  unfold Contracts.s6_heterogeneous_tie_free_law
  exact @MEJF.HeterogeneousTieFree.source_exists_tieFree_minimax_law

theorem s6_asymmetric_sup : Contracts.s6_asymmetric_sup := by
  unfold Contracts.s6_asymmetric_sup
  exact @MEJF.Asymmetric.gamma_eq

theorem s6_asymmetric_symmetric_value : Contracts.s6_asymmetric_symmetric_value := by
  unfold Contracts.s6_asymmetric_symmetric_value
  exact @MEJF.Asymmetric.gamma_eq_symmetric

theorem s6_symmetric_containment : Contracts.s6_symmetric_containment := by
  unfold Contracts.s6_symmetric_containment
  exact @MEJF.Asymmetric.symmetric_max_interval_subset

theorem s6_random_rank_sup : Contracts.s6_random_rank_sup := by
  unfold Contracts.s6_random_rank_sup
  exact @MEJF.RandomizedProbability.finiteRankGammaPi_eq

theorem s6_random_rank_attainment : Contracts.s6_random_rank_attainment := by
  unfold Contracts.s6_random_rank_attainment
  exact @MEJF.RandomizedProbability.exists_attaining_model

theorem s6_random_rank_tie_free : Contracts.s6_random_rank_tie_free := by
  unfold Contracts.s6_random_rank_tie_free
  exact @MEJF.RandomizedTieFree.exists_tieFree_attaining_law

theorem s6_landau_dp : Contracts.s6_landau_dp := by
  unfold Contracts.s6_landau_dp
  exact @MEJF.RankDP.dp_computes_gamma

theorem s6_dp_quartic_cost : Contracts.s6_dp_quartic_cost := by
  unfold Contracts.s6_dp_quartic_cost
  exact @MEJF.RankDP.complete_program_cost

theorem s6_nonconvexification : Contracts.s6_nonconvexification := by
  unfold Contracts.s6_nonconvexification
  exact @MEJF.RandomizedProbability.nonconvexification_actual

theorem s6_expanded_probability : Contracts.s6_expanded_probability := by
  unfold Contracts.s6_expanded_probability
  exact @MEJF.StabilityProbability.expanded_failure_probability_le

theorem s6_expanded_full_sup : Contracts.s6_expanded_full_sup := by
  unfold Contracts.s6_expanded_full_sup
  exact @MEJF.StabilityExtended.gamma_eq

theorem s6_stable_maximal_pair : Contracts.s6_stable_maximal_pair := by
  unfold Contracts.s6_stable_maximal_pair
  exact @MEJF.StabilityFrontier.maximal_valid_pair_iff

theorem s6_stable_asymptotic_rectangle : Contracts.s6_stable_asymptotic_rectangle := by
  unfold Contracts.s6_stable_asymptotic_rectangle
  exact @MEJF.StabilityAsymptotic.actual_limiting_rectangle

theorem s6_unexpanded_stable_sup : Contracts.s6_unexpanded_stable_sup := by
  unfold Contracts.s6_unexpanded_stable_sup
  exact @MEJF.Scaling.stableUnexpandedGamma_eq

theorem s6_swap_upper : Contracts.s6_swap_upper := by
  unfold Contracts.s6_swap_upper
  exact @MEJF.SwapRobustness.source_failure_probability_le

theorem s6_swap_attainment : Contracts.s6_swap_attainment := by
  unfold Contracts.s6_swap_attainment
  exact @MEJF.SwapRobustness.source_swap_sharpness

theorem s7_factor_two_failure : Contracts.s7_factor_two_failure := by
  unfold Contracts.s7_factor_two_failure
  exact @MEJF.MainResults.ordinary_factor_two_failure

theorem s7_full_efficiency : Contracts.s7_full_efficiency := by
  unfold Contracts.s7_full_efficiency
  exact @MEJF.EfficiencyCompletion.proposition_7_2

theorem s7_every_noiseless_realization : Contracts.s7_every_noiseless_realization := by
  unfold Contracts.s7_every_noiseless_realization
  exact @MEJF.EfficiencyCompletion.noiseless_every_permutation

theorem s7_every_supported_noise : Contracts.s7_every_supported_noise := by
  unfold Contracts.s7_every_supported_noise
  exact @MEJF.EfficiencyCompletion.noisy_every_supported_sample

theorem s7_strict_containment : Contracts.s7_strict_containment := by
  unfold Contracts.s7_strict_containment
  exact @MEJF.Efficiency.strict_containment

theorem s6_all_covariates_containment : Contracts.s6_all_covariates_containment := by
  unfold Contracts.s6_all_covariates_containment
  exact @MEJF.AsymmetricFrontier.symmetric_interval_subset

theorem s6_asymmetric_pareto_symmetric : Contracts.s6_asymmetric_pareto_symmetric := by
  unfold Contracts.s6_asymmetric_pareto_symmetric
  exact @MEJF.AsymmetricFrontier.outer_pareto_symmetric

theorem s3_floor_cells : Contracts.s3_floor_cells := by
  unfold Contracts.s3_floor_cells
  exact @MEJF.RankCells.shifted_rank_cell

theorem s3_pathwise_monotonicity : Contracts.s3_pathwise_monotonicity := by
  unfold Contracts.s3_pathwise_monotonicity
  exact @MEJF.RankCells.intervalAt_antitone

theorem s3_pathwise_cell_constancy : Contracts.s3_pathwise_cell_constancy := by
  unfold Contracts.s3_pathwise_cell_constancy
  exact @MEJF.RankCells.interval_constant_on_cell

theorem s7_factor_two_continuous_levels : Contracts.s7_factor_two_continuous_levels := by
  unfold Contracts.s7_factor_two_continuous_levels
  exact @MEJF.RankCells.ordinary_factor_two_at_levels

theorem s2_coherent_seed_minimax : Contracts.s2_coherent_seed_minimax := by
  unfold Contracts.s2_coherent_seed_minimax
  exact @MEJF.CoherentSeed.randomizedGamma_eq_finiteRankGamma

theorem s2_coherent_seed_joint_measurable : Contracts.s2_coherent_seed_joint_measurable := by
  unfold Contracts.s2_coherent_seed_joint_measurable
  exact @MEJF.CoherentSeed.measurableSet_failure

theorem s2_ae_admissible_seed_bound : Contracts.s2_ae_admissible_seed_bound := by
  unfold Contracts.s2_ae_admissible_seed_bound
  exact @MEJF.CoherentSeed.ae_admissible_failure_probability_le

theorem s2_ae_admissible_seed_minimax : Contracts.s2_ae_admissible_seed_minimax := by
  unfold Contracts.s2_ae_admissible_seed_minimax
  exact @MEJF.CoherentSeed.aeAdmissibleGamma_eq_finiteRankGamma

end Paper33.Checked
