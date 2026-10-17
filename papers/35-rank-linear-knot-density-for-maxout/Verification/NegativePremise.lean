import Verification.Statements

namespace Verification.Certificate

theorem rank_one : False → Verification.Specification.rank_one := by
  intro _
  exact Paper35.switchCount_rank_one

theorem pair_decomposition : Verification.Specification.pair_decomposition := by
  exact Paper35.switchCount_eq_sum_pairSwitchSet

theorem opposite_mass : Verification.Specification.opposite_mass := by
  exact Paper35.Visibility.opposite_mass_bound

theorem layer_cake : Verification.Specification.layer_cake := by
  exact Paper35.Visibility.gini_layer_cake

theorem gini_bound : Verification.Specification.gini_bound := by
  exact Paper35.Gini.sharp_gini_iid

theorem atomic_bias : Verification.Specification.atomic_bias := by
  exact Paper35.Counterexamples.atomic_bias_expected_density

theorem dependent_bias : Verification.Specification.dependent_bias := by
  exact Paper35.Counterexamples.dependent_bias_expected_density

theorem binary_count : Verification.Specification.binary_count := by
  exact Paper35.Counterexamples.switchCount_binaryScores

theorem positive_rescaling : Verification.Specification.positive_rescaling := by
  exact Paper35.Gaussian.switchCount_affine_on

theorem normalized_speed : Verification.Specification.normalized_speed := by
  exact Paper35.Gaussian.normalizedVelocity_norm_sq

theorem rank_increase : Verification.Specification.rank_increase := by
  exact Paper35.gaussianMaxMean_strictMono

theorem rank_concavity : Verification.Specification.rank_concavity := by
  exact Paper35.gaussianMaxMean_strict_concavity

theorem length_recursion : Verification.Specification.length_recursion := by
  exact Paper35.Deep.length_recursion

theorem switch_recursion : Verification.Specification.switch_recursion := by
  exact Paper35.Deep.switch_recursion

theorem psd_domination : Verification.Specification.psd_domination := by
  exact Paper35.Deep.activeSecondMomentMatrix_domination

theorem source_atomic_bias : Verification.Specification.source_atomic_bias := by
  exact Paper35.Counterexamples.atomic_bias_source_density

theorem source_dependent_bias : Verification.Specification.source_dependent_bias := by
  exact Paper35.Counterexamples.proposition_5_2

theorem tilt_probability : Verification.Specification.tilt_probability := by
  exact Paper35.Visibility.tiltedLaw_isProbability

theorem integrated_visibility_split : Verification.Specification.integrated_visibility_split := by
  exact Paper35.Visibility.integrated_opposite_mass_bound

theorem gini_uniform_equality : Verification.Specification.gini_uniform_equality := by
  exact Paper35.Gini.uniform_iid_gini_equality

theorem gini_sharpness : Verification.Specification.gini_sharpness := by
  exact Paper35.Gini.sharp_coefficient

theorem gaussian_rank_two : Verification.Specification.gaussian_rank_two := by
  exact Paper35.gaussianRankCoefficient_two

theorem gaussian_rank_linear : Verification.Specification.gaussian_rank_linear := by
  exact Paper35.gaussianRankCoefficient_le_rank_linear

theorem tilted_directional_gini : Verification.Specification.tilted_directional_gini := by
  exact Paper35.Source.WeightedModel.directionalGini_le_sqrt_projectedVariance

theorem cdf_power : Verification.Specification.cdf_power := by
  exact Paper35.CDFPower.lintegral_cdf_mass_pow_mul_density

theorem gaussian_half_rank : Verification.Specification.gaussian_half_rank := by
  exact Paper35.gaussianRankCoefficient_le_half_rank

theorem gaussian_uniform_sharpness : Verification.Specification.gaussian_uniform_sharpness := by
  exact Paper35.gaussianRankCoefficient_uniform_bound_iff

end Verification.Certificate
