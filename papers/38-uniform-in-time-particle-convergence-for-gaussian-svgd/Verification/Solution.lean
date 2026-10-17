import Verification.Statements

noncomputable section
open MeasureTheory Matrix
open scoped MatrixOrder ENNReal NNReal
namespace Paper38.Checked

theorem mobility_bilinear : Contracts.MobilityBilinear := by
  intro d μ a a' S B B' hS hB hB'
  exact Mobility.bilinear_identity μ S a a' B B' hS hB hB'

theorem mobility_strict : Contracts.MobilityStrict := by
  intro d μ a S B hS hB
  exact Mobility.quadratic_eq_zero_iff μ S a B hS hB

theorem covariance_rank : Contracts.CovarianceRank := by
  intro N d x
  exact Empirical.rank_covariance_le_all x

theorem covariance_span : Contracts.CovarianceSpan := by
  intro N d hN x
  exact Empirical.covariance_posDef_iff_affineSpan hN x

theorem endpoint_necessary : Contracts.EndpointNecessary := by
  intro N d hN x h
  exact Empirical.dimension_add_one_le_of_posDef hN x h

theorem density_affine_span : Contracts.DensityAffineSpan := by
  intro d N μ hprob hdensity hN
  letI := hprob
  exact GaussianFullRank.ae_affineSpan_eq_top hdensity (by simpa using hN)

theorem particle_moment_closure : Contracts.ParticleMomentClosure := by
  intro N d hN X t m Γ hΓ hX
  exact MomentClosure.projected_particle_moment_closure hN X t m Γ hΓ hX

theorem standardized_residual : Contracts.StandardizedResidual := by
  intro N d hN x hS
  exact Standardization.principal_standardized_identity_and_bound hN x hS

theorem gaussian_mean_second_moment : Contracts.GaussianMeanSecondMoment := by
  intro N d hN
  exact GaussianStatistics.sampleMean_secondMoment hN

theorem affine_transport : Contracts.AffineTransport := by
  intro d μ ν hμ hν m B a b ha hb
  letI := hμ
  letI := hν
  exact Transport.affine_two_sided μ ν m B a b ha hb

theorem finite_shape_floor : Contracts.FiniteShapeFloor := by
  intro N d x ν hprob hnonatomic
  letI := hprob
  letI := hnonatomic
  exact Transport.empirical_w2sq_pos x ν

theorem physical_time_countability : Contracts.PhysicalTimeCountability := by
  intro f hf
  exact RandomSupremum.timeSup_eq_rationalSup hf

theorem rate_dominates_mean : Contracts.RateDominatesMean :=
  Model.inv_sampleSize_le_rate

theorem scalar_counterexample : Contracts.ScalarCounterexample :=
  ScalarCounterexample.proposition_8_1

theorem cosine_hessian : Contracts.CosineHessian := by
  intro ε hε hε' x
  simpa only [Cosine.second_deriv_potential] using (Cosine.source_hessian_bounds hε hε' x).2

theorem cosine_optimum : Contracts.CosineOptimum := by
  intro ε hε hε'
  have hε1 : ε < 1 := lt_of_le_of_lt hε' (by norm_num)
  simpa only [Cosine.varianceEquation, Cosine.attenuation] using
    Cosine.unique_global_minimum hε.le hε1

theorem density_positive_covariance : Contracts.DensityPositiveCovariance := by
  intro d N μ hprob hdensity hN
  letI := hprob
  exact ModelBridges.ae_empiricalCovariance_posDef hdensity hN

theorem gaussian_synchronous : Contracts.GaussianSynchronous := by
  intro d μ ν A B
  exact GaussianCoupling.gaussian_w2sq_le μ ν A B

theorem quadratic_triangle : Contracts.QuadraticTriangle := by
  intro d μ ν ξ hμ hν hξ
  letI := hμ
  letI := hν
  letI := hξ
  exact Transport.w2sq_triangle μ ν ξ

end Paper38.Checked
