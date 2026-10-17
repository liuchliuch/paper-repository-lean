import Paper27.CompactCoefficient
import Paper27.CyclicLaurent
import Paper27.DegreeArithmetic
import Paper27.Geometry.ActionGluing
import Paper27.Geometry.ActualCyclicModels
import Paper27.Geometry.ActualDisjointObstruction
import Paper27.Geometry.ActualFormulaSixObstruction
import Paper27.Geometry.BranchGraphs
import Paper27.Geometry.CheckingBothProjections
import Paper27.Geometry.ClassicalInputs
import Paper27.Geometry.CoefficientGluing
import Paper27.Geometry.CommonComponents
import Paper27.Geometry.CommonRetractions
import Paper27.Geometry.ComponentAlternatives
import Paper27.Geometry.CoordinateCalculus
import Paper27.Geometry.CoordinateFiniteGerms
import Paper27.Geometry.CovectorGauges
import Paper27.Geometry.CurveBranchInputs
import Paper27.Geometry.CurveFamilies
import Paper27.Geometry.CurveMetricRigidity
import Paper27.Geometry.CyclicModel
import Paper27.Geometry.CyclicTransitions
import Paper27.Geometry.DifferentialRigidity
import Paper27.Geometry.DiscGraphExtension
import Paper27.Geometry.EmbeddedCurve
import Paper27.Geometry.EmbeddedFrames
import Paper27.Geometry.FactoredRetractionCoordinates
import Paper27.Geometry.Factorization
import Paper27.Geometry.FibrationBound
import Paper27.Geometry.FibreGeometry
import Paper27.Geometry.FiniteAnalyticGerm
import Paper27.Geometry.FiniteBranchAssembly
import Paper27.Geometry.FiniteGermNeighbourhood
import Paper27.Geometry.FixedAmbientBranchGraphs
import Paper27.Geometry.FormulaSixGeometry
import Paper27.Geometry.FormulaSixInvariantExtension
import Paper27.Geometry.IntrinsicDichotomy
import Paper27.Geometry.KodairaFibrations
import Paper27.Geometry.LeadingNormalTensor
import Paper27.Geometry.LineCocycles
import Paper27.Geometry.MeromorphicSplittingAverage
import Paper27.Geometry.MetricComparison
import Paper27.Geometry.MetricTangency
import Paper27.Geometry.NeighbourhoodSplittings
import Paper27.Geometry.NormalAtlasAction
import Paper27.Geometry.NormalAtlasRestriction
import Paper27.Geometry.NormalAtlasTensor
import Paper27.Geometry.NormalCorrection
import Paper27.Geometry.NormalDegreeInvariance
import Paper27.Geometry.NormalJets
import Paper27.Geometry.NormalQuotient
import Paper27.Geometry.NormalizationLocalization
import Paper27.Geometry.NormalizedBranchConstruction
import Paper27.Geometry.NormalizedDifferentials
import Paper27.Geometry.Objects
import Paper27.Geometry.Obstruction
import Paper27.Geometry.OriginalAveragingProof
import Paper27.Geometry.ProductCover
import Paper27.Geometry.PuncturedAverageInvariance
import Paper27.Geometry.PuncturedFormulaSix
import Paper27.Geometry.PuncturedNeighbourhoods
import Paper27.Geometry.PuncturedRotationCoordinates
import Paper27.Geometry.PuncturedSectionAverage
import Paper27.Geometry.PuncturedSectionRemovability
import Paper27.Geometry.PuncturedSplittingSections
import Paper27.Geometry.RamificationCovectors
import Paper27.Geometry.RamificationDichotomy
import Paper27.Geometry.RamificationDivisorOrder
import Paper27.Geometry.RamificationFamilies
import Paper27.Geometry.RamificationGeometry
import Paper27.Geometry.RamificationIndexConstancy
import Paper27.Geometry.RamificationSupport
import Paper27.Geometry.RetractionAtlas
import Paper27.Geometry.RetractionCoefficientHolomorphic
import Paper27.Geometry.RetractionCoordinateGerms
import Paper27.Geometry.RetractionFactorization
import Paper27.Geometry.RetractionNormalAtlasBridge
import Paper27.Geometry.RetractionNormalCoordinates
import Paper27.Geometry.SmoothCurveDecomposition
import Paper27.Geometry.TangentConnection
import Paper27.Geometry.TaylorGerms
import Paper27.Geometry.ThreePairNormalObstruction
import Paper27.Geometry.ThreeRetractionOrders
import Paper27.Geometry.UniformCyclicRestrictions
import Paper27.JetCalculation
import Paper27.LocalProjection
import Paper27.ProductCoverGroup
import Paper27.Splitting

/-!
P27: actual compact-complex geometry and the complete own relative derivation.

The main entry points are `ClassicalInputs.at_most_two` and
`ClassicalInputs.at_most_two_classes`. `at_most_two_kodaira` retains the
separate published hyperbolic-base theorem. `ClassicalInputs.ramification_geometry`
constructs Proposition 2.4 from the original maps. The actual Appendix and
original formula-(6) common-component arguments are both included.

Known unformalized classical theorems remain precise explicit universal
parameters in `ClassicalInputs`, the supplementary `AveragingInputs` and the
separately disclosed Kodaira/historical example inputs. No instance of these
external theories or unconditional proof of the paper is asserted here.

Verification challenges and invalid controls are outside this production
import closure. This final expanded root has not been aggregate-built or
kernel/axiom-audited and its new official Comparator contracts have not run,
as explicitly deferred by the user. See `VERIFICATION_DEFERRED.md`.
-/
