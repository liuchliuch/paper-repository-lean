import Paper28.CellwiseSphericalPushforward
import Paper28.IntrinsicPrescribedPolyhedralFilling

/-! A convenience bundle of the already disclosed generic foundations,
with the actual target current algebra fixed across different geometric
refinements. No paper-owned estimate or existence conclusion is a field. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
variable {d : ℕ} {K : FiniteEuclideanComplex (EuclideanAmbient d)}
  {Y : Type} [metricY : MetricSpace Y] {S : FiniteSphericalTriangulation K Y}
  {e : ℕ} {K₁ : FiniteEuclideanComplex (EuclideanAmbient e)}
  (N : SphericalNeighborhoodRealization S K₁) (y₀ : Y)
  (J : CompactIntegralCurrentAlgebraInput.{0,0} Y metricY)
  (A : LipschitzSimplexIntegrationInput metricY J)

abbrev neighborhoodSphericalMap := atlasSphericalMap N.atlas N.charts.homeomorph y₀
abbrev neighborhoodSphericalDomain := atlasRetractionDomain N.atlas
abbrev neighborhoodSphericalMap_lipschitz := atlasSphericalMap_near_lipschitz_intrinsic N.charts N.metric y₀
abbrev neighborhoodInverse_lipschitz := atlasInverseMap_near_lipschitz N.charts.homeomorph
  (sphericalInverseConstant N.charts N.metric N.nondegenerate)
  (sphericalInverseConstant_lipschitz N.charts N.metric N.nondegenerate)

structure SphericalPolyhedronCurrentFoundations where
  euclidean : CompactIntegralCurrentAlgebraInput.{0,0} (EuclideanAmbient e) inferInstance
  simplex : EuclideanSimplexIntegrationInput e euclidean
  deformation : EuclideanDeformationInput e euclidean simplex
  tangent : EuclideanCurrentTangentInput e euclidean
  strictPolar : StrictPolarMeasureContinuityInput.{0}
  portmanteau : UpperPortmanteauInput.{0}
  pull : NeighborhoodCurrentPushforwardInput metricY inferInstance J euclidean univ
    (atlasInverseMap N.charts.homeomorph) isOpen_univ (neighborhoodInverse_lipschitz N)
  push : NeighborhoodCurrentPushforwardInput inferInstance metricY euclidean J (neighborhoodSphericalDomain N)
    (neighborhoodSphericalMap N y₀) (atlasRetractionDomain_isOpen N.atlas)
    (neighborhoodSphericalMap_lipschitz N y₀)
  area : EuclideanCurrentAreaInput metricY euclidean tangent J (neighborhoodSphericalDomain N)
    (neighborhoodSphericalMap N y₀) (atlasRetractionDomain_isOpen N.atlas)
    (neighborhoodSphericalMap_lipschitz N y₀) push
  functoriality : TwoStagePushforwardFunctorialityInput metricY inferInstance J euclidean univ
    (neighborhoodSphericalDomain N) (atlasInverseMap N.charts.homeomorph) (neighborhoodSphericalMap N y₀)
    isOpen_univ (atlasRetractionDomain_isOpen N.atlas) (neighborhoodInverse_lipschitz N)
    (neighborhoodSphericalMap_lipschitz N y₀) pull push
  reverseFunctoriality : TwoStagePushforwardFunctorialityInput inferInstance metricY euclidean J
    (neighborhoodSphericalDomain N) univ (neighborhoodSphericalMap N y₀) (atlasInverseMap N.charts.homeomorph)
    (atlasRetractionDomain_isOpen N.atlas) isOpen_univ (neighborhoodSphericalMap_lipschitz N y₀)
    (neighborhoodInverse_lipschitz N) push pull
  simplexCompatibility : SimplexPushforwardCompatibilityInput euclidean simplex J A (neighborhoodSphericalDomain N)
    (neighborhoodSphericalMap N y₀) (atlasRetractionDomain_isOpen N.atlas)
    (neighborhoodSphericalMap_lipschitz N y₀) push
  affineTangents : EuclideanAffineSupportTangentInput euclidean tangent
  massFaithfulness : CurrentMassFaithfulnessInput J
  cauchyBinet : CauchyBinetInput
  subdivision : EuclideanPolyhedralCellSubdivisionInput euclidean simplex
  separation : EuclideanSimplexSeparationInput euclidean simplex

variable {N y₀ J A}

def SphericalPolyhedronCurrentFoundations.toData (D : SphericalPolyhedronCurrentFoundations N y₀ J A) :
    IntrinsicSphericalCurrentData N.atlas N.charts N.metric N.nondegenerate y₀ where
  euclidean := D.euclidean
  spherical := J
  simplex := D.simplex
  deformation := D.deformation
  tangent := D.tangent
  strictPolar := D.strictPolar
  portmanteau := D.portmanteau
  pull := D.pull
  push := D.push
  area := D.area
  functoriality := D.functoriality

end Paper28
