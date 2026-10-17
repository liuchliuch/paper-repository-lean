import Paper28.SphericalAtlasGeometry
import Paper28.SharpNeighborhoodApproximation

/-! The actual spherical barycentric realization and constructed retraction
instantiate the sharp approximation theorem. No derivatives, round lift
identities, incident Jacobian values or sharp estimates are hypotheses. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter Set
open scoped Topology
universe w v

set_option maxHeartbeats 600000 in
theorem spherical_atlas_sharp_approximation
    {V Idx : Type*} [Fintype V] [DecidableEq V] [Fintype Idx]
    {d k : ℕ} {K : FiniteEuclideanComplex (EuclideanAmbient d)}
    (B : FullSubcomplexBarycentricAtlas K V Idx) {Y : Type w} [metricY : MetricSpace Y]
    (C : FullSubcomplexSphericalCharts B Y) (y₀ : Y)
    (Lh : NNReal) (hh : LipschitzWith Lh C.homeomorph)
    (I : CompactIntegralCurrentAlgebraInput.{0,v} (EuclideanAmbient d) inferInstance)
    (S : EuclideanSimplexIntegrationInput d I) (E : EuclideanDeformationInput d I S)
    (R : EuclideanCurrentTangentInput d I)
    (hRes : StrictPolarMeasureContinuityInput.{0}) (hPort : UpperPortmanteauInput.{0})
    (J : CompactIntegralCurrentAlgebraInput.{w,v} Y metricY)
    (P : NeighborhoodCurrentPushforwardInput inferInstance metricY I J (atlasRetractionDomain B)
      (atlasSphericalMap B C.homeomorph y₀) (atlasRetractionDomain_isOpen B)
      (atlasSphericalMap_near_lipschitz B C.homeomorph y₀ Lh hh))
    (A : EuclideanCurrentAreaInput metricY I R J (atlasRetractionDomain B)
      (atlasSphericalMap B C.homeomorph y₀) (atlasRetractionDomain_isOpen B)
      (atlasSphericalMap_near_lipschitz B C.homeomorph y₀ Lh hh) P)
    (T : supportedCurrents I (atlasRetractionDomain B) (k+1))
    (hTK : I.support T.val ⊆ K.complex.space) (hCycle : I.boundary k T.val = 0) :
    ∃ Qi : ℕ → supportedCurrents I (atlasRetractionDomain B) (k+1),
    ∃ Si : ℕ → supportedCurrents I (atlasRetractionDomain B) (k+2),
      (∀ i, (Qi i).val ∈ euclideanPolyhedralCurrents S (k+1)) ∧
      (∀ i, I.boundary k (Qi i).val = 0) ∧
      (∀ i, J.boundary k (P.push (k+1) (Qi i)) = 0) ∧
      (∀ i, P.push (k+1) T-P.push (k+1) (Qi i) = J.boundary (k+1) (P.push (k+2) (Si i))) ∧
      Tendsto (fun i => J.mass (P.push (k+2) (Si i))) atTop (𝓝 0) ∧
      Tendsto (fun i => J.mass (P.push (k+1) (Qi i))) atTop (𝓝 (J.mass (P.push (k+1) T))) := by
  classical
  apply sharp_neighborhood_approximation metricY I S E R hRes hPort J
    (atlasRetractionDomain B) (atlasSphericalMap B C.homeomorph y₀)
    (atlasRetractionDomain_isOpen B) (atlasSphericalMap_near_lipschitz B C.homeomorph y₀ Lh hh)
    P A T hCycle ((atlasSphericalMap_injective_on_carrier B C.homeomorph y₀ C.homeomorph.injective).mono hTK)
    C.dimension (atlasCell B) atlasCell_isClosed atlasCells_cover
    (fun j => atlasSphereLift B (C.vertex j) j) (atlasSphereDerivativeMatrix C)
    (atlasSphereDerivativeMatrix_continuous C) (realizationFaces B) (realizationStratum B)
    realizationStrata_cover
    (fun j _ x hx => atlasSphereLift_unit C j x hx.1)
    (atlasSphereLift_round_stratum C y₀)
    (fun j _ x hx => atlasSphereLift_hasFDerivAt C j x hx.1)

end Paper28
