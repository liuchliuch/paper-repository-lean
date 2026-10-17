import Paper28.IntrinsicPolyhedralApproximation
import Paper28.SphericalSimplicialIntegrationInjective

/-! Exact prescribed polyhedral filling on the actual intrinsic spherical
realization. The simplicial cycle condition is derived from the current
cycle condition. The resulting actual current has precisely the given
boundary and is a finite integer sum of nondegenerate spherical simplices. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open CategoryTheory Set
variable {V Idx : Type} [Fintype V] [DecidableEq V] [Fintype Idx]
  {d : ℕ} {K : FiniteEuclideanComplex (EuclideanAmbient d)}
  (B : FullSubcomplexBarycentricAtlas K V Idx) {Y : Type} [metricY : MetricSpace Y]
  (C : FullSubcomplexSphericalCharts B Y) (Metric : SphericalCellPathMetricInput C)
  (hQ : CellVertexIndependence C) (y₀ : Y)
  (D : IntrinsicSphericalCurrentData B C Metric hQ y₀)
  (A : LipschitzSimplexIntegrationInput metricY D.spherical)
  (F : SimplexPushforwardCompatibilityInput D.euclidean D.simplex D.spherical A (atlasRetractionDomain B)
    (atlasSphericalMap B C.homeomorph y₀) (atlasRetractionDomain_isOpen B)
    (atlasSphericalMap_near_lipschitz_intrinsic C Metric y₀) D.push)

include F in
theorem intrinsic_canonical_integration_mem_polyhedral
    (hB : Function.Injective B.vertex)
    (hTangent : EuclideanAffineSupportTangentInput D.euclidean D.tangent)
    (hFaith : CurrentMassFaithfulnessInput D.spherical) (hCB : CauchyBinetInput)
    (Sub : EuclideanPolyhedralCellSubdivisionInput D.euclidean D.simplex)
    {k : ℕ} (hk : 0 < k) (z : finiteSimplicialChains K k) :
    (intrinsicCanonicalCurrentChainMap B C Metric y₀ A).f k z ∈ nondegenerateGeodesicCurrents A k := by
  change (canonicalSimplicialCurrentChainMap C.homeomorph (sphericalForwardConstant C Metric y₀)
    (sphericalForwardConstant_lipschitz C Metric y₀) A).f k z ∈ _
  rw [canonicalSimplicialCurrent_eq_push C y₀ (sphericalForwardConstant C Metric y₀)
    (sphericalForwardConstant_lipschitz C Metric y₀) (atlasSphericalMap_near_lipschitz_intrinsic C Metric y₀)
    D.euclidean D.simplex D.spherical A D.push F]
  exact spherical_polyhedral_pushforward C hB y₀ D.euclidean D.simplex D.tangent hTangent
    D.spherical A hFaith hCB (atlasSphericalMap_near_lipschitz_intrinsic C Metric y₀) D.push D.area F Sub hk
    _ (orderedIntegration_mem_polyhedral D.simplex k (nondegenerateChainInclusion k z))

variable (Sep : EuclideanSimplexSeparationInput D.euclidean D.simplex)
  (Back : TwoStagePushforwardFunctorialityInput inferInstance metricY D.euclidean D.spherical
    (atlasRetractionDomain B) univ (atlasSphericalMap B C.homeomorph y₀) (atlasInverseMap C.homeomorph)
    (atlasRetractionDomain_isOpen B) isOpen_univ
    (atlasSphericalMap_near_lipschitz_intrinsic C Metric y₀)
    (atlasInverseMap_near_lipschitz C.homeomorph (sphericalInverseConstant C Metric hQ)
      (sphericalInverseConstant_lipschitz C Metric hQ)) D.push D.pull)

include F Sep Back in
theorem intrinsic_prescribed_polyhedral_filling
    (hB : Function.Injective B.vertex)
    (hTangent : EuclideanAffineSupportTangentInput D.euclidean D.tangent)
    (hFaith : CurrentMassFaithfulnessInput D.spherical) (hCB : CauchyBinetInput)
    (Sub : EuclideanPolyhedralCellSubdivisionInput D.euclidean D.simplex)
    (RS : LipschitzCurrentHomologyComparisonInput D.spherical A)
    (SS : SimplicialSingularHomologyComparisonInput)
    {k : ℕ} (Z : D.spherical.Current (k+1)) (hZ : D.spherical.boundary k Z = 0)
    (z : finiteSimplicialChains K (k+1))
    (hRep : (intrinsicCanonicalCurrentChainMap B C Metric y₀ A).f (k+1) z = Z)
    (hBounds : ∃ W : D.spherical.Current (k+2), D.spherical.boundary (k+1) W = Z) :
    ∃ q : finiteSimplicialChains K (k+2), finiteSimplicialBoundary (k+1) q = z ∧
      (intrinsicCanonicalCurrentChainMap B C Metric y₀ A).f (k+2) q ∈ nondegenerateGeodesicCurrents A (k+2) ∧
      D.spherical.boundary (k+1) ((intrinsicCanonicalCurrentChainMap B C Metric y₀ A).f (k+2) q) = Z := by
  have hz : finiteSimplicialBoundary k z = 0 :=
    spherical_current_cycle_implies_simplicial_cycle C y₀ (sphericalForwardConstant C Metric y₀)
      (sphericalForwardConstant_lipschitz C Metric y₀) (atlasSphericalMap_near_lipschitz_intrinsic C Metric y₀)
      (atlasInverseMap_near_lipschitz C.homeomorph (sphericalInverseConstant C Metric hQ)
        (sphericalInverseConstant_lipschitz C Metric hQ))
      D.euclidean D.simplex Sep D.spherical A D.push F D.pull Back z
      (by change D.spherical.boundary k ((intrinsicCanonicalCurrentChainMap B C Metric y₀ A).f (k+1) z) = 0
          rw [hRep]; exact hZ)
  obtain ⟨q,hq⟩ := intrinsic_prescribed_simplicial_filling B C Metric hQ y₀ D.spherical A RS SS z hz
    (by rw [hRep]; exact hBounds)
  refine ⟨q,hq,intrinsic_canonical_integration_mem_polyhedral B C Metric hQ y₀ D A F hB hTangent
    hFaith hCB Sub (by omega) q,?_⟩
  have he := congrArg (fun g => g q) ((intrinsicCanonicalCurrentChainMap B C Metric y₀ A).comm (k+2) (k+1))
  have hd : (finiteSimplicialChainComplex K).d (k+2) (k+1) =
      AddCommGrpCat.ofHom (finiteSimplicialBoundary (k+1)) := ChainComplex.of_d _ _ _ (k+1)
  rw [compactCurrentChainComplex_d,hd] at he
  exact he.trans ((congrArg ((intrinsicCanonicalCurrentChainMap B C Metric y₀ A).f (k+1)) hq).trans hRep)

end Paper28
