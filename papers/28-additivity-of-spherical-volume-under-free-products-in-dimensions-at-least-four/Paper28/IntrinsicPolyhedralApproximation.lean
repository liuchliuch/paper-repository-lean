import Paper28.SphericalAtlasBiLipschitz
import Paper28.MassSharpPolyhedralApproximation
import Paper28.SimplicialCurrentComparison

/-! Intrinsic spherical results with the geometric bi-Lipschitz bounds
constructed internally. The remaining parameters are actual finite
triangulation/chart data, the exact defining cell-path metric, standard
cell nondegeneracy and disclosed generic current/calculus foundations. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter Set CategoryTheory
open scoped Topology
variable {V Idx : Type} [Fintype V] [DecidableEq V] [Fintype Idx]
  {d : ℕ} {K : FiniteEuclideanComplex (EuclideanAmbient d)}
  (B : FullSubcomplexBarycentricAtlas K V Idx) {Y : Type} [metricY : MetricSpace Y]
  (C : FullSubcomplexSphericalCharts B Y) (Metric : SphericalCellPathMetricInput C)
  (hQ : CellVertexIndependence C) (y₀ : Y)

abbrev IntrinsicSphericalCurrentData := SphericalAtlasCurrentData.{0,0} B C y₀
  (sphericalForwardConstant C Metric y₀) (sphericalInverseConstant C Metric hQ)
  (sphericalForwardConstant_lipschitz C Metric y₀) (sphericalInverseConstant_lipschitz C Metric hQ)

theorem intrinsic_mass_sharp_spherical_polyhedral_approximation
    (hB : Function.Injective B.vertex) (D : IntrinsicSphericalCurrentData B C Metric hQ y₀)
    (A : LipschitzSimplexIntegrationInput metricY D.spherical)
    (hTangent : EuclideanAffineSupportTangentInput D.euclidean D.tangent)
    (hFaith : CurrentMassFaithfulnessInput D.spherical) (hCB : CauchyBinetInput)
    (Sub : EuclideanPolyhedralCellSubdivisionInput D.euclidean D.simplex)
    (F : SimplexPushforwardCompatibilityInput D.euclidean D.simplex D.spherical A (atlasRetractionDomain B)
      (atlasSphericalMap B C.homeomorph y₀) (atlasRetractionDomain_isOpen B)
      (atlasSphericalMap_near_lipschitz_intrinsic C Metric y₀) D.push)
    {k : ℕ} (Z : D.spherical.Current (k+1)) (hZ : D.spherical.boundary k Z = 0) :
    ∃ Zi : ℕ → D.spherical.Current (k+1), ∃ Wi : ℕ → D.spherical.Current (k+2),
      (∀ i, Zi i ∈ nondegenerateGeodesicCurrents A (k+1)) ∧
      (∀ i, D.spherical.boundary k (Zi i) = 0) ∧
      (∀ i, Z-Zi i = D.spherical.boundary (k+1) (Wi i)) ∧
      Tendsto (fun i => D.spherical.mass (Wi i)) atTop (𝓝 0) ∧
      Tendsto (fun i => D.spherical.mass (Zi i)) atTop (𝓝 (D.spherical.mass Z)) :=
  mass_sharp_spherical_polyhedral_approximation B C hB y₀
    (sphericalForwardConstant C Metric y₀) (sphericalInverseConstant C Metric hQ)
    (sphericalForwardConstant_lipschitz C Metric y₀) (sphericalInverseConstant_lipschitz C Metric hQ)
    D A hTangent hFaith hCB Sub F Z hZ

include B C Metric hQ y₀ in
theorem intrinsic_spherical_comparison_hypotheses :
    CompleteSpace Y ∧ AdmitsLocallyStrongLipschitzContractions Y :=
  spherical_atlas_comparison_hypotheses B C
    (sphericalForwardConstant C Metric y₀) (sphericalInverseConstant C Metric hQ)
    (sphericalForwardConstant_lipschitz C Metric y₀) (sphericalInverseConstant_lipschitz C Metric hQ)

def intrinsicCanonicalCurrentChainMap
    {J : CompactIntegralCurrentAlgebraInput.{0,0} Y metricY}
    (A : LipschitzSimplexIntegrationInput metricY J) :
    finiteSimplicialChainComplex K ⟶ compactCurrentChainComplex J :=
  canonicalSimplicialCurrentChainMap C.homeomorph (sphericalForwardConstant C Metric y₀)
    (sphericalForwardConstant_lipschitz C Metric y₀) A

include hQ in
theorem intrinsic_prescribed_simplicial_filling
    (J : CompactIntegralCurrentAlgebraInput.{0,0} Y metricY)
    (A : LipschitzSimplexIntegrationInput metricY J)
    (RS : LipschitzCurrentHomologyComparisonInput J A)
    (SS : SimplicialSingularHomologyComparisonInput)
    {k : ℕ} (z : finiteSimplicialChains K (k+1)) (hz : finiteSimplicialBoundary k z = 0)
    (hBounds : ∃ D : J.Current (k+2), J.boundary (k+1) D =
      (intrinsicCanonicalCurrentChainMap B C Metric y₀ A).f (k+1) z) :
    ∃ Q : finiteSimplicialChains K (k+2), finiteSimplicialBoundary (k+1) Q = z :=
  spherical_prescribed_simplicial_filling B C
    (sphericalForwardConstant C Metric y₀) (sphericalInverseConstant C Metric hQ)
    (sphericalForwardConstant_lipschitz C Metric y₀) (sphericalInverseConstant_lipschitz C Metric hQ)
    J A RS SS z hz hBounds

end Paper28
