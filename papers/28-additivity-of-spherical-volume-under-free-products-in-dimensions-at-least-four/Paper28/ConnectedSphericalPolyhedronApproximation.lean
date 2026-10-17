import Paper28.SphericalPolyhedronCurrentFoundations
import Paper28.SphericalFiniteRefinementInput

/-! The source finite spherical triangulation is independent of all
proof-specific neighborhood choices. Classical geometric realization and
common subdivision are the only additional geometric foundations. Actual
sharp approximation and prescribed source-cell polyhedral filling follow
from the native constructions and estimates. This file treats one component. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open CategoryTheory Filter Set
open scoped Topology
variable {d : ℕ} {K : FiniteEuclideanComplex (EuclideanAmbient d)}
  {Y : Type} [metricY : MetricSpace Y] (S : FiniteSphericalTriangulation K Y)
  {e : ℕ} {K₁ : FiniteEuclideanComplex (EuclideanAmbient e)}
  (N : SphericalNeighborhoodRealization S K₁) (y₀ : Y)
  {J : CompactIntegralCurrentAlgebraInput.{0,0} Y metricY}
  (A : LipschitzSimplexIntegrationInput metricY J)
  (D : SphericalPolyhedronCurrentFoundations N y₀ J A)

include D in
theorem source_canonical_integration_mem_polyhedral {k : ℕ} (hk : 0 < k)
    (z : finiteSimplicialChains K₁ k) :
    (intrinsicCanonicalCurrentChainMap N.atlas N.charts N.metric y₀ A).f k z ∈
      cellwiseSphericalPolyhedralCurrents S A k := by
  change (canonicalSimplicialCurrentChainMap N.charts.homeomorph
    (sphericalForwardConstant N.charts N.metric y₀)
    (sphericalForwardConstant_lipschitz N.charts N.metric y₀) A).f k z ∈ _
  rw [canonicalSimplicialCurrent_eq_push N.charts y₀ (sphericalForwardConstant N.charts N.metric y₀)
    (sphericalForwardConstant_lipschitz N.charts N.metric y₀) (neighborhoodSphericalMap_lipschitz N y₀)
    D.euclidean D.simplex J A D.push D.simplexCompatibility]
  exact realization_polyhedral_push_cellwise S N y₀ (neighborhoodSphericalMap_lipschitz N y₀)
    D.euclidean D.simplex D.tangent D.affineTangents J A D.massFaithfulness D.cauchyBinet
    D.push D.area D.simplexCompatibility D.subdivision hk _
    (orderedIntegration_mem_polyhedral D.simplex k (nondegenerateChainInclusion k z))

include D in
theorem source_realization_sharp_cycle_approximation {k : ℕ}
    (Z : J.Current (k+1)) (hZ : J.boundary k Z = 0) :
    ∃ Zi : ℕ → J.Current (k+1), ∃ Wi : ℕ → J.Current (k+2),
      (∀ i, Zi i ∈ cellwiseSphericalPolyhedralCurrents S A (k+1)) ∧
      (∀ i, J.boundary k (Zi i) = 0) ∧
      (∀ i, Z-Zi i = J.boundary (k+1) (Wi i)) ∧
      Tendsto (fun i => J.mass (Wi i)) atTop (𝓝 0) ∧
      Tendsto (fun i => J.mass (Zi i)) atTop (𝓝 (J.mass Z)) := by
  obtain ⟨Zi,Wi,hCycles,hHom,hFill,hMass,hPreimage⟩ := actual_spherical_cycle_approximation
    N.atlas N.charts y₀ (sphericalForwardConstant N.charts N.metric y₀)
    (sphericalInverseConstant N.charts N.metric N.nondegenerate)
    (sphericalForwardConstant_lipschitz N.charts N.metric y₀)
    (sphericalInverseConstant_lipschitz N.charts N.metric N.nondegenerate) D.toData Z hZ
  refine ⟨Zi,Wi,?_,hCycles,hHom,hFill,hMass⟩
  intro i
  obtain ⟨Q,hQ,hPush⟩ := hPreimage i
  rw [← hPush]
  exact realization_polyhedral_push_cellwise S N y₀ (neighborhoodSphericalMap_lipschitz N y₀)
    D.euclidean D.simplex D.tangent D.affineTangents J A D.massFaithfulness D.cauchyBinet
    D.push D.area D.simplexCompatibility D.subdivision (Nat.zero_lt_succ k) Q hQ

variable {N D}

theorem connected_spherical_polyhedron_sharp_approximation
    (PL : SphericalFullNeighborhoodInput) (hMetric : IntrinsicSphericalTriangulationMetric S)
    (Foundations : ∀ {e : ℕ} (K₁ : FiniteEuclideanComplex (EuclideanAmbient e))
      (N : SphericalNeighborhoodRealization S K₁), Nonempty (SphericalPolyhedronCurrentFoundations N y₀ J A))
    {k : ℕ} (Z : J.Current (k+1)) (hZ : J.boundary k Z = 0) :
    ∃ Zi : ℕ → J.Current (k+1), ∃ Wi : ℕ → J.Current (k+2),
      (∀ i, Zi i ∈ cellwiseSphericalPolyhedralCurrents S A (k+1)) ∧
      (∀ i, J.boundary k (Zi i) = 0) ∧
      (∀ i, Z-Zi i = J.boundary (k+1) (Wi i)) ∧
      Tendsto (fun i => J.mass (Wi i)) atTop (𝓝 0) ∧
      Tendsto (fun i => J.mass (Zi i)) atTop (𝓝 (J.mass Z)) := by
  obtain ⟨e,K₁,N⟩ := PL.realization S hMetric
  obtain ⟨N⟩ := N
  obtain ⟨D⟩ := Foundations K₁ N
  exact source_realization_sharp_cycle_approximation S N y₀ A D Z hZ

theorem connected_spherical_polyhedron_prescribed_filling
    (Ref : SphericalFiniteRefinementInput) (hMetric : IntrinsicSphericalTriangulationMetric S)
    (Foundations : ∀ {e : ℕ} (K₁ : FiniteEuclideanComplex (EuclideanAmbient e))
      (N : SphericalNeighborhoodRealization S K₁), Nonempty (SphericalPolyhedronCurrentFoundations N y₀ J A))
    (RS : LipschitzCurrentHomologyComparisonInput J A) (SS : SimplicialSingularHomologyComparisonInput)
    {k : ℕ} (Z : J.Current (k+1)) (hPoly : Z ∈ cellwiseSphericalPolyhedralCurrents S A (k+1))
    (hZ : J.boundary k Z = 0) (hBounds : ∃ W : J.Current (k+2), J.boundary (k+1) W = Z) :
    ∃ Q : J.Current (k+2), Q ∈ cellwiseSphericalPolyhedralCurrents S A (k+2) ∧
      J.boundary (k+1) Q = Z := by
  obtain ⟨e,K₁,N,z,hRep⟩ := cellwise_polyhedral_simplicial_representation S Ref hMetric y₀ A Z hPoly
  obtain ⟨D⟩ := Foundations K₁ N
  obtain ⟨q,_,_,hb⟩ := intrinsic_prescribed_polyhedral_filling N.atlas N.charts N.metric N.nondegenerate y₀
    D.toData A D.simplexCompatibility D.separation D.reverseFunctoriality N.vertex_injective
    D.affineTangents D.massFaithfulness D.cauchyBinet D.subdivision RS SS Z hZ z hRep hBounds
  exact ⟨(intrinsicCanonicalCurrentChainMap N.atlas N.charts N.metric y₀ A).f (k+2) q,
    source_canonical_integration_mem_polyhedral S N y₀ A D (by omega) q,hb⟩

end Paper28
