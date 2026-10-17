import Paper28.SphericalCycleApproximation
import Paper28.SphericalPolyhedralPushforward

/-! Own mass-sharp polyhedral approximation on the actual spherical
realization. Starting with the original integral cycle, all approximants
are proved to be finite integer sums of nondegenerate spherical geodesic
simplex currents. No approximation or sharp mass estimate is an input.
The universal source realization/refinement connection remains separate. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter Set
open scoped Topology

theorem mass_sharp_spherical_polyhedral_approximation
    {V Idx : Type} [Fintype V] [DecidableEq V] [Fintype Idx]
    {d k : ℕ} {K : FiniteEuclideanComplex (EuclideanAmbient d)}
    (B : FullSubcomplexBarycentricAtlas K V Idx) {Y : Type} [metricY : MetricSpace Y]
    (C : FullSubcomplexSphericalCharts B Y) (hB : Function.Injective B.vertex) (y₀ : Y)
    (L M : NNReal) (hL : LipschitzWith L C.homeomorph) (hM : LipschitzWith M C.homeomorph.symm)
    (D : SphericalAtlasCurrentData.{0,0} B C y₀ L M hL hM)
    (A : LipschitzSimplexIntegrationInput metricY D.spherical)
    (hTangent : EuclideanAffineSupportTangentInput D.euclidean D.tangent)
    (hFaith : CurrentMassFaithfulnessInput D.spherical) (hCB : CauchyBinetInput)
    (Sub : EuclideanPolyhedralCellSubdivisionInput D.euclidean D.simplex)
    (F : SimplexPushforwardCompatibilityInput D.euclidean D.simplex D.spherical A (atlasRetractionDomain B)
      (atlasSphericalMap B C.homeomorph y₀) (atlasRetractionDomain_isOpen B)
      (atlasSphericalMap_near_lipschitz B C.homeomorph y₀ L hL) D.push)
    (Z : D.spherical.Current (k+1)) (hZ : D.spherical.boundary k Z = 0) :
    ∃ Zi : ℕ → D.spherical.Current (k+1), ∃ Wi : ℕ → D.spherical.Current (k+2),
      (∀ i, Zi i ∈ nondegenerateGeodesicCurrents A (k+1)) ∧
      (∀ i, D.spherical.boundary k (Zi i) = 0) ∧
      (∀ i, Z-Zi i = D.spherical.boundary (k+1) (Wi i)) ∧
      Tendsto (fun i => D.spherical.mass (Wi i)) atTop (𝓝 0) ∧
      Tendsto (fun i => D.spherical.mass (Zi i)) atTop (𝓝 (D.spherical.mass Z)) := by
  obtain ⟨Zi,Wi,hCycles,hHom,hFill,hMass,hPreimage⟩ := actual_spherical_cycle_approximation
    B C y₀ L M hL hM D Z hZ
  refine ⟨Zi,Wi,?_,hCycles,hHom,hFill,hMass⟩
  intro i
  obtain ⟨Q,hQ,hPush⟩ := hPreimage i
  rw [← hPush]
  exact spherical_polyhedral_pushforward C hB y₀ D.euclidean D.simplex D.tangent hTangent D.spherical A
    hFaith hCB (atlasSphericalMap_near_lipschitz B C.homeomorph y₀ L hL) D.push D.area F Sub
    (Nat.zero_lt_succ k) Q hQ

end Paper28
