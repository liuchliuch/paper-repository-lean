import Paper28.SphericalAtlasApproximation
import Paper28.SphericalAtlasCurrentTransport

/-! Current-level approximation of the original actual spherical cycle,
with exact homology and sharp mass. The convenience bundle below only
collects already disclosed generic foundational inputs on the exact spaces;
it adds no approximation, deformation, sharp mass or filling hypothesis.
The spherical-polyhedral membership step after subdivision is separate. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter Set
open scoped Topology
universe w v

structure SphericalAtlasCurrentData
    {V Idx : Type*} [Fintype V] [DecidableEq V] [Fintype Idx]
    {d : ℕ} {K : FiniteEuclideanComplex (EuclideanAmbient d)}
    (B : FullSubcomplexBarycentricAtlas K V Idx) {Y : Type w} [metricY : MetricSpace Y]
    (C : FullSubcomplexSphericalCharts B Y) (y₀ : Y)
    (L M : NNReal) (hL : LipschitzWith L C.homeomorph) (hM : LipschitzWith M C.homeomorph.symm) where
  euclidean : CompactIntegralCurrentAlgebraInput.{0,v} (EuclideanAmbient d) inferInstance
  spherical : CompactIntegralCurrentAlgebraInput.{w,v} Y metricY
  simplex : EuclideanSimplexIntegrationInput d euclidean
  deformation : EuclideanDeformationInput d euclidean simplex
  tangent : EuclideanCurrentTangentInput d euclidean
  strictPolar : StrictPolarMeasureContinuityInput.{0}
  portmanteau : UpperPortmanteauInput.{0}
  pull : NeighborhoodCurrentPushforwardInput metricY inferInstance spherical euclidean Set.univ
    (atlasInverseMap C.homeomorph) isOpen_univ (atlasInverseMap_near_lipschitz C.homeomorph M hM)
  push : NeighborhoodCurrentPushforwardInput inferInstance metricY euclidean spherical (atlasRetractionDomain B)
    (atlasSphericalMap B C.homeomorph y₀) (atlasRetractionDomain_isOpen B)
    (atlasSphericalMap_near_lipschitz B C.homeomorph y₀ L hL)
  area : EuclideanCurrentAreaInput metricY euclidean tangent spherical (atlasRetractionDomain B)
    (atlasSphericalMap B C.homeomorph y₀) (atlasRetractionDomain_isOpen B)
    (atlasSphericalMap_near_lipschitz B C.homeomorph y₀ L hL) push
  functoriality : TwoStagePushforwardFunctorialityInput metricY inferInstance spherical euclidean Set.univ
    (atlasRetractionDomain B) (atlasInverseMap C.homeomorph) (atlasSphericalMap B C.homeomorph y₀)
    isOpen_univ (atlasRetractionDomain_isOpen B) (atlasInverseMap_near_lipschitz C.homeomorph M hM)
    (atlasSphericalMap_near_lipschitz B C.homeomorph y₀ L hL) pull push

set_option maxHeartbeats 600000 in
theorem actual_spherical_cycle_approximation
    {V Idx : Type*} [Fintype V] [DecidableEq V] [Fintype Idx]
    {d k : ℕ} {K : FiniteEuclideanComplex (EuclideanAmbient d)}
    (B : FullSubcomplexBarycentricAtlas K V Idx) {Y : Type w} [metricY : MetricSpace Y]
    (C : FullSubcomplexSphericalCharts B Y) (y₀ : Y)
    (L M : NNReal) (hL : LipschitzWith L C.homeomorph) (hM : LipschitzWith M C.homeomorph.symm)
    (D : SphericalAtlasCurrentData.{w,v} B C y₀ L M hL hM)
    (Z : D.spherical.Current (k+1)) (hZ : D.spherical.boundary k Z = 0) :
    ∃ Zi : ℕ → D.spherical.Current (k+1), ∃ Wi : ℕ → D.spherical.Current (k+2),
      (∀ i, D.spherical.boundary k (Zi i) = 0) ∧
      (∀ i, Z-Zi i = D.spherical.boundary (k+1) (Wi i)) ∧
      Tendsto (fun i => D.spherical.mass (Wi i)) atTop (𝓝 0) ∧
      Tendsto (fun i => D.spherical.mass (Zi i)) atTop (𝓝 (D.spherical.mass Z)) ∧
      (∀ i, ∃ Q : supportedCurrents D.euclidean (atlasRetractionDomain B) (k+1),
        Q.val ∈ euclideanPolyhedralCurrents D.simplex (k+1) ∧ D.push.push (k+1) Q = Zi i) := by
  let T := atlasPullback B C.homeomorph M hM D.euclidean D.spherical D.pull Z
  have hT := atlasPullback_cycle B C.homeomorph M hM D.euclidean D.spherical D.pull Z hZ
  have hBack : D.push.push (k+1) T = Z :=
    atlasPullback_push_identity B C.homeomorph M hM D.euclidean D.spherical D.pull y₀
      (atlasSphericalMap_near_lipschitz B C.homeomorph y₀ L hL) D.push D.functoriality Z
  obtain ⟨Qi,Si,hPoly,_,hCycles,hHom,hFill,hMass⟩ := spherical_atlas_sharp_approximation
    B C y₀ L hL D.euclidean D.simplex D.deformation D.tangent D.strictPolar D.portmanteau D.spherical
    D.push D.area T (atlasPullback_support C.homeomorph M hM D.euclidean D.spherical D.pull Z) hT
  rw [hBack] at hMass
  refine ⟨(fun i => D.push.push (k+1) (Qi i)),(fun i => D.push.push (k+2) (Si i)),hCycles,?_,hFill,hMass,?_⟩
  · intro i
    rw [← hBack]
    exact hHom i
  · exact fun i => ⟨Qi i,hPoly i,rfl⟩

end Paper28
