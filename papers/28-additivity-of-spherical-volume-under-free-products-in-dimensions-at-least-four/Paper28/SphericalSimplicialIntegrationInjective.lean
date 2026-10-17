import Paper28.SphericalSimplicialIntegrationIdentity
import Paper28.SimplicialIntegrationSeparation

/-! Actual spherical simplicial integration is injective: pull back its
actual affine push, use the proved retraction identity on the carrier,
and then use Euclidean test-current separation. A closed integrated
current therefore comes from an actual simplicial cycle. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open CategoryTheory Set
variable {V Idx : Type} [Fintype V] [DecidableEq V] [Fintype Idx]
  {d : ℕ} {K : FiniteEuclideanComplex (EuclideanAmbient d)}
  {B : FullSubcomplexBarycentricAtlas K V Idx} {Y : Type} [metricY : MetricSpace Y]
  (C : FullSubcomplexSphericalCharts B Y) (y₀ : Y) (L : NNReal) (hL : LipschitzWith L C.homeomorph)
  (hf : LipschitzNearSet inferInstance metricY (atlasSphericalMap B C.homeomorph y₀) (atlasRetractionDomain B))
  (hq : LipschitzNearSet metricY inferInstance (atlasInverseMap C.homeomorph) univ)
  (I : CompactIntegralCurrentAlgebraInput.{0,0} (EuclideanAmbient d) inferInstance)
  (S : EuclideanSimplexIntegrationInput d I)
  (Sep : EuclideanSimplexSeparationInput I S)
  (J : CompactIntegralCurrentAlgebraInput.{0,0} Y metricY)
  (A : LipschitzSimplexIntegrationInput metricY J)
  (P : NeighborhoodCurrentPushforwardInput inferInstance metricY I J (atlasRetractionDomain B)
    (atlasSphericalMap B C.homeomorph y₀) (atlasRetractionDomain_isOpen B) hf)
  (F : SimplexPushforwardCompatibilityInput I S J A (atlasRetractionDomain B)
    (atlasSphericalMap B C.homeomorph y₀) (atlasRetractionDomain_isOpen B) hf P)
  (Pull : NeighborhoodCurrentPushforwardInput metricY inferInstance J I univ
    (atlasInverseMap C.homeomorph) isOpen_univ hq)
  (Back : TwoStagePushforwardFunctorialityInput inferInstance metricY I J
    (atlasRetractionDomain B) univ (atlasSphericalMap B C.homeomorph y₀) (atlasInverseMap C.homeomorph)
    (atlasRetractionDomain_isOpen B) isOpen_univ hf hq P Pull)

include Sep F Back in
theorem spherical_canonical_integration_injective (k : ℕ) :
    Function.Injective ((canonicalSimplicialCurrentChainMap C.homeomorph L hL A).f k) := by
  change Function.Injective ((canonicalSimplicialCurrentChainMap C.homeomorph L hL A).f k).hom
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  apply finiteSimplicialIntegration_injective I S Sep K k
  rw [map_zero]
  let Cz := orderedIntegrationSupported S (atlasRetractionDomain B) (atlasRetractionDomain_contains B) k
    (nondegenerateChainInclusion k z)
  have hPush : P.push k Cz = 0 :=
    (canonicalSimplicialCurrent_eq_push C y₀ L hL hf I S J A P F z).symm.trans hz
  have hBack := Back.composition_identity_on_support k Cz (subset_univ _) (by
    intro x hx
    exact atlasInverseMap_sphericalMap_on_carrier C y₀ x
      (orderedIntegration_support_carrier S k (nondegenerateChainInclusion k z) hx))
  have hLift : (⟨P.push k Cz,subset_univ _⟩ : supportedCurrents J univ k) = 0 := Subtype.ext hPush
  rw [hLift,map_zero] at hBack
  exact hBack.symm

include Sep F Back in
theorem spherical_current_cycle_implies_simplicial_cycle {k : ℕ}
    (z : finiteSimplicialChains K (k+1))
    (hz : J.boundary k ((canonicalSimplicialCurrentChainMap C.homeomorph L hL A).f (k+1) z) = 0) :
    finiteSimplicialBoundary k z = 0 := by
  apply spherical_canonical_integration_injective C y₀ L hL hf hq I S Sep J A P F Pull Back k
  rw [map_zero]
  have he := congrArg (fun g => g z)
    ((canonicalSimplicialCurrentChainMap C.homeomorph L hL A).comm (k+1) k)
  have hd : (finiteSimplicialChainComplex K).d (k+1) k =
      AddCommGrpCat.ofHom (finiteSimplicialBoundary k) := ChainComplex.of_d _ _ _ k
  rw [compactCurrentChainComplex_d,hd] at he
  exact he.symm.trans hz

end Paper28
