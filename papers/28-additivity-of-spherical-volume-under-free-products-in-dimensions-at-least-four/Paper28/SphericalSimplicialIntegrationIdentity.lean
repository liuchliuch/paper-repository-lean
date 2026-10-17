import Paper28.SimplicialCurrentComparison
import Paper28.AffineSimplexPushforward
import Paper28.SphericalAtlasCurrentTransport

/-! Canonical simplicial-to-Lipschitz-to-current integration is exactly
the actual push of affine integration. This identification is proved on
actual generators and extended to finite integer chains. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open CategoryTheory Set
open scoped Simplicial
variable {d : ℕ} {K : FiniteEuclideanComplex (EuclideanAmbient d)}

theorem orderedSimplexHull_subset_carrier {k : ℕ} (σ : OrderedComplexSimplex K k) :
    convexHull ℝ (Set.range (orderedSimplexVertices σ)) ⊆ K.complex.space :=
  (convexHull_mono (fun _ hx => by
    obtain ⟨i,rfl⟩ := hx
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)).trans
      (K.complex.convexHull_subset_space σ.face)

theorem canonicalSimplicialCurrent_of {Y : Type} [metricY : MetricSpace Y]
    (h : K.complex.space → Y) (L : NNReal) (hL : LipschitzWith L h)
    {J : CompactIntegralCurrentAlgebraInput.{0,0} Y metricY}
    (A : LipschitzSimplexIntegrationInput metricY J) {k : ℕ} (σ : NondegenerateComplexSimplex K k) :
    (canonicalSimplicialCurrentChainMap h L hL A).f k (FreeAbelianGroup.of σ) =
      A.integration k ((simplicialToLipschitzSingular h L hL).app (Opposite.op ⦋k⦌) σ.val) := by
  change lipschitzCurrentIntegration A k (FreeAbelianGroup.map
    ((simplicialToLipschitzSingular h L hL).app (Opposite.op ⦋k⦌))
    (nondegenerateChainInclusion k (FreeAbelianGroup.of σ))) = _
  rw [nondegenerateChainInclusion,FreeAbelianGroup.map_of_apply,FreeAbelianGroup.map_of_apply,
    lipschitzCurrentIntegration,FreeAbelianGroup.lift_apply_of]

section Atlas
variable {V Idx : Type*} [Fintype V] [DecidableEq V] [Fintype Idx]
  {B : FullSubcomplexBarycentricAtlas K V Idx} {Y : Type} [metricY : MetricSpace Y]
  (C : FullSubcomplexSphericalCharts B Y) (y₀ : Y) (L : NNReal) (hL : LipschitzWith L C.homeomorph)
  (hf : LipschitzNearSet inferInstance metricY (atlasSphericalMap B C.homeomorph y₀) (atlasRetractionDomain B))

theorem simplicial_parameter_eq_neighborhood_affine {k : ℕ} (σ : OrderedComplexSimplex K k) :
    (simplicialToLipschitzSingular C.homeomorph L hL).app (Opposite.op ⦋k⦌) σ =
      neighborhoodAffineSimplex (atlasRetractionDomain B) (atlasSphericalMap B C.homeomorph y₀) hf
        (orderedSimplexVertices σ) ((orderedSimplexHull_subset_carrier σ).trans (atlasRetractionDomain_contains B)) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  exact (atlasSphericalMap_on_carrier B C.homeomorph y₀ (orderedSimplexParameter σ t)).symm

variable (I : CompactIntegralCurrentAlgebraInput.{0,0} (EuclideanAmbient d) inferInstance)
  (S : EuclideanSimplexIntegrationInput d I)
  (J : CompactIntegralCurrentAlgebraInput.{0,0} Y metricY)
  (A : LipschitzSimplexIntegrationInput metricY J)
  (P : NeighborhoodCurrentPushforwardInput inferInstance metricY I J (atlasRetractionDomain B)
    (atlasSphericalMap B C.homeomorph y₀) (atlasRetractionDomain_isOpen B) hf)
  (F : SimplexPushforwardCompatibilityInput I S J A (atlasRetractionDomain B)
    (atlasSphericalMap B C.homeomorph y₀) (atlasRetractionDomain_isOpen B) hf P)

include F in
theorem canonicalSimplicialCurrent_of_eq_push {k : ℕ} (σ : NondegenerateComplexSimplex K k) :
    (canonicalSimplicialCurrentChainMap C.homeomorph L hL A).f k (FreeAbelianGroup.of σ) =
      P.push k ⟨S.integration k (orderedSimplexVertices σ.val),(S.support_subset k _).trans
        ((orderedSimplexHull_subset_carrier σ.val).trans (atlasRetractionDomain_contains B))⟩ := by
  rw [canonicalSimplicialCurrent_of,F.push_affine_simplex k (orderedSimplexVertices σ.val)
    ((orderedSimplexHull_subset_carrier σ.val).trans (atlasRetractionDomain_contains B)),
    simplicial_parameter_eq_neighborhood_affine C y₀ L hL hf σ.val]

include F in
theorem canonicalSimplicialCurrent_eq_push {k : ℕ} (z : finiteSimplicialChains K k) :
    (canonicalSimplicialCurrentChainMap C.homeomorph L hL A).f k z =
      P.push k (orderedIntegrationSupported S (atlasRetractionDomain B) (atlasRetractionDomain_contains B) k
        (nondegenerateChainInclusion k z)) := by
  refine FreeAbelianGroup.induction_on z ?_ ?_ ?_ ?_
  · simp only [map_zero]
  · intro σ
    rw [nondegenerateChainInclusion,FreeAbelianGroup.map_of_apply]
    have he : orderedIntegrationSupported S (atlasRetractionDomain B)
        (atlasRetractionDomain_contains B) k (FreeAbelianGroup.of σ.val) =
        ⟨S.integration k (orderedSimplexVertices σ.val),(S.support_subset k _).trans
          ((orderedSimplexHull_subset_carrier σ.val).trans (atlasRetractionDomain_contains B))⟩ := by
      apply Subtype.ext
      change orderedIntegration S k (FreeAbelianGroup.of σ.val) = _
      exact FreeAbelianGroup.lift_apply_of _ _
    rw [he]
    exact canonicalSimplicialCurrent_of_eq_push C y₀ L hL hf I S J A P F σ
  · intro σ ih
    simpa only [map_neg] using congrArg Neg.neg ih
  · intro a b ha hb
    simpa only [map_add] using congrArg₂ (fun x y => x+y) ha hb

theorem atlasInverseMap_sphericalMap_on_carrier (x : EuclideanAmbient d) (hx : x ∈ K.complex.space) :
    atlasInverseMap C.homeomorph (atlasSphericalMap B C.homeomorph y₀ x) = x := by
  have he := atlasSphericalMap_on_carrier B C.homeomorph y₀ (⟨x,hx⟩ : K.complex.space)
  rw [he]
  exact congrArg Subtype.val (C.homeomorph.symm_apply_apply ⟨x,hx⟩)

end Atlas
end Paper28
