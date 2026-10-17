import Paper28.SimplicialSingularMap
import Paper28.LipschitzSimplexIntegration
import Paper28.NeighborhoodPushforwardInput
import Paper28.ProjectiveSimplexImages
import Paper28.SphericalAtlasGeometry

/-! Actual affine-simplex parameterization under a neighborhood map. The
only additional generic AK input is the defining compatibility of affine
integration, Lipschitz-simplex integration and canonical pushforward.
The normalized spherical parameter formula is proved locally. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
variable {d k : ℕ} {Y : Type} [metricY : MetricSpace Y]

def affineSimplexParameter (σ : AffineSimplexVertices d k) (t : stdSimplex ℝ (Fin (k+1))) :
    EuclideanAmbient d := ∑ i, t.val i • σ i

theorem affineSimplexParameter_lipschitz (σ : AffineSimplexVertices d k) :
    LipschitzWith ‖simplexBarycentricLinear σ‖₊ (affineSimplexParameter σ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [simplexBarycentricLinear_apply] using (simplexBarycentricLinear σ).lipschitz.dist_le_mul x.val y.val

theorem exists_lipschitz_affine_composition (U : Set (EuclideanAmbient d)) (f : EuclideanAmbient d → Y)
    (hf : LipschitzNearSet inferInstance metricY f U) (σ : AffineSimplexVertices d k)
    (hσ : convexHull ℝ (Set.range σ) ⊆ U) :
    ∃ L : NNReal, LipschitzWith L (fun t : stdSimplex ℝ (Fin (k+1)) => f (affineSimplexParameter σ t)) := by
  let N := convexHull ℝ (Set.range σ)
  have hN : IsCompact N := (Set.finite_range σ).isCompact_convexHull
  obtain ⟨L,hL⟩ := LipschitzNearSet.compact_restrict f U N hf hσ hN
  let F : stdSimplex ℝ (Fin (k+1)) → N := fun t =>
    ⟨affineSimplexParameter σ t,(affineSimplexPatch_eq_convexHull σ).subset ⟨t,rfl⟩⟩
  have hF : LipschitzWith ‖simplexBarycentricLinear σ‖₊ F := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact (affineSimplexParameter_lipschitz σ).dist_le_mul x y
  exact ⟨L*‖simplexBarycentricLinear σ‖₊,hL.comp hF⟩

def neighborhoodAffineSimplex (U : Set (EuclideanAmbient d)) (f : EuclideanAmbient d → Y)
    (hf : LipschitzNearSet inferInstance metricY f U) (σ : AffineSimplexVertices d k)
    (hσ : convexHull ℝ (Set.range σ) ⊆ U) : LipschitzSingularSimplex Y k :=
  ⟨⟨(fun t => f (affineSimplexParameter σ t)),
    (exists_lipschitz_affine_composition U f hf σ hσ).choose_spec.continuous⟩,
    exists_lipschitz_affine_composition U f hf σ hσ⟩

structure SimplexPushforwardCompatibilityInput
    (I : CompactIntegralCurrentAlgebraInput.{0,0} (EuclideanAmbient d) inferInstance)
    (S : EuclideanSimplexIntegrationInput d I)
    (J : CompactIntegralCurrentAlgebraInput.{0,0} Y metricY)
    (A : LipschitzSimplexIntegrationInput metricY J)
    (U : Set (EuclideanAmbient d)) (f : EuclideanAmbient d → Y) (hU : IsOpen U)
    (hf : LipschitzNearSet inferInstance metricY f U)
    (P : NeighborhoodCurrentPushforwardInput inferInstance metricY I J U f hU hf) : Prop where
  push_affine_simplex : ∀ k (σ : AffineSimplexVertices d k) (hσ : convexHull ℝ (Set.range σ) ⊆ U),
    P.push k ⟨S.integration k σ,(S.support_subset k σ).trans hσ⟩ =
      A.integration k (neighborhoodAffineSimplex U f hf σ hσ)

theorem neighborhoodAffineSimplex_projective_formula
    {V Idx : Type*} [Fintype V] [DecidableEq V] [Fintype Idx]
    {K : FiniteEuclideanComplex (EuclideanAmbient d)} {B : FullSubcomplexBarycentricAtlas K V Idx}
    (C : FullSubcomplexSphericalCharts B Y) (y₀ : Y)
    (hf : LipschitzNearSet inferInstance metricY (atlasSphericalMap B C.homeomorph y₀) (atlasRetractionDomain B))
    (j : Idx) (σ : AffineSimplexVertices d k)
    (hσ : convexHull ℝ (Set.range σ) ⊆ atlasRetractionDomain B ∩ atlasCell B j)
    (t : stdSimplex ℝ (Fin (k+1))) :
    (neighborhoodAffineSimplex (atlasRetractionDomain B) (atlasSphericalMap B C.homeomorph y₀) hf σ
      (fun _ hx => (hσ hx).1)).val t = C.chart j (sphericalNormalize
        (∑ i, t.val i • (atlasLiftLinear B (C.vertex j) j (σ i)+atlasLiftOffset B (C.vertex j) j))) := by
  have ht := hσ ((affineSimplexPatch_eq_convexHull σ).subset ⟨t,rfl⟩)
  change atlasSphericalMap B C.homeomorph y₀ (∑ i, t.val i • σ i) = _
  rw [atlasSphericalMap_chart C y₀ j (∑ i, t.val i • σ i) ht.1 ht.2]
  change C.chart j (normalizedAffineMap (atlasLiftLinear B (C.vertex j) j)
    (atlasLiftOffset B (C.vertex j) j) (∑ i, t.val i • σ i)) = _
  rw [normalizedAffineMap,affineMap_barycentric]

end Paper28
