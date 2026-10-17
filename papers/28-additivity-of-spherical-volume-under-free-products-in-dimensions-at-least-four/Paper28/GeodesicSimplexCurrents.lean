import Paper28.SphericalAtlasSimplexGeometry
import Paper28.AffineSimplexPushforward

/-! Actual geodesic spherical simplex parameterizations and their integer
integration-current subgroups. Nondegenerate generators are kept separate
from possibly collapsed images; no unproved dimension-drop assertion is
used to identify the two groups. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
variable {Y : Type} [metricY : MetricSpace Y]

structure GeodesicSphericalParameterization (Y : Type) [MetricSpace Y] (k : ℕ) where
  dimension : ℕ
  rawVertices : Fin (k+1) → EuclideanAmbient dimension
  center : EuclideanAmbient dimension
  hemisphere : ∀ i, 0 < inner ℝ center (rawVertices i)
  chart : EuclideanAmbient dimension → Y
  chart_injective : Set.InjOn chart (sphericalSimplexPatch rawVertices)
  chart_round : ∀ u ∈ strictSphericalSimplexPatch rawVertices, ∃ r : ℝ, 0 < r ∧
    ∀ v ∈ strictSphericalSimplexPatch rawVertices, ∀ z ∈ strictSphericalSimplexPatch rawVertices,
      dist v u < r → dist z u < r → dist (chart v) (chart z) = angular v z
  parameter : LipschitzSingularSimplex Y k
  formula : ∀ t : stdSimplex ℝ (Fin (k+1)), parameter.val t =
    chart (sphericalNormalize (∑ i, t.val i • rawVertices i))

def geodesicImageCurrents
    {J : CompactIntegralCurrentAlgebraInput.{0,0} Y metricY}
    (A : LipschitzSimplexIntegrationInput metricY J) (k : ℕ) : AddSubgroup (J.Current k) :=
  AddSubgroup.closure (Set.range (fun σ : GeodesicSphericalParameterization Y k => A.integration k σ.parameter))

def nondegenerateGeodesicCurrents
    {J : CompactIntegralCurrentAlgebraInput.{0,0} Y metricY}
    (A : LipschitzSimplexIntegrationInput metricY J) (k : ℕ) : AddSubgroup (J.Current k) :=
  AddSubgroup.closure (Set.range (fun σ : {σ : GeodesicSphericalParameterization Y k //
    LinearIndependent ℝ σ.rawVertices} => A.integration k σ.val.parameter))

def atlasGeodesicParameterization
    {V Idx : Type*} [Fintype V] [DecidableEq V] [Fintype Idx]
    {d k : ℕ} {K : FiniteEuclideanComplex (EuclideanAmbient d)}
    {B : FullSubcomplexBarycentricAtlas K V Idx}
    (C : FullSubcomplexSphericalCharts B Y) (hB : Function.Injective B.vertex) (y₀ : Y)
    (hf : LipschitzNearSet inferInstance metricY (atlasSphericalMap B C.homeomorph y₀) (atlasRetractionDomain B))
    (j : Idx) (σ : AffineSimplexVertices d k)
    (hσ : convexHull ℝ (Set.range σ) ⊆ atlasRetractionDomain B ∩ atlasCell B j) :
    GeodesicSphericalParameterization Y k where
  dimension := C.dimension j
  rawVertices := atlasSimplexRawVertices C j σ
  center := C.center j
  hemisphere := atlasSimplexRaw_hemisphere C j σ hσ
  chart := C.chart j
  chart_injective := atlasSimplex_chart_injective C hB j σ hσ
  chart_round := atlasSimplex_chart_round_interior C j σ hσ
  parameter := neighborhoodAffineSimplex (atlasRetractionDomain B) (atlasSphericalMap B C.homeomorph y₀) hf σ
    (fun _ hx => (hσ hx).1)
  formula := neighborhoodAffineSimplex_projective_formula C y₀ hf j σ hσ

theorem atlas_affine_simplex_push_mem_geodesic_images
    {V Idx : Type*} [Fintype V] [DecidableEq V] [Fintype Idx]
    {d k : ℕ} {K : FiniteEuclideanComplex (EuclideanAmbient d)}
    {B : FullSubcomplexBarycentricAtlas K V Idx}
    (C : FullSubcomplexSphericalCharts B Y) (hB : Function.Injective B.vertex) (y₀ : Y)
    (I : CompactIntegralCurrentAlgebraInput.{0,0} (EuclideanAmbient d) inferInstance)
    (S : EuclideanSimplexIntegrationInput d I)
    (J : CompactIntegralCurrentAlgebraInput.{0,0} Y metricY)
    (A : LipschitzSimplexIntegrationInput metricY J)
    (hf : LipschitzNearSet inferInstance metricY (atlasSphericalMap B C.homeomorph y₀) (atlasRetractionDomain B))
    (P : NeighborhoodCurrentPushforwardInput inferInstance metricY I J (atlasRetractionDomain B)
      (atlasSphericalMap B C.homeomorph y₀) (atlasRetractionDomain_isOpen B) hf)
    (F : SimplexPushforwardCompatibilityInput I S J A (atlasRetractionDomain B)
      (atlasSphericalMap B C.homeomorph y₀) (atlasRetractionDomain_isOpen B) hf P)
    (j : Idx) (σ : AffineSimplexVertices d k)
    (hσ : convexHull ℝ (Set.range σ) ⊆ atlasRetractionDomain B ∩ atlasCell B j) :
    P.push k ⟨S.integration k σ,(S.support_subset k σ).trans (fun _ hx => (hσ hx).1)⟩ ∈ geodesicImageCurrents A k := by
  rw [F.push_affine_simplex k σ (fun _ hx => (hσ hx).1)]
  apply AddSubgroup.subset_closure
  exact ⟨atlasGeodesicParameterization C hB y₀ hf j σ hσ,rfl⟩

theorem atlas_affine_simplex_push_mem_nondegenerate
    {V Idx : Type*} [Fintype V] [DecidableEq V] [Fintype Idx]
    {d k : ℕ} {K : FiniteEuclideanComplex (EuclideanAmbient d)}
    {B : FullSubcomplexBarycentricAtlas K V Idx}
    (C : FullSubcomplexSphericalCharts B Y) (hB : Function.Injective B.vertex) (y₀ : Y)
    (I : CompactIntegralCurrentAlgebraInput.{0,0} (EuclideanAmbient d) inferInstance)
    (S : EuclideanSimplexIntegrationInput d I)
    (J : CompactIntegralCurrentAlgebraInput.{0,0} Y metricY)
    (A : LipschitzSimplexIntegrationInput metricY J)
    (hf : LipschitzNearSet inferInstance metricY (atlasSphericalMap B C.homeomorph y₀) (atlasRetractionDomain B))
    (P : NeighborhoodCurrentPushforwardInput inferInstance metricY I J (atlasRetractionDomain B)
      (atlasSphericalMap B C.homeomorph y₀) (atlasRetractionDomain_isOpen B) hf)
    (F : SimplexPushforwardCompatibilityInput I S J A (atlasRetractionDomain B)
      (atlasSphericalMap B C.homeomorph y₀) (atlasRetractionDomain_isOpen B) hf P)
    (j : Idx) (σ : AffineSimplexVertices d k)
    (hσ : convexHull ℝ (Set.range σ) ⊆ atlasRetractionDomain B ∩ atlasCell B j)
    (hIndependent : LinearIndependent ℝ (atlasSimplexRawVertices C j σ)) :
    P.push k ⟨S.integration k σ,(S.support_subset k σ).trans (fun _ hx => (hσ hx).1)⟩ ∈ nondegenerateGeodesicCurrents A k := by
  rw [F.push_affine_simplex k σ (fun _ hx => (hσ hx).1)]
  apply AddSubgroup.subset_closure
  exact ⟨⟨atlasGeodesicParameterization C hB y₀ hf j σ hσ,hIndependent⟩,rfl⟩

end Paper28
