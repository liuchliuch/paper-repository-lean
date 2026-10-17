import Paper28.SphericalAtlasGeometry
import Paper28.ProjectiveSimplexImages

/-! Exact images of actual affine simplices under h composed with the
constructed retraction: spherical geodesic simplex images in its actual
chart, including lower dimensional images. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
universe w

theorem atlasSphericalMap_simplex_image
    {V Idx : Type*} [Fintype V] [DecidableEq V] [Fintype Idx]
    {d k : ℕ} {K : FiniteEuclideanComplex (EuclideanAmbient d)}
    {A : FullSubcomplexBarycentricAtlas K V Idx} {Y : Type w} [MetricSpace Y]
    (C : FullSubcomplexSphericalCharts A Y) (y₀ : Y) (j : Idx)
    (σ : AffineSimplexVertices d k)
    (hσ : convexHull ℝ (Set.range σ) ⊆ atlasRetractionDomain A ∩ atlasCell A j) :
    atlasSphericalMap A C.homeomorph y₀ '' convexHull ℝ (Set.range σ) =
      C.chart j '' sphericalSimplexPatch (fun i => atlasSphereLift A (C.vertex j) j (σ i)) := by
  have hVertex : ∀ i, atlasLiftLinear A (C.vertex j) j (σ i)+atlasLiftOffset A (C.vertex j) j ≠ 0 :=
    fun i => atlasSphereLift_raw_nonzero C j (σ i) (hσ (subset_convexHull ℝ _ (mem_range_self i)))
  calc
    _ = (fun x => C.chart j (atlasSphereLift A (C.vertex j) j x)) '' convexHull ℝ (Set.range σ) := by
      apply Set.image_congr
      intro x hx
      exact atlasSphericalMap_chart C y₀ j x (hσ hx).1 (hσ hx).2
    _ = C.chart j '' (atlasSphereLift A (C.vertex j) j '' convexHull ℝ (Set.range σ)) := by
      rw [Set.image_image]
    _ = _ := by
      rw [← affineSimplexPatch_eq_convexHull]
      exact congrArg (fun Q => C.chart j '' Q)
        (normalizedAffineMap_simplex_image (atlasLiftLinear A (C.vertex j) j)
          (atlasLiftOffset A (C.vertex j) j) σ hVertex)

end Paper28
