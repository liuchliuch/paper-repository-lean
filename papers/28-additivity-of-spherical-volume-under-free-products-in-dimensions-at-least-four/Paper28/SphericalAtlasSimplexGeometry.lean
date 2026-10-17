import Paper28.SphericalChartEmbedding
import Paper28.AtlasAffineSimplexCoordinates
import Paper28.SphericalAtlasGeometry

/-! Actual spherical geometry of the image of a subdivided ambient
simplex: a common hemisphere, an injective chart on its closed spherical
patch, and the exact round metric along its relative interior. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
universe w
variable {V Idx : Type*} [Fintype V] [DecidableEq V] [Fintype Idx]

theorem supportedSimplex_inner_pos {m : ℕ} (F : Finset V) (t : stdSimplex ℝ V)
    (q : V → EuclideanAmbient m) (c : EuclideanAmbient m)
    (ht : ∀ v, v ∉ F → t.val v = 0) (hc : ∀ v ∈ F, 0 < inner ℝ c (q v)) :
    0 < inner ℝ c (∑ v, t.val v • q v) := by
  have hpos : ∃ v ∈ F, 0 < t.val v := by
    by_contra h
    push_neg at h
    have hn := Finset.sum_nonpos (fun v hv => h v hv)
    rw [supportedSimplex_sum F t ht] at hn
    linarith
  obtain ⟨v,hv,hvp⟩ := hpos
  simp only [inner_sum,real_inner_smul_right]
  apply Finset.sum_pos'
  · intro a _
    by_cases ha : a ∈ F
    · exact mul_nonneg (t.property.1 a) (hc a ha).le
    · rw [ht a ha,zero_mul]
  · exact ⟨v,Finset.mem_univ _,mul_pos hvp (hc v hv)⟩

variable {d k : ℕ} {K : FiniteEuclideanComplex (EuclideanAmbient d)}
  {B : FullSubcomplexBarycentricAtlas K V Idx} {Y : Type w} [MetricSpace Y]
variable (C : FullSubcomplexSphericalCharts B Y)

def atlasSimplexRawVertices (j : Idx) (σ : AffineSimplexVertices d k) :
    Fin (k+1) → EuclideanAmbient (C.dimension j) :=
  fun i => atlasLiftLinear B (C.vertex j) j (σ i)+atlasLiftOffset B (C.vertex j) j

theorem atlasSimplexRaw_hemisphere (j : Idx) (σ : AffineSimplexVertices d k)
    (hσ : convexHull ℝ (Set.range σ) ⊆ atlasRetractionDomain B ∩ atlasCell B j) :
    ∀ i, 0 < inner ℝ (C.center j) (atlasSimplexRawVertices C j σ i) := by
  intro i
  have hx := hσ (subset_convexHull ℝ _ (mem_range_self i))
  have hp := supportedSimplex_inner_pos (B.cells j ∩ B.selected)
    (atlasSimplexCoordinates B (σ i) hx.1) (C.vertex j) (C.center j)
    (atlasCoordinates_zero_off_cell B j (σ i) hx.2) (C.hemisphere j)
  change 0 < inner ℝ (C.center j) (∑ v, atlasCoordinates B (σ i) v • C.vertex j v) at hp
  rw [atlasCoordinates_weighted_sum B (C.vertex j) (σ i),real_inner_smul_right] at hp
  change 0 < inner ℝ (C.center j) (atlasLiftLinear B (C.vertex j) j (σ i)+atlasLiftOffset B (C.vertex j) j)
  rw [atlasLift_raw_eq B (C.vertex j) j (σ i) hx.2]
  exact (mul_pos_iff_of_pos_left (inv_pos.mpr hx.1.2)).mp hp

theorem atlasSimplexPatch_subset_closed (j : Idx) (σ : AffineSimplexVertices d k)
    (hσ : convexHull ℝ (Set.range σ) ⊆ atlasRetractionDomain B ∩ atlasCell B j) :
    sphericalSimplexPatch (atlasSimplexRawVertices C j σ) ⊆
      closedSphericalPatch (C.vertex j) (B.cells j ∩ B.selected) := by
  rintro u ⟨t,rfl⟩
  have hx := hσ ((affineSimplexPatch_eq_convexHull σ).subset ⟨t,rfl⟩)
  have hm := atlasSphereLift_mem_closed_patch C j (∑ i, t.val i • σ i) hx
  change sphericalNormalize (atlasLiftLinear B (C.vertex j) j (∑ i, t.val i • σ i)+
    atlasLiftOffset B (C.vertex j) j) ∈ _ at hm
  rw [affineMap_barycentric] at hm
  exact hm

theorem atlasSimplex_chart_injective (hB : Function.Injective B.vertex) (j : Idx)
    (σ : AffineSimplexVertices d k)
    (hσ : convexHull ℝ (Set.range σ) ⊆ atlasRetractionDomain B ∩ atlasCell B j) :
    Set.InjOn (C.chart j) (sphericalSimplexPatch (atlasSimplexRawVertices C j σ)) :=
  (spherical_chart_injective_on_closed_patch C hB j).mono (atlasSimplexPatch_subset_closed C j σ hσ)

def strictSphericalSimplexPatch {m k : ℕ} (q : Fin (k+1) → EuclideanAmbient m) : Set (EuclideanAmbient m) :=
  {u | ∃ t : stdSimplex ℝ (Fin (k+1)), (∀ i, 0 < t.val i) ∧
    u = sphericalNormalize (∑ i, t.val i • q i)}

theorem atlasSimplexImageFace_subset (j : Idx) (σ : AffineSimplexVertices d k)
    (hσ : convexHull ℝ (Set.range σ) ⊆ atlasRetractionDomain B ∩ atlasCell B j) :
    atlasSimplexImageFace B σ ⊆ B.cells j ∩ B.selected := by
  classical
  intro v hv
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hv
  exact atlasPositiveFace_subset B j (σ i) (hσ (subset_convexHull ℝ _ (mem_range_self i))).2 hi

theorem atlasSimplexInterior_subset_relative (j : Idx) (σ : AffineSimplexVertices d k)
    (hσ : convexHull ℝ (Set.range σ) ⊆ atlasRetractionDomain B ∩ atlasCell B j) :
    strictSphericalSimplexPatch (atlasSimplexRawVertices C j σ) ⊆
      relativeSphericalPatch (C.vertex j) (atlasSimplexImageFace B σ) := by
  rintro u ⟨t,ht,rfl⟩
  let F : realizationFaces B j := ⟨atlasSimplexImageFace B σ,atlasSimplexImageFace_subset j σ hσ⟩
  have hx := hσ ((affineSimplexPatch_eq_convexHull σ).subset ⟨t,rfl⟩)
  have hm := atlasSphereLift_mem_relative C j F (∑ i, t.val i • σ i)
    ⟨hx,atlasPositiveFace_interior B j σ hσ t ht⟩
  change sphericalNormalize (atlasLiftLinear B (C.vertex j) j (∑ i, t.val i • σ i)+
    atlasLiftOffset B (C.vertex j) j) ∈ _ at hm
  rw [affineMap_barycentric] at hm
  exact hm

theorem atlasSimplex_chart_round_interior (j : Idx) (σ : AffineSimplexVertices d k)
    (hσ : convexHull ℝ (Set.range σ) ⊆ atlasRetractionDomain B ∩ atlasCell B j) :
    ∀ u ∈ strictSphericalSimplexPatch (atlasSimplexRawVertices C j σ), ∃ r : ℝ, 0 < r ∧
    ∀ v ∈ strictSphericalSimplexPatch (atlasSimplexRawVertices C j σ),
    ∀ z ∈ strictSphericalSimplexPatch (atlasSimplexRawVertices C j σ),
      dist v u < r → dist z u < r → dist (C.chart j v) (C.chart j z) = angular v z := by
  intro u hu
  have hs := atlasSimplexInterior_subset_relative C j σ hσ
  obtain ⟨r,hr,hMetric⟩ := C.round_relative_face j (atlasSimplexImageFace B σ)
    (atlasSimplexImageFace_subset j σ hσ) u (hs hu)
  exact ⟨r,hr,fun v hv z hz hvu hzu => hMetric v (hs hv) z (hs hz) hvu hzu⟩

end Paper28
