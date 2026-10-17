import Paper28.FiniteSphericalTriangulation
import Paper28.SphericalPolyhedralPushforward

/-! The actual approximating simplices belong to source-cell spherical
polyhedral chains, not merely an unrestricted collection of round charts. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
variable {d : ℕ} {K : FiniteEuclideanComplex (EuclideanAmbient d)}
  {Y : Type} [metricY : MetricSpace Y] (S₀ : FiniteSphericalTriangulation K Y)
  {e : ℕ} {K₁ : FiniteEuclideanComplex (EuclideanAmbient e)}
  (N : SphericalNeighborhoodRealization S₀ K₁) (y₀ : Y)
  (hf : LipschitzNearSet inferInstance metricY (atlasSphericalMap N.atlas N.charts.homeomorph y₀)
    (atlasRetractionDomain N.atlas))

def realizationCellwiseSimplex {k : ℕ} (j : Fin N.cellCount) (σ : AffineSimplexVertices e k)
    (hσ : convexHull ℝ (Set.range σ) ⊆ atlasRetractionDomain N.atlas ∩ atlasCell N.atlas j) :
    CellwiseGeodesicParameterization S₀ k where
  geometric := atlasGeodesicParameterization N.charts N.vertex_injective y₀ hf j σ hσ
  cell := N.sourceCell j
  embedding := N.embedding j
  chart_eq u hu := N.chart_eq j u (atlasSimplexPatch_subset_closed N.charts j σ hσ hu)
  location := by
    rintro _ ⟨u,hu,rfl⟩
    exact N.location j ⟨u,atlasSimplexPatch_subset_closed N.charts j σ hσ hu,rfl⟩

variable (I : CompactIntegralCurrentAlgebraInput.{0,0} (EuclideanAmbient e) inferInstance)
  (S : EuclideanSimplexIntegrationInput e I)
  (R : EuclideanCurrentTangentInput e I) (hTangent : EuclideanAffineSupportTangentInput I R)
  (J : CompactIntegralCurrentAlgebraInput.{0,0} Y metricY)
  (A : LipschitzSimplexIntegrationInput metricY J)
  (hFaith : CurrentMassFaithfulnessInput J) (hCB : CauchyBinetInput)
  (P : NeighborhoodCurrentPushforwardInput inferInstance metricY I J (atlasRetractionDomain N.atlas)
    (atlasSphericalMap N.atlas N.charts.homeomorph y₀) (atlasRetractionDomain_isOpen N.atlas) hf)
  (Area : EuclideanCurrentAreaInput metricY I R J (atlasRetractionDomain N.atlas)
    (atlasSphericalMap N.atlas N.charts.homeomorph y₀) (atlasRetractionDomain_isOpen N.atlas) hf P)
  (F : SimplexPushforwardCompatibilityInput I S J A (atlasRetractionDomain N.atlas)
    (atlasSphericalMap N.atlas N.charts.homeomorph y₀) (atlasRetractionDomain_isOpen N.atlas) hf P)

include F in
theorem realization_simplex_push_mem_cellwise {k : ℕ} (j : Fin N.cellCount) (σ : AffineSimplexVertices e k)
    (hσ : convexHull ℝ (Set.range σ) ⊆ atlasRetractionDomain N.atlas ∩ atlasCell N.atlas j)
    (hLI : LinearIndependent ℝ (atlasSimplexRawVertices N.charts j σ)) :
    P.push k ⟨S.integration k σ,(S.support_subset k σ).trans (fun _ hx => (hσ hx).1)⟩ ∈
      cellwiseSphericalPolyhedralCurrents S₀ A k := by
  rw [F.push_affine_simplex k σ (fun _ hx => (hσ hx).1)]
  apply AddSubgroup.subset_closure
  exact ⟨⟨realizationCellwiseSimplex S₀ N y₀ hf j σ hσ,hLI⟩,rfl⟩

include R hTangent hFaith hCB Area F in
theorem realization_affine_simplex_push_cellwise {k : ℕ} (hk : 0 < k) (j : Fin N.cellCount)
    (σ : AffineSimplexVertices e k)
    (hσ : convexHull ℝ (Set.range σ) ⊆ atlasRetractionDomain N.atlas ∩ atlasCell N.atlas j) :
    P.push k ⟨S.integration k σ,(S.support_subset k σ).trans (fun _ hx => (hσ hx).1)⟩ ∈
      cellwiseSphericalPolyhedralCurrents S₀ A k := by
  classical
  by_cases hLI : LinearIndependent ℝ (atlasSimplexRawVertices N.charts j σ)
  · exact realization_simplex_push_mem_cellwise S₀ N y₀ hf I S J A P F j σ hσ hLI
  · rw [atlas_collapsed_simplex_push_eq_zero N.charts y₀ I S R hTangent J hFaith hCB hf P Area j σ hσ hk hLI]
    exact AddSubgroup.zero_mem _

include R hTangent hFaith hCB Area F in
theorem realization_polyhedral_push_cellwise
    (Sub : EuclideanPolyhedralCellSubdivisionInput I S) {k : ℕ} (hk : 0 < k)
    (Q : supportedCurrents I (atlasRetractionDomain N.atlas) k)
    (hQ : Q.val ∈ euclideanPolyhedralCurrents S k) :
    P.push k Q ∈ cellwiseSphericalPolyhedralCurrents S₀ A k := by
  classical
  obtain ⟨D⟩ := Sub.subdivision (fun j => N.atlas.vertex '' (N.atlas.cells j : Set (Fin N.vertexCount)))
    (fun j => (N.atlas.cells j).finite_toSet.image N.atlas.vertex) (atlasRetractionDomain N.atlas)
    (atlasRetractionDomain_isOpen N.atlas) atlasCells_cover k Q hQ
  let G : Fin D.count → supportedCurrents I (atlasRetractionDomain N.atlas) k := fun i =>
    ⟨S.integration k (D.simplex i),(S.support_subset k (D.simplex i)).trans
      (fun _ hx => (D.location i hx).1)⟩
  have hval : (∑ i, D.coefficient i • G i).val =
      ∑ i, D.coefficient i • S.integration k (D.simplex i) := by
    change (supportedCurrents I (atlasRetractionDomain N.atlas) k).subtype (∑ i, D.coefficient i • G i) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_zsmul]
    rfl
  have he : Q = ∑ i, D.coefficient i • G i := Subtype.ext (D.eq_sum.trans hval.symm)
  rw [he,map_sum]
  apply AddSubgroup.sum_mem
  intro i _
  rw [map_zsmul]
  apply AddSubgroup.zsmul_mem
  exact realization_affine_simplex_push_cellwise S₀ N y₀ hf I S R hTangent J A hFaith hCB P Area F hk
    (D.cell i) (D.simplex i) (D.location i)

end Paper28
