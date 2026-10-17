import Paper28.CollapsedSphericalSimplex
import Paper28.GeodesicSimplexCurrents
import Paper28.EuclideanCellSubdivisionInput

/-! Every piecewise-projective spherical push of an actual Euclidean
polyhedral current is a finite integer sum of nondegenerate spherical
geodesic simplex currents. Collapsed pieces are proved to vanish. Only
generic common affine subdivision and canonical integration laws are inputs. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
variable {V Idx : Type} [Fintype V] [DecidableEq V] [Fintype Idx]
  {d : ℕ} {K : FiniteEuclideanComplex (EuclideanAmbient d)}
  {B : FullSubcomplexBarycentricAtlas K V Idx} {Y : Type} [metricY : MetricSpace Y]
variable (C : FullSubcomplexSphericalCharts B Y) (hB : Function.Injective B.vertex) (y₀ : Y)
  (I : CompactIntegralCurrentAlgebraInput.{0,0} (EuclideanAmbient d) inferInstance)
  (S : EuclideanSimplexIntegrationInput d I) (R : EuclideanCurrentTangentInput d I)
  (hTangent : EuclideanAffineSupportTangentInput I R)
  (J : CompactIntegralCurrentAlgebraInput.{0,0} Y metricY)
  (A : LipschitzSimplexIntegrationInput metricY J)
  (hFaith : CurrentMassFaithfulnessInput J) (hCB : CauchyBinetInput)
  (hf : LipschitzNearSet inferInstance metricY (atlasSphericalMap B C.homeomorph y₀) (atlasRetractionDomain B))
  (P : NeighborhoodCurrentPushforwardInput inferInstance metricY I J (atlasRetractionDomain B)
    (atlasSphericalMap B C.homeomorph y₀) (atlasRetractionDomain_isOpen B) hf)
  (Area : EuclideanCurrentAreaInput metricY I R J (atlasRetractionDomain B)
    (atlasSphericalMap B C.homeomorph y₀) (atlasRetractionDomain_isOpen B) hf P)
  (F : SimplexPushforwardCompatibilityInput I S J A (atlasRetractionDomain B)
    (atlasSphericalMap B C.homeomorph y₀) (atlasRetractionDomain_isOpen B) hf P)

include hB R hTangent hFaith hCB Area F

theorem atlas_affine_simplex_push_polyhedral {k : ℕ} (hk : 0 < k) (j : Idx)
    (σ : AffineSimplexVertices d k)
    (hσ : convexHull ℝ (Set.range σ) ⊆ atlasRetractionDomain B ∩ atlasCell B j) :
    P.push k ⟨S.integration k σ,(S.support_subset k σ).trans (fun _ hx => (hσ hx).1)⟩ ∈
      nondegenerateGeodesicCurrents A k := by
  classical
  by_cases hLI : LinearIndependent ℝ (atlasSimplexRawVertices C j σ)
  · exact atlas_affine_simplex_push_mem_nondegenerate C hB y₀ I S J A hf P F j σ hσ hLI
  · rw [atlas_collapsed_simplex_push_eq_zero C y₀ I S R hTangent J hFaith hCB hf P Area j σ hσ hk hLI]
    exact AddSubgroup.zero_mem _

set_option maxHeartbeats 600000 in
theorem spherical_polyhedral_pushforward
    (Sub : EuclideanPolyhedralCellSubdivisionInput I S) {k : ℕ} (hk : 0 < k)
    (Q : supportedCurrents I (atlasRetractionDomain B) k)
    (hQ : Q.val ∈ euclideanPolyhedralCurrents S k) :
    P.push k Q ∈ nondegenerateGeodesicCurrents A k := by
  classical
  obtain ⟨D⟩ := Sub.subdivision (fun j => B.vertex '' (B.cells j : Set V))
    (fun j => (B.cells j).finite_toSet.image B.vertex) (atlasRetractionDomain B)
    (atlasRetractionDomain_isOpen B) atlasCells_cover k Q hQ
  let G : Fin D.count → supportedCurrents I (atlasRetractionDomain B) k := fun i =>
    ⟨S.integration k (D.simplex i),(S.support_subset k (D.simplex i)).trans
      (fun _ hx => (D.location i hx).1)⟩
  have hval : (∑ i, D.coefficient i • G i).val =
      ∑ i, D.coefficient i • S.integration k (D.simplex i) := by
    change (supportedCurrents I (atlasRetractionDomain B) k).subtype (∑ i, D.coefficient i • G i) = _
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
  exact atlas_affine_simplex_push_polyhedral C hB y₀ I S R hTangent J A hFaith hCB hf P Area F hk
    (D.cell i) (D.simplex i) (D.location i)

end Paper28
