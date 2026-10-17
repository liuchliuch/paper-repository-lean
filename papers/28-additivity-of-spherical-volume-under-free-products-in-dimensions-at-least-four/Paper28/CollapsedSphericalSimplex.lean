import Paper28.AffineSimplexTangents
import Paper28.SphericalAtlasSimplexGeometry
import Paper28.RankZeroCurrentPushforward

/-! A collapsed spherical image contributes the zero k-current. The
projective rank drop, tangent restriction and zero area are own proofs.
No collapsed-image vanishing assertion is an external premise. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set

set_option maxHeartbeats 600000 in
theorem atlas_collapsed_simplex_push_eq_zero
    {V Idx : Type*} [Fintype V] [DecidableEq V] [Fintype Idx]
    {d k : ℕ} {K : FiniteEuclideanComplex (EuclideanAmbient d)}
    {B : FullSubcomplexBarycentricAtlas K V Idx} {Y : Type} [metricY : MetricSpace Y]
    (C : FullSubcomplexSphericalCharts B Y) (y₀ : Y)
    (I : CompactIntegralCurrentAlgebraInput.{0,0} (EuclideanAmbient d) inferInstance)
    (S : EuclideanSimplexIntegrationInput d I) (R : EuclideanCurrentTangentInput d I)
    (hTangent : EuclideanAffineSupportTangentInput I R)
    (J : CompactIntegralCurrentAlgebraInput.{0,0} Y metricY)
    (hFaith : CurrentMassFaithfulnessInput J) (hCB : CauchyBinetInput)
    (hf : LipschitzNearSet inferInstance metricY (atlasSphericalMap B C.homeomorph y₀) (atlasRetractionDomain B))
    (P : NeighborhoodCurrentPushforwardInput inferInstance metricY I J (atlasRetractionDomain B)
      (atlasSphericalMap B C.homeomorph y₀) (atlasRetractionDomain_isOpen B) hf)
    (A : EuclideanCurrentAreaInput metricY I R J (atlasRetractionDomain B)
      (atlasSphericalMap B C.homeomorph y₀) (atlasRetractionDomain_isOpen B) hf P)
    (j : Idx) (σ : AffineSimplexVertices d k)
    (hσ : convexHull ℝ (Set.range σ) ⊆ atlasRetractionDomain B ∩ atlasCell B j)
    (hk : 0 < k) (hDep : ¬ LinearIndependent ℝ (atlasSimplexRawVertices C j σ)) :
    P.push k ⟨S.integration k σ,(S.support_subset k σ).trans (fun _ hx => (hσ hx).1)⟩ = 0 := by
  classical
  let L := atlasLiftLinear B (C.vertex j) j
  let b := atlasLiftOffset B (C.vertex j) j
  have hDrop : ∀ x ∈ convexHull ℝ (Set.range σ),
      ∃ W : Submodule ℝ (EuclideanAmbient (C.dimension j)), Module.finrank ℝ W < k ∧
        ∀ h ∈ affineSimplexDirections σ, normalizedAffineDerivative L b x h ∈ W := by
    intro x hx
    exact normalizedAffineDerivative_rank_drop L b σ x hx (atlasSphereLift_raw_nonzero C j x (hσ hx)) hDep
  let W : EuclideanAmbient d → Submodule ℝ (EuclideanAmbient (C.dimension j)) :=
    fun x => if hx : x ∈ convexHull ℝ (Set.range σ) then (hDrop x hx).choose else ⊥
  let strata : realizationFaces B j → Set (EuclideanAmbient d) :=
    fun F => realizationStratum B j F ∩ convexHull ℝ (Set.range σ)
  apply push_eq_zero_of_stratified_tangent_rank metricY I R J hFaith hCB
    (atlasRetractionDomain B) (atlasSphericalMap B C.homeomorph y₀) (atlasRetractionDomain_isOpen B)
    hf P A _ hk strata (atlasSphereLift B (C.vertex j) j) (atlasSphereDerivativeMatrix C j)
    ?_ ?_ ?_ ?_ (affineSimplexDirections σ)
    (affineSimplex_current_tangent_directions I R hTangent S σ) W ?_ ?_
  · intro x hx
    have hxσ := S.support_subset k σ hx
    obtain ⟨F,hF⟩ := mem_iUnion.mp (realizationStrata_cover j (hσ hxσ))
    exact mem_iUnion.mpr ⟨F,hF,hxσ⟩
  · intro F x hx
    exact atlasSphereLift_unit C j x hx.1.1
  · intro F x hx
    obtain ⟨r,hr,hRound⟩ := atlasSphereLift_round_stratum C y₀ j F x hx.1
    exact ⟨r,hr,fun y hy z hz hyr hzr => hRound y hy.1 z hz.1 hyr hzr⟩
  · intro F x hx
    exact atlasSphereLift_hasFDerivAt C j x hx.1.1
  · intro x hx
    have hxσ := S.support_subset k σ hx
    dsimp only [W]
    rw [dif_pos hxσ]
    exact (hDrop x hxσ).choose_spec.1
  · intro x hx h hh
    have hxσ := S.support_subset k σ hx
    have hx0 := atlasSphereLift_raw_nonzero C j x (hσ hxσ)
    have he : (Matrix.toEuclideanLin (atlasSphereDerivativeMatrix C j x)).toContinuousLinearMap =
        normalizedAffineDerivative L b x :=
      (atlasSphereLift_hasFDerivAt C j x (hσ hxσ)).unique (normalizedAffineMap_hasFDerivAt L b x hx0)
    change (Matrix.toEuclideanLin (atlasSphereDerivativeMatrix C j x)).toContinuousLinearMap h ∈ W x
    rw [he]
    simpa only [W,dif_pos hxσ] using (hDrop x hxσ).choose_spec.2 h hh

end Paper28
