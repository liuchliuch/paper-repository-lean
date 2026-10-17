import Paper28.NondegenerateSimplicialChains
import Paper28.BarycentricNeighborhoodAtlas
import Paper28.PushforwardHomology

/-! Actual integration of oriented simplicial chains on the carrier, then
their actual spherical pushforward. All supports and boundary maps are
native, so subsequent homology comparisons apply to the real chain map. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open CategoryTheory Set
variable {d : ℕ} {K : FiniteEuclideanComplex (EuclideanAmbient d)}

theorem orderedIntegration_support_carrier
    {I : CompactIntegralCurrentAlgebraInput.{0,0} (EuclideanAmbient d) inferInstance}
    (S : EuclideanSimplexIntegrationInput d I) (k : ℕ) (z : orderedSimplicialChains K k) :
    I.support (orderedIntegration S k z) ⊆ K.complex.space := by
  refine FreeAbelianGroup.induction_on z ?_ ?_ ?_ ?_
  · rw [map_zero,I.support_zero]
    exact empty_subset _
  · intro σ
    rw [orderedIntegration,FreeAbelianGroup.lift_apply_of]
    exact (S.support_subset k (orderedSimplexVertices σ)).trans
      ((convexHull_mono (fun _ hx => by
        obtain ⟨i,rfl⟩ := hx
        exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)).trans
        (K.complex.convexHull_subset_space σ.face))
  · intro σ hσ
    rw [map_neg]
    exact (I.support_neg_subset _).trans hσ
  · intro a b ha hb
    rw [map_add]
    exact (I.support_add_subset _ _).trans (union_subset ha hb)

def nondegenerateChainInclusionMap : finiteSimplicialChainComplex K ⟶ orderedSimplicialChainComplex K :=
  ChainComplex.ofHom _ _ (by intro k; apply AddCommGrpCat.ext; intro z; exact finiteSimplicialBoundary_squared k z)
    _ _ (AlgebraicTopology.AlternatingFaceMapComplex.d_squared (orderedComplexSSet K ⋙ AddCommGrpCat.free))
    (fun k => AddCommGrpCat.ofHom (nondegenerateChainInclusion k)) (by
      intro k
      apply AddCommGrpCat.ext
      intro z
      have he := (nondegenerateChainInclusion_boundary k z).symm
      exact (congrArg (fun q => q (nondegenerateChainInclusion (k+1) z))
        (AlgebraicTopology.alternatingFaceMapComplex_obj_d (orderedComplexSSet K ⋙ AddCommGrpCat.free) k)).symm.trans he)

def orderedIntegrationSupported
    {I : CompactIntegralCurrentAlgebraInput.{0,0} (EuclideanAmbient d) inferInstance}
    (S : EuclideanSimplexIntegrationInput d I) (U : Set (EuclideanAmbient d))
    (hU : K.complex.space ⊆ U) (k : ℕ) : orderedSimplicialChains K k →+ supportedCurrents I U k where
  toFun z := ⟨orderedIntegration S k z,(orderedIntegration_support_carrier S k z).trans hU⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

def orderedIntegrationSupportedChainMap
    {I : CompactIntegralCurrentAlgebraInput.{0,0} (EuclideanAmbient d) inferInstance}
    (S : EuclideanSimplexIntegrationInput d I) (U : Set (EuclideanAmbient d))
    (hU : K.complex.space ⊆ U) : orderedSimplicialChainComplex K ⟶ supportedCurrentChainComplex I U :=
  ChainComplex.ofHom _ _
    (AlgebraicTopology.AlternatingFaceMapComplex.d_squared (orderedComplexSSet K ⋙ AddCommGrpCat.free))
    _ _ (by intro k; apply AddCommGrpCat.ext; intro z; exact supportedBoundary_squared_zero I U k z)
    (fun k => AddCommGrpCat.ofHom (orderedIntegrationSupported S U hU k)) (by
      intro k
      apply AddCommGrpCat.ext
      intro z
      apply Subtype.ext
      exact (orderedIntegration_boundary S k z).trans
        (congrArg (fun q => orderedIntegration S k (q z))
          (AlgebraicTopology.alternatingFaceMapComplex_obj_d (orderedComplexSSet K ⋙ AddCommGrpCat.free) k)))

def finiteCarrierIntegrationChainMap
    {I : CompactIntegralCurrentAlgebraInput.{0,0} (EuclideanAmbient d) inferInstance}
    (S : EuclideanSimplexIntegrationInput d I) (U : Set (EuclideanAmbient d))
    (hU : K.complex.space ⊆ U) : finiteSimplicialChainComplex K ⟶ supportedCurrentChainComplex I U :=
  nondegenerateChainInclusionMap ≫ orderedIntegrationSupportedChainMap S U hU

def finiteSphericalIntegrationChainMap {Y : Type} {metricY : MetricSpace Y}
    {I : CompactIntegralCurrentAlgebraInput.{0,0} (EuclideanAmbient d) inferInstance}
    {J : CompactIntegralCurrentAlgebraInput.{0,0} Y metricY}
    (S : EuclideanSimplexIntegrationInput d I) (U : Set (EuclideanAmbient d))
    (hKU : K.complex.space ⊆ U) (f : EuclideanAmbient d → Y) (hU : IsOpen U)
    (hf : LipschitzNearSet inferInstance metricY f U)
    (P : NeighborhoodCurrentPushforwardInput inferInstance metricY I J U f hU hf) :
    finiteSimplicialChainComplex K ⟶ compactCurrentChainComplex J :=
  finiteCarrierIntegrationChainMap S U hKU ≫ neighborhoodPushforwardChainMap P

end Paper28
