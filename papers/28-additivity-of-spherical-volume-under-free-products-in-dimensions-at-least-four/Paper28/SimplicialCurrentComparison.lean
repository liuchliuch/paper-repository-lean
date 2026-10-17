import Paper28.SimplicialSingularMap
import Paper28.LipschitzSimplexIntegration
import Paper28.SphericalAtlasContractions
import Paper28.ChainHomologyFilling

/-! The two published comparison inputs are kept separate and pinned to
their actual canonical chain maps. The paper-owned integration homology
injection and exact finite integer simplicial filling are derived. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open CategoryTheory

structure SimplicialSingularHomologyComparisonInput : Prop where
  comparison : ∀ {d : ℕ} (K : FiniteEuclideanComplex (EuclideanAmbient d))
    {Y : Type} [MetricSpace Y] (h : K.complex.space ≃ₜ Y) (L : NNReal)
    (hh : LipschitzWith L h) (k : ℕ),
    IsIso (HomologicalComplex.homologyMap (finiteSimplicialToSingularChainMap h L hh) k)

def canonicalSimplicialCurrentChainMap
    {d : ℕ} {K : FiniteEuclideanComplex (EuclideanAmbient d)} {Y : Type} [metricY : MetricSpace Y]
    (h : K.complex.space → Y) (L : NNReal) (hh : LipschitzWith L h)
    {J : CompactIntegralCurrentAlgebraInput.{0,0} Y metricY}
    (A : LipschitzSimplexIntegrationInput metricY J) :
    finiteSimplicialChainComplex K ⟶ compactCurrentChainComplex J :=
  finiteSimplicialToLipschitzChainMap h L hh ≫ lipschitzCurrentIntegrationChainMap A

theorem spherical_simplicial_integration_homology_mono
    {V Idx : Type*} [Fintype V] [DecidableEq V] [Fintype Idx]
    {d : ℕ} {K : FiniteEuclideanComplex (EuclideanAmbient d)}
    (B : FullSubcomplexBarycentricAtlas K V Idx) {Y : Type} [metricY : MetricSpace Y]
    (C : FullSubcomplexSphericalCharts B Y) (L M : NNReal)
    (hL : LipschitzWith L C.homeomorph) (hM : LipschitzWith M C.homeomorph.symm)
    (J : CompactIntegralCurrentAlgebraInput.{0,0} Y metricY)
    (A : LipschitzSimplexIntegrationInput metricY J)
    (RS : LipschitzCurrentHomologyComparisonInput J A)
    (SS : SimplicialSingularHomologyComparisonInput) (k : ℕ) :
    Mono (HomologicalComplex.homologyMap (canonicalSimplicialCurrentChainMap C.homeomorph L hL A) k) := by
  obtain ⟨hComplete,hStrong⟩ := spherical_atlas_comparison_hypotheses B C L M hL hM
  letI := RS.comparison hComplete hStrong k
  letI := SS.comparison K C.homeomorph L hL k
  exact integration_homology_mono (finiteSimplicialToLipschitzChainMap C.homeomorph L hL)
    (lipschitzCurrentIntegrationChainMap A) (forgetLipschitzSingularChainMap Y)
    (finiteSimplicialToSingularChainMap C.homeomorph L hL)
    (canonicalSimplicialCurrentChainMap C.homeomorph L hL A) rfl rfl k

theorem spherical_prescribed_simplicial_filling
    {V Idx : Type*} [Fintype V] [DecidableEq V] [Fintype Idx]
    {d k : ℕ} {K : FiniteEuclideanComplex (EuclideanAmbient d)}
    (B : FullSubcomplexBarycentricAtlas K V Idx) {Y : Type} [metricY : MetricSpace Y]
    (C : FullSubcomplexSphericalCharts B Y) (L M : NNReal)
    (hL : LipschitzWith L C.homeomorph) (hM : LipschitzWith M C.homeomorph.symm)
    (J : CompactIntegralCurrentAlgebraInput.{0,0} Y metricY)
    (A : LipschitzSimplexIntegrationInput metricY J)
    (RS : LipschitzCurrentHomologyComparisonInput J A)
    (SS : SimplicialSingularHomologyComparisonInput)
    (z : finiteSimplicialChains K (k+1)) (hz : finiteSimplicialBoundary k z = 0)
    (hBounds : ∃ D : J.Current (k+2), J.boundary (k+1) D =
      (canonicalSimplicialCurrentChainMap C.homeomorph L hL A).f (k+1) z) :
    ∃ Q : finiteSimplicialChains K (k+2), finiteSimplicialBoundary (k+1) Q = z := by
  letI := spherical_simplicial_integration_homology_mono B C L M hL hM J A RS SS (k+1)
  have hd : ∀ n, (finiteSimplicialChainComplex K).d (n+1) n = AddCommGrpCat.ofHom (finiteSimplicialBoundary n) :=
    fun n => ChainComplex.of_d _ _ _ n
  have hz' : (finiteSimplicialChainComplex K).d (k+1) k z = 0 := by
    rw [hd]
    exact hz
  have hb' : ∃ D : (compactCurrentChainComplex J).X (k+2),
      (compactCurrentChainComplex J).d (k+2) (k+1) D =
        (canonicalSimplicialCurrentChainMap C.homeomorph L hL A).f (k+1) z := by
    rw [compactCurrentChainComplex_d]
    exact hBounds
  have hQ := prescribed_chain_filling_of_homology_mono
    (canonicalSimplicialCurrentChainMap C.homeomorph L hL A) k z hz' hb'
  rw [hd] at hQ
  exact hQ

end Paper28
