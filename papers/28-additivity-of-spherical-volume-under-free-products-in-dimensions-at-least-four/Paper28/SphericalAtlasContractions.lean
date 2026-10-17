import Paper28.SphericalRealizationCharts
import Paper28.BarycentricAtlasRegularity
import Paper28.StrongContractionTransfer

/-! Actual completeness and exact locally strong Lipschitz contractions
for the spherical realization. These verify the metric hypotheses of the
published current-homology comparison rather than assuming them. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
universe w

theorem spherical_atlas_compactSpace
    {V Idx : Type*} [Fintype V] [DecidableEq V] [Fintype Idx]
    {d : ℕ} {K : FiniteEuclideanComplex (EuclideanAmbient d)}
    {B : FullSubcomplexBarycentricAtlas K V Idx} {Y : Type w} [MetricSpace Y]
    (C : FullSubcomplexSphericalCharts B Y) : CompactSpace Y := C.homeomorph.compactSpace

theorem spherical_atlas_completeSpace
    {V Idx : Type*} [Fintype V] [DecidableEq V] [Fintype Idx]
    {d : ℕ} {K : FiniteEuclideanComplex (EuclideanAmbient d)}
    {B : FullSubcomplexBarycentricAtlas K V Idx} {Y : Type w} [MetricSpace Y]
    (C : FullSubcomplexSphericalCharts B Y) : CompleteSpace Y := by
  letI := spherical_atlas_compactSpace C
  infer_instance

theorem spherical_atlas_locally_strong_contractions
    {V Idx : Type*} [Fintype V] [DecidableEq V] [Fintype Idx]
    {d : ℕ} {K : FiniteEuclideanComplex (EuclideanAmbient d)}
    (B : FullSubcomplexBarycentricAtlas K V Idx) {Y : Type w} [MetricSpace Y]
    (C : FullSubcomplexSphericalCharts B Y) (L M : NNReal)
    (hL : 0 < (L : ℝ)) (hM : 0 < (M : ℝ))
    (hh : LipschitzWith L C.homeomorph) (hg : LipschitzWith M C.homeomorph.symm) :
    AdmitsLocallyStrongLipschitzContractions Y :=
  locally_strong_contractions_biLipschitz C.homeomorph L M hL hM hh hg
    (atlas_polyhedron_locally_strong_contractions B)

theorem spherical_atlas_comparison_hypotheses
    {V Idx : Type*} [Fintype V] [DecidableEq V] [Fintype Idx]
    {d : ℕ} {K : FiniteEuclideanComplex (EuclideanAmbient d)}
    (B : FullSubcomplexBarycentricAtlas K V Idx) {Y : Type w} [MetricSpace Y]
    (C : FullSubcomplexSphericalCharts B Y) (L M : NNReal)
    (hh : LipschitzWith L C.homeomorph) (hg : LipschitzWith M C.homeomorph.symm) :
    CompleteSpace Y ∧ AdmitsLocallyStrongLipschitzContractions Y := by
  refine ⟨spherical_atlas_completeSpace C,?_⟩
  exact spherical_atlas_locally_strong_contractions B C (L+1) (M+1)
    (by simp only [NNReal.coe_add,NNReal.coe_one]; positivity)
    (by simp only [NNReal.coe_add,NNReal.coe_one]; positivity)
    (hh.weaken (le_add_of_nonneg_right zero_le_one))
    (hg.weaken (le_add_of_nonneg_right zero_le_one))

end Paper28
