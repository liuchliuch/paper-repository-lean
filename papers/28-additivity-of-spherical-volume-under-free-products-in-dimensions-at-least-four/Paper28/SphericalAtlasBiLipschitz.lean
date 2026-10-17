import Paper28.SphericalAtlasInverseFormula
import Paper28.SphericalAtlasForwardLipschitz

/-! The actual normalized-barycentric realization is bi-Lipschitz for
the exact intrinsic spherical cell metric. Both constants are constructed
from the actual finite cells; neither bound is a theorem premise. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
universe w
variable {V Idx : Type*} [Fintype V] [DecidableEq V] [Fintype Idx]
  {d : ℕ} {K : FiniteEuclideanComplex (EuclideanAmbient d)}
  {B : FullSubcomplexBarycentricAtlas K V Idx} {Y : Type w} [MetricSpace Y]
variable (C : FullSubcomplexSphericalCharts B Y) (Metric : SphericalCellPathMetricInput C)
  (hQ : CellVertexIndependence C)

include Metric hQ in
theorem spherical_realization_inverse_lipschitz : ∃ M : NNReal, LipschitzWith M C.homeomorph.symm := by
  classical
  choose L hLip using fun j => atlasCellInverse_lipschitz C hQ j
  let M : NNReal := Finset.univ.sup L+1
  have hM : 0 < (M : ℝ) := by dsimp [M]; positivity
  have hUnit : ∀ j u, u ∈ closedSphericalPatch (C.vertex j) (B.cells j ∩ B.selected) → ‖u‖ = 1 := by
    intro j u hu
    obtain ⟨t,ht,rfl⟩ := hu
    apply sphericalNormalize_norm
    intro hz
    have he := atlasCellSumFunctional_combination C hQ j t ht
    rw [hz,map_zero] at he
    exact zero_ne_one he
  refine ⟨M,lipschitz_of_spherical_cell_bounds C Metric C.homeomorph.symm M hM ?_⟩
  intro j u v hu hv
  have hMax : (L j : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast ((Finset.le_sup (Finset.mem_univ j) : L j ≤ Finset.univ.sup L).trans
      (le_add_of_nonneg_right zero_le_one))
  change dist (C.homeomorph.symm (C.chart j u)).val (C.homeomorph.symm (C.chart j v)).val ≤ _
  rw [← atlasCellInverse_formula C hQ j u hu,← atlasCellInverse_formula C hQ j v hv]
  have hChord : dist u v ≤ angular u v := by
    simpa only [dist_eq_norm] using chord_le_angular u v (hUnit j u hu) (hUnit j v hv)
  exact ((hLip j).dist_le_mul u hu v hv).trans
    ((mul_le_mul_of_nonneg_left hChord (L j).coe_nonneg).trans
      (mul_le_mul_of_nonneg_right hMax (Real.arccos_nonneg _)))

include Metric hQ in
theorem spherical_realization_biLipschitz (y₀ : Y) :
    ∃ L M : NNReal, LipschitzWith L C.homeomorph ∧ LipschitzWith M C.homeomorph.symm := by
  obtain ⟨L,hL⟩ := spherical_realization_lipschitz C Metric y₀
  obtain ⟨M,hM⟩ := spherical_realization_inverse_lipschitz C Metric hQ
  exact ⟨L,M,hL,hM⟩

def sphericalForwardConstant (y₀ : Y) : NNReal := (spherical_realization_lipschitz C Metric y₀).choose
def sphericalInverseConstant : NNReal := (spherical_realization_inverse_lipschitz C Metric hQ).choose

theorem sphericalForwardConstant_lipschitz (y₀ : Y) :
    LipschitzWith (sphericalForwardConstant C Metric y₀) C.homeomorph :=
  (spherical_realization_lipschitz C Metric y₀).choose_spec

theorem sphericalInverseConstant_lipschitz :
    LipschitzWith (sphericalInverseConstant C Metric hQ) C.homeomorph.symm :=
  (spherical_realization_inverse_lipschitz C Metric hQ).choose_spec

end Paper28
