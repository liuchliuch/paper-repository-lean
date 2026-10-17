import Paper28.BarycentricNeighborhoodAtlas
import Paper28.FiniteLipschitzCalculus
import Paper28.StrongContractions

/-! Native local Lipschitz regularity of the actual barycentric retraction
and the exact RS strong-contraction hypothesis for the actual polyhedron. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter Set Metric
open scoped Topology
variable {H V Idx : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [DecidableEq H]
  [Fintype V] [DecidableEq V] [Fintype Idx]
variable {K : FiniteEuclideanComplex H} (A : FullSubcomplexBarycentricAtlas K V Idx)

theorem atlasSelectedSum_lipschitz : ∃ L : NNReal, LipschitzWith L (atlasSelectedSum A) :=
  exists_lipschitz_finset_sum A.selected A.hat A.hat_lipschitz

theorem atlasSelectedVector_lipschitz : ∃ L : NNReal, LipschitzWith L (atlasSelectedVector A) := by
  apply exists_lipschitz_finset_sum
  intro v
  obtain ⟨L,hL⟩ := A.hat_lipschitz v
  let S : ℝ →L[ℝ] H := (1 : ℝ →L[ℝ] ℝ).smulRight (A.vertex v)
  refine ⟨‖S‖₊*L,?_⟩
  simpa only [S,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.one_apply] using S.lipschitz.comp hL

theorem atlasRetraction_near_lipschitz : ∀ x ∈ atlasRetractionDomain A,
    ∃ L : NNReal, ∃ S : Set H, S ∈ 𝓝 x ∧ LipschitzOnWith L (atlasRetraction A) S := by
  intro x hx
  have hden : atlasSelectedSum A x ≠ 0 := ne_of_gt hx.2
  obtain ⟨Ls,hs⟩ := atlasSelectedSum_lipschitz A
  obtain ⟨Lv,hv⟩ := atlasSelectedVector_lipschitz A
  let g : H → ℝ×H := fun y => (atlasSelectedSum A y,atlasSelectedVector A y)
  let φ : ℝ×H → H := fun p => p.1⁻¹ • p.2
  have hg : LipschitzWith (max Ls Lv) g := hs.prodMk hv
  have hφ : ContDiffAt ℝ 1 φ (g x) := (contDiffAt_fst.inv hden).smul contDiffAt_snd
  exact lipschitz_comp_contDiff_neighborhood g _ hg φ x hφ

include A in
theorem atlas_polyhedron_locally_strong_contractions :
    AdmitsLocallyStrongLipschitzContractions K.complex.space := by
  apply locally_strong_contractions_of_neighborhood_retraction K.complex.space (atlasRetraction A)
    (atlasRetraction_fixed A)
  intro x hx
  have hxU := atlasRetractionDomain_contains A hx
  obtain ⟨L,S,hS,hLip⟩ := atlasRetraction_near_lipschitz A x hxU
  have hBoth : S ∩ atlasRetractionDomain A ∈ 𝓝 x := inter_mem hS ((atlasRetractionDomain_isOpen A).mem_nhds hxU)
  obtain ⟨r,hr,hrS⟩ := Metric.mem_nhds_iff.mp hBoth
  exact ⟨r,hr,L,hLip.mono (fun _ h => (hrS h).1),
    fun y hy => atlasRetraction_mapsTo A (hrS hy).2⟩

end Paper28
