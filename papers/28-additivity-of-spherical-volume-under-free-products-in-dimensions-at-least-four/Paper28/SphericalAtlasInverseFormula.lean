import Paper28.SphericalVertexReconstruction
import Paper28.SphericalCellPathMetric
import Paper28.NeighborhoodPushforwardInput

/-! Explicit inverse barycentric operators on each actual spherical cell.
Independence of its vertex vectors is the defining nondegeneracy of the
original spherical cell, not a Lipschitz or current estimate. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
universe w
variable {V Idx : Type*} [Fintype V] [DecidableEq V] [Fintype Idx]
  {d : ℕ} {K : FiniteEuclideanComplex (EuclideanAmbient d)}
  {B : FullSubcomplexBarycentricAtlas K V Idx} {Y : Type w} [MetricSpace Y]
variable (C : FullSubcomplexSphericalCharts B Y)

abbrev CellVertexIndependence : Prop :=
  ∀ j, LinearIndependent ℝ (fun v : {v : V // v ∈ B.cells j ∩ B.selected} => C.vertex j v.val)

variable (hQ : CellVertexIndependence C)

def atlasCellReconstruction (j : Idx) : EuclideanAmbient (C.dimension j) →L[ℝ] EuclideanAmbient d :=
  vertexReconstructionLinear (fun v : {v : V // v ∈ B.cells j ∩ B.selected} => C.vertex j v.val)
    (hQ j) (fun v => B.vertex v.val)

def atlasCellSumFunctional (j : Idx) : EuclideanAmbient (C.dimension j) →L[ℝ] ℝ :=
  vertexReconstructionLinear (fun v : {v : V // v ∈ B.cells j ∩ B.selected} => C.vertex j v.val)
    (hQ j) (fun _ => (1 : ℝ))

def atlasCellInverse (j : Idx) : EuclideanAmbient (C.dimension j) → EuclideanAmbient d :=
  affineProjectiveReconstruction (atlasCellReconstruction C hQ j) (atlasCellSumFunctional C hQ j)

theorem atlasCellReconstruction_vertex (j : Idx) (v : V) (hv : v ∈ B.cells j ∩ B.selected) :
    atlasCellReconstruction C hQ j (C.vertex j v) = B.vertex v := by
  exact vertexReconstructionLinear_vertex
    (fun w : {v : V // v ∈ B.cells j ∩ B.selected} => C.vertex j w.val) (hQ j)
    (fun w => B.vertex w.val) ⟨v,hv⟩

theorem atlasCellSumFunctional_vertex (j : Idx) (v : V) (hv : v ∈ B.cells j ∩ B.selected) :
    atlasCellSumFunctional C hQ j (C.vertex j v) = 1 := by
  exact vertexReconstructionLinear_vertex
    (fun w : {v : V // v ∈ B.cells j ∩ B.selected} => C.vertex j w.val) (hQ j)
    (fun _ => (1 : ℝ)) ⟨v,hv⟩

theorem atlasCellSumFunctional_combination (j : Idx) (t : stdSimplex ℝ V)
    (ht : ∀ v, v ∉ B.cells j ∩ B.selected → t.val v = 0) :
    atlasCellSumFunctional C hQ j (∑ v, t.val v • C.vertex j v) = 1 := by
  rw [map_sum]
  have he : (∑ v, atlasCellSumFunctional C hQ j (t.val v • C.vertex j v)) = ∑ v, t.val v := by
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : v ∈ B.cells j ∩ B.selected
    · rw [map_smul,atlasCellSumFunctional_vertex C hQ j v hv,smul_eq_mul,mul_one]
    · rw [ht v hv,zero_smul,map_zero]
  rw [he,t.property.2]

theorem atlasCellReconstruction_combination (j : Idx) (t : stdSimplex ℝ V)
    (ht : ∀ v, v ∉ B.cells j ∩ B.selected → t.val v = 0) :
    atlasCellReconstruction C hQ j (∑ v, t.val v • C.vertex j v) = ∑ v, t.val v • B.vertex v := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v ∈ B.cells j ∩ B.selected
  · rw [map_smul,atlasCellReconstruction_vertex C hQ j v hv]
  · rw [ht v hv,zero_smul,zero_smul,map_zero]

theorem atlasCellSumFunctional_positive (j : Idx) (u : EuclideanAmbient (C.dimension j))
    (hu : u ∈ closedSphericalPatch (C.vertex j) (B.cells j ∩ B.selected)) :
    0 < atlasCellSumFunctional C hQ j u := by
  obtain ⟨t,ht,rfl⟩ := hu
  have he := atlasCellSumFunctional_combination C hQ j t ht
  have hn : (∑ v, t.val v • C.vertex j v) ≠ 0 := by
    intro h
    rw [h,map_zero] at he
    exact zero_ne_one he
  rw [sphericalNormalize,map_smul,he,smul_eq_mul,mul_one]
  exact inv_pos.mpr (norm_pos_iff.mpr hn)

theorem atlasCellInverse_formula (j : Idx) (u : EuclideanAmbient (C.dimension j))
    (hu : u ∈ closedSphericalPatch (C.vertex j) (B.cells j ∩ B.selected)) :
    atlasCellInverse C hQ j u = (C.homeomorph.symm (C.chart j u)).val := by
  obtain ⟨t,ht,rfl⟩ := hu
  have he := atlasCellSumFunctional_combination C hQ j t ht
  rw [atlasCellInverse,affineProjectiveReconstruction_normalized _ _ _ he,
    atlasCellReconstruction_combination C hQ j t ht]
  let x : K.complex.space := ⟨∑ v, t.val v • B.vertex v,atlasFacePoint_mem B j t ht⟩
  have hx := C.barycentric_formula j t ht x rfl
  rw [← hx,C.homeomorph.symm_apply_apply]

include hQ in
theorem closedSphericalPatch_isCompact (j : Idx) :
    IsCompact (closedSphericalPatch (C.vertex j) (B.cells j ∩ B.selected)) := by
  let T : Set (stdSimplex ℝ V) := {t | ∀ v, v ∉ B.cells j ∩ B.selected → t.val v = 0}
  have hT : IsClosed T := by
    simp only [T,setOf_forall]
    exact isClosed_iInter (fun v => isClosed_iInter (fun _ => isClosed_eq
      ((continuous_apply v).comp continuous_subtype_val) continuous_const))
  have hRaw : Continuous (fun t : stdSimplex ℝ V => ∑ v, t.val v • C.vertex j v) :=
    continuous_finset_sum _ (fun v _ => ((continuous_apply v).comp continuous_subtype_val).smul continuous_const)
  have hCont : ContinuousOn (fun t : stdSimplex ℝ V => sphericalNormalize (∑ v, t.val v • C.vertex j v)) T := by
    intro t ht
    have he := atlasCellSumFunctional_combination C hQ j t ht
    have hn : (∑ v, t.val v • C.vertex j v) ≠ 0 := by
      intro h
      rw [h,map_zero] at he
      exact zero_ne_one he
    exact ((sphericalNormalize_contDiffAt _ hn 1).continuousAt.comp
      (f := fun t : stdSimplex ℝ V => ∑ v, t.val v • C.vertex j v) hRaw.continuousAt).continuousWithinAt
  have hImage : (fun t : stdSimplex ℝ V => sphericalNormalize (∑ v, t.val v • C.vertex j v)) '' T =
      closedSphericalPatch (C.vertex j) (B.cells j ∩ B.selected) := by
    apply Set.ext
    intro u
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨t,ht,rfl⟩
    · rintro ⟨t,ht,rfl⟩
      exact ⟨t,ht,rfl⟩
  rw [← hImage]
  exact hT.isCompact.image_of_continuousOn hCont

theorem atlasCellInverse_lipschitz (j : Idx) :
    ∃ L : NNReal, LipschitzOnWith L (atlasCellInverse C hQ j)
      (closedSphericalPatch (C.vertex j) (B.cells j ∩ B.selected)) := by
  let U := {u | atlasCellSumFunctional C hQ j u ≠ 0}
  have hf : LipschitzNearSet inferInstance inferInstance (atlasCellInverse C hQ j) U :=
    fun u hu => affineProjectiveReconstruction_near_lipschitz _ _ u hu
  obtain ⟨L,hL⟩ := LipschitzNearSet.compact_restrict (atlasCellInverse C hQ j) U
    (closedSphericalPatch (C.vertex j) (B.cells j ∩ B.selected)) hf
    (fun u hu => ne_of_gt (atlasCellSumFunctional_positive C hQ j u hu)) (closedSphericalPatch_isCompact C hQ j)
  exact ⟨L,LipschitzOnWith.of_dist_le_mul (fun u hu v hv => hL.dist_le_mul ⟨u,hu⟩ ⟨v,hv⟩)⟩

end Paper28
