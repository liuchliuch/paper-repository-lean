import Paper28.FiniteEuclideanComplex
import Mathlib.Topology.MetricSpace.Lipschitz

/-! Standard full-subcomplex barycentric coordinate data and the actual
deleting-and-renormalizing neighborhood retraction. The data contains only
triangulation coordinates and incidence, never a retraction conclusion. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
variable {H V Idx : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [DecidableEq H]
  [Fintype V] [DecidableEq V] [Fintype Idx]

structure FullSubcomplexBarycentricAtlas [DecidableEq H] (K : FiniteEuclideanComplex H) (V Idx : Type*)
    [Fintype V] [DecidableEq V] [Fintype Idx] where
  vertex : V → H
  selected : Finset V
  cells : Idx → Finset V
  hat : V → H → ℝ
  hat_lipschitz : ∀ v, ∃ L : NNReal, LipschitzWith L (hat v)
  domain : Set H
  domain_open : IsOpen domain
  contains : K.complex.space ⊆ domain
  cover : domain ⊆ ⋃ j, convexHull ℝ (vertex '' (cells j : Set V))
  nonneg : ∀ x ∈ domain, ∀ v, 0 ≤ hat v x
  sum_one : ∀ x ∈ domain, ∑ v, hat v x = 1
  reconstruct : ∀ x ∈ domain, ∑ v, hat v x • vertex v = x
  support_cell : ∀ j, ∀ x ∈ convexHull ℝ (vertex '' (cells j : Set V)), ∀ v ∉ cells j, hat v x = 0
  zero_off_selected : ∀ x ∈ K.complex.space, ∀ v ∉ selected, hat v x = 0
  full_face : ∀ j, (cells j ∩ selected).Nonempty → (cells j ∩ selected).image vertex ∈ K.complex.faces
  slope : Idx → V → H →L[ℝ] ℝ
  offset : Idx → V → ℝ
  coordinate_on_cell : ∀ j, ∀ x ∈ convexHull ℝ (vertex '' (cells j : Set V)), ∀ v,
    hat v x = slope j v x+offset j v

variable {K : FiniteEuclideanComplex H} (A : FullSubcomplexBarycentricAtlas K V Idx)

def atlasSelectedSum (x : H) : ℝ := ∑ v ∈ A.selected, A.hat v x
def atlasSelectedVector (x : H) : H := ∑ v ∈ A.selected, A.hat v x • A.vertex v
def atlasRetraction (x : H) : H := (atlasSelectedSum A x)⁻¹ • atlasSelectedVector A x
def atlasRetractionDomain : Set H := A.domain ∩ {x | 0 < atlasSelectedSum A x}

theorem atlasSelectedSum_continuous : Continuous (atlasSelectedSum A) :=
  continuous_finset_sum _ (fun v _ => (A.hat_lipschitz v).choose_spec.continuous)

theorem atlasRetractionDomain_isOpen : IsOpen (atlasRetractionDomain A) :=
  A.domain_open.inter (isOpen_lt continuous_const (atlasSelectedSum_continuous A))

theorem atlasSelectedSum_eq_one (x : H) (hx : x ∈ K.complex.space) : atlasSelectedSum A x = 1 := by
  classical
  calc
    _ = ∑ v : V, A.hat v x := Finset.sum_subset (Finset.subset_univ _)
      (fun v _ hv => A.zero_off_selected x hx v hv)
    _ = 1 := A.sum_one x (A.contains hx)

theorem atlasSelectedVector_eq (x : H) (hx : x ∈ K.complex.space) : atlasSelectedVector A x = x := by
  classical
  calc
    _ = ∑ v : V, A.hat v x • A.vertex v := Finset.sum_subset (Finset.subset_univ _)
      (fun v _ hv => by rw [A.zero_off_selected x hx v hv,zero_smul])
    _ = x := A.reconstruct x (A.contains hx)

theorem atlasRetractionDomain_contains : K.complex.space ⊆ atlasRetractionDomain A := by
  intro x hx
  refine ⟨A.contains hx,?_⟩
  change 0 < atlasSelectedSum A x
  rw [atlasSelectedSum_eq_one A x hx]
  norm_num

theorem atlasRetraction_fixed (x : H) (hx : x ∈ K.complex.space) : atlasRetraction A x = x := by
  rw [atlasRetraction,atlasSelectedSum_eq_one A x hx,atlasSelectedVector_eq A x hx,inv_one,one_smul]

theorem atlasRetraction_mapsTo : MapsTo (atlasRetraction A) (atlasRetractionDomain A) K.complex.space := by
  classical
  intro x hx
  change x ∈ A.domain ∧ 0 < atlasSelectedSum A x at hx
  obtain ⟨j,hj⟩ := mem_iUnion.mp (A.cover hx.1)
  let F := A.cells j ∩ A.selected
  have hF : F.Nonempty := by
    by_contra h
    have hzero : atlasSelectedSum A x = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      exact A.support_cell j x hj v (by
        intro hvCell
        exact h ⟨v,Finset.mem_inter.mpr ⟨hvCell,hv⟩⟩)
    rw [hzero] at hx
    exact lt_irrefl _ hx.2
  have hFace : F.image A.vertex ∈ K.complex.faces := A.full_face j hF
  apply K.complex.convexHull_subset_space hFace
  have hSum : (∑ v ∈ F, A.hat v x) = atlasSelectedSum A x := by
    apply Finset.sum_subset (Finset.inter_subset_right)
    intro v hv hvF
    exact A.support_cell j x hj v (by intro hvCell; exact hvF (Finset.mem_inter.mpr ⟨hvCell,hv⟩))
  have hVector : (∑ v ∈ F, A.hat v x • A.vertex v) = atlasSelectedVector A x := by
    apply Finset.sum_subset Finset.inter_subset_right
    intro v hv hvF
    rw [A.support_cell j x hj v (by intro hvCell; exact hvF (Finset.mem_inter.mpr ⟨hvCell,hv⟩)),zero_smul]
  change (atlasSelectedSum A x)⁻¹ • atlasSelectedVector A x ∈ convexHull ℝ (F.image A.vertex : Set H)
  rw [← hVector,Finset.smul_sum]
  simp_rw [smul_smul]
  apply (convex_convexHull ℝ _).sum_mem
  · intro v _
    exact mul_nonneg (inv_nonneg.mpr hx.2.le) (A.nonneg x hx.1 v)
  · rw [← Finset.mul_sum,hSum]
    exact inv_mul_cancel₀ (ne_of_gt hx.2)
  · intro v hv
    exact subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨v,hv,rfl⟩)

end Paper28
