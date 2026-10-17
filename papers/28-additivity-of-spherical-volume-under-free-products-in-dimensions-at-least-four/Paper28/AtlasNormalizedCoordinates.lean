import Paper28.BarycentricAtlasBranches

/-! The actual retained barycentric coordinates, including their exact
positive face and reconstruction of the neighborhood retraction. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
variable {H V Idx E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [DecidableEq H]
  [Fintype V] [DecidableEq V] [Fintype Idx]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {K : FiniteEuclideanComplex H} (A : FullSubcomplexBarycentricAtlas K V Idx)

def atlasCoordinates (x : H) (v : V) : ℝ :=
  if v ∈ A.selected then (atlasSelectedSum A x)⁻¹*A.hat v x else 0

theorem atlasCoordinates_nonneg (x : H) (hx : x ∈ atlasRetractionDomain A) (v : V) :
    0 ≤ atlasCoordinates A x v := by
  unfold atlasCoordinates
  split_ifs
  · exact mul_nonneg (inv_nonneg.mpr hx.2.le) (A.nonneg x hx.1 v)
  · exact le_rfl

theorem atlasCoordinates_sum (x : H) (hx : x ∈ atlasRetractionDomain A) :
    ∑ v, atlasCoordinates A x v = 1 := by
  classical
  calc
    _ = ∑ v ∈ A.selected, atlasCoordinates A x v :=
      (Finset.sum_subset (Finset.subset_univ _) (fun v _ hv => by simp [atlasCoordinates,hv])).symm
    _ = (atlasSelectedSum A x)⁻¹*atlasSelectedSum A x := by
      simp only [atlasCoordinates,Finset.sum_congr rfl (fun v hv => if_pos hv)]
      simp only [← Finset.mul_sum,atlasSelectedSum]
    _ = 1 := inv_mul_cancel₀ (ne_of_gt hx.2)

def atlasSimplexCoordinates (x : H) (hx : x ∈ atlasRetractionDomain A) : stdSimplex ℝ V :=
  ⟨atlasCoordinates A x,atlasCoordinates_nonneg A x hx,atlasCoordinates_sum A x hx⟩

theorem atlasCoordinates_weighted_sum (q : V → E) (x : H) :
    ∑ v, atlasCoordinates A x v • q v = (atlasSelectedSum A x)⁻¹ • atlasWeightedVector A q x := by
  classical
  calc
    _ = ∑ v ∈ A.selected, atlasCoordinates A x v • q v :=
      (Finset.sum_subset (Finset.subset_univ _) (fun v _ hv => by simp [atlasCoordinates,hv])).symm
    _ = _ := by
      rw [atlasWeightedVector,Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      simp only [atlasCoordinates,if_pos hv,mul_smul]

theorem atlasCoordinates_reconstruct (x : H) :
    ∑ v, atlasCoordinates A x v • A.vertex v = atlasRetraction A x := by
  classical
  calc
    _ = ∑ v ∈ A.selected, atlasCoordinates A x v • A.vertex v :=
      (Finset.sum_subset (Finset.subset_univ _) (fun v _ hv => by simp [atlasCoordinates,hv])).symm
    _ = _ := by
      rw [atlasRetraction,atlasSelectedVector,Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      simp only [atlasCoordinates,if_pos hv,mul_smul]

theorem atlasCoordinates_zero_off_cell (j : Idx) (x : H) (hx : x ∈ atlasCell A j)
    (v : V) (hv : v ∉ A.cells j ∩ A.selected) : atlasCoordinates A x v = 0 := by
  unfold atlasCoordinates
  split_ifs with h
  · rw [A.support_cell j x hx v (by intro hc; exact hv (Finset.mem_inter.mpr ⟨hc,h⟩)),mul_zero]
  · rfl

def atlasPositiveFace (x : H) : Finset V := by
  classical
  exact A.selected.filter (fun v => 0 < A.hat v x)

theorem atlasPositiveFace_subset (j : Idx) (x : H) (hx : x ∈ atlasCell A j) :
    atlasPositiveFace A x ⊆ A.cells j ∩ A.selected := by
  classical
  intro v hv
  obtain ⟨hv,hp⟩ := Finset.mem_filter.mp hv
  refine Finset.mem_inter.mpr ⟨?_,hv⟩
  by_contra h
  have hz := A.support_cell j x hx v h
  linarith

theorem atlasCoordinates_pos_iff (x : H) (hx : x ∈ atlasRetractionDomain A) (v : V) :
    0 < atlasCoordinates A x v ↔ v ∈ atlasPositiveFace A x := by
  classical
  by_cases hv : v ∈ A.selected
  · simp only [atlasCoordinates,atlasPositiveFace,Finset.mem_filter,hv,↓reduceIte,true_and]
    exact mul_pos_iff_of_pos_left (inv_pos.mpr hx.2)
  · simp [atlasCoordinates,atlasPositiveFace,hv]

end Paper28
