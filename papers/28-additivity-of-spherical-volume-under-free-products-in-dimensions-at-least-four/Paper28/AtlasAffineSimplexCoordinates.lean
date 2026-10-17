import Paper28.BarycentricAtlasBranches
import Paper28.AtlasNormalizedCoordinates
import Paper28.ProjectiveSimplexImages
import Paper28.EuclideanPolyhedralCurrents

/-! Actual affine coordinate identities and the constant relative image
face of the interior of a subdivided ambient simplex. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
variable {V Idx : Type*} [Fintype V] [DecidableEq V] [Fintype Idx]
  {d k : ℕ} {K : FiniteEuclideanComplex (EuclideanAmbient d)}
  (A : FullSubcomplexBarycentricAtlas K V Idx)

theorem atlas_hat_on_affine_simplex (j : Idx) (σ : AffineSimplexVertices d k)
    (hσ : convexHull ℝ (Set.range σ) ⊆ atlasCell A j)
    (t : stdSimplex ℝ (Fin (k+1))) (v : V) :
    A.hat v (∑ i, t.val i • σ i) = ∑ i, t.val i*A.hat v (σ i) := by
  have hx : (∑ i, t.val i • σ i) ∈ atlasCell A j :=
    hσ ((affineSimplexPatch_eq_convexHull σ).subset ⟨t,rfl⟩)
  rw [A.coordinate_on_cell j _ hx,affineMap_barycentric]
  apply Finset.sum_congr rfl
  intro i _
  rw [A.coordinate_on_cell j (σ i) (hσ (subset_convexHull ℝ _ (mem_range_self i))) v]
  rfl

theorem atlas_hat_positive_interior (j : Idx) (σ : AffineSimplexVertices d k)
    (hσ : convexHull ℝ (Set.range σ) ⊆ atlasRetractionDomain A ∩ atlasCell A j)
    (t : stdSimplex ℝ (Fin (k+1))) (ht : ∀ i, 0 < t.val i) (v : V) :
    0 < A.hat v (∑ i, t.val i • σ i) ↔ ∃ i, 0 < A.hat v (σ i) := by
  rw [atlas_hat_on_affine_simplex A j σ (fun _ hx => (hσ hx).2) t v]
  have hn : ∀ i, 0 ≤ A.hat v (σ i) := fun i =>
    A.nonneg (σ i) (hσ (subset_convexHull ℝ _ (mem_range_self i))).1.1 v
  constructor
  · intro h
    by_contra he
    push_neg at he
    have hs : (∑ i, t.val i*A.hat v (σ i)) ≤ 0 :=
      Finset.sum_nonpos (fun i _ => mul_nonpos_of_nonneg_of_nonpos (ht i).le (he i))
    linarith
  · rintro ⟨i,hi⟩
    exact Finset.sum_pos' (fun a _ => mul_nonneg (ht a).le (hn a))
      ⟨i,Finset.mem_univ _,mul_pos (ht i) hi⟩

def atlasSimplexImageFace (σ : AffineSimplexVertices d k) : Finset V := by
  classical
  exact Finset.univ.biUnion (fun i => atlasPositiveFace A (σ i))

theorem atlasPositiveFace_interior (j : Idx) (σ : AffineSimplexVertices d k)
    (hσ : convexHull ℝ (Set.range σ) ⊆ atlasRetractionDomain A ∩ atlasCell A j)
    (t : stdSimplex ℝ (Fin (k+1))) (ht : ∀ i, 0 < t.val i) :
    atlasPositiveFace A (∑ i, t.val i • σ i) = atlasSimplexImageFace A σ := by
  classical
  apply Finset.ext
  intro v
  change (v ∈ A.selected.filter (fun v => 0 < A.hat v (∑ i, t.val i • σ i))) ↔
    v ∈ Finset.univ.biUnion (fun i => A.selected.filter (fun v => 0 < A.hat v (σ i)))
  simp only [Finset.mem_filter,Finset.mem_biUnion,Finset.mem_univ,true_and]
  rw [atlas_hat_positive_interior A j σ hσ t ht v]
  constructor
  · rintro ⟨hv,i,hi⟩
    exact ⟨i,hv,hi⟩
  · rintro ⟨i,hv,hi⟩
    exact ⟨hv,i,hi⟩

end Paper28
