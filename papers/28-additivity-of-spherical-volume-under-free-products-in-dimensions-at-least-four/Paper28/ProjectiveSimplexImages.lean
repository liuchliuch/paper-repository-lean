import Paper28.NormalizedAffineMaps
import Paper28.SphericalSimplexPatch

/-! Normalization of an affine map sends every actual affine simplex
onto the spherical simplex spanned by the normalized vertex images.
The statement allows dependent vertices, so collapsed images are included. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem sphericalSimplexPatch_pos_smul_subset {k : ℕ} (v : Fin (k+1) → H)
    (a : Fin (k+1) → ℝ) (ha : ∀ i, 0 < a i) :
    sphericalSimplexPatch (fun i => a i • v i) ⊆ sphericalSimplexPatch v := by
  rintro u ⟨t,rfl⟩
  have ht : ∃ i, 0 < t.val i := by
    by_contra h
    push_neg at h
    have hh := Finset.sum_nonpos (s := Finset.univ) (fun i _ => h i)
    rw [t.property.2] at hh
    linarith
  let s := ∑ i, t.val i*a i
  have hs : 0 < s := by
    obtain ⟨i,hi⟩ := ht
    exact Finset.sum_pos' (fun j _ => mul_nonneg (t.property.1 j) (ha j).le)
      ⟨i,Finset.mem_univ _,mul_pos hi (ha i)⟩
  let w : stdSimplex ℝ (Fin (k+1)) := ⟨fun i => t.val i*a i/s,
    (fun i => div_nonneg (mul_nonneg (t.property.1 i) (ha i).le) hs.le),by
      rw [← Finset.sum_div]
      exact div_self (ne_of_gt hs)⟩
  refine ⟨w,?_⟩
  have hv : sphericalBarycentricVector (fun i => a i • v i) t =
      s • sphericalBarycentricVector v w := by
    simp only [sphericalBarycentricVector,Finset.smul_sum,smul_smul]
    apply Finset.sum_congr rfl
    intro i _
    change (t.val i*a i) • v i = (s*(t.val i*a i/s)) • v i
    congr 1
    field_simp
  change sphericalNormalize (sphericalBarycentricVector v w) =
    sphericalNormalize (sphericalBarycentricVector (fun i => a i • v i) t)
  rw [hv,sphericalNormalize_pos_smul s hs]

theorem sphericalSimplexPatch_pos_smul {k : ℕ} (v : Fin (k+1) → H)
    (a : Fin (k+1) → ℝ) (ha : ∀ i, 0 < a i) :
    sphericalSimplexPatch (fun i => a i • v i) = sphericalSimplexPatch v := by
  apply Subset.antisymm (sphericalSimplexPatch_pos_smul_subset v a ha)
  have h := sphericalSimplexPatch_pos_smul_subset (fun i => a i • v i)
    (fun i => (a i)⁻¹) (fun i => inv_pos.mpr (ha i))
  simpa only [smul_smul,inv_mul_cancel₀ (ne_of_gt (ha _)),one_smul] using h

theorem sphericalSimplexPatch_normalize_vertices {k : ℕ} (v : Fin (k+1) → H)
    (hv : ∀ i, v i ≠ 0) :
    sphericalSimplexPatch (fun i => sphericalNormalize (v i)) = sphericalSimplexPatch v := by
  exact sphericalSimplexPatch_pos_smul v (fun i => ‖v i‖⁻¹)
    (fun i => inv_pos.mpr (norm_pos_iff.mpr (hv i)))

def affineSimplexPatch {k : ℕ} (v : Fin (k+1) → E) : Set E :=
  Set.range (fun t : stdSimplex ℝ (Fin (k+1)) => ∑ i, t.val i • v i)

theorem affineSimplexPatch_eq_convexHull {k : ℕ} (v : Fin (k+1) → E) :
    affineSimplexPatch v = convexHull ℝ (Set.range v) := by
  let F : (Fin (k+1) → ℝ) →ₗ[ℝ] E := ∑ i, (LinearMap.proj i).smulRight (v i)
  have hF : F '' (Set.range (fun i : Fin (k+1) => Pi.single i (1 : ℝ))) = Set.range v := by
    rw [← Set.range_comp]
    congr 1
    funext i
    simp [F,LinearMap.sum_apply,LinearMap.smulRight_apply,LinearMap.proj_apply]
  rw [← hF,← LinearMap.image_convexHull,convexHull_rangle_single_eq_stdSimplex]
  apply Set.ext
  intro y
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨t.val,t.property,by simp [F,LinearMap.sum_apply,LinearMap.smulRight_apply,LinearMap.proj_apply]⟩
  · rintro ⟨t,ht,rfl⟩
    refine ⟨⟨t,ht⟩,?_⟩
    simp [F,LinearMap.sum_apply,LinearMap.smulRight_apply,LinearMap.proj_apply]

theorem normalizedAffineMap_simplex_image {k : ℕ} (L : E →L[ℝ] H) (b : H)
    (v : Fin (k+1) → E) (hv : ∀ i, L (v i)+b ≠ 0) :
    normalizedAffineMap L b '' affineSimplexPatch v =
      sphericalSimplexPatch (fun i => normalizedAffineMap L b (v i)) := by
  rw [show (fun i => normalizedAffineMap L b (v i)) =
    (fun i => sphericalNormalize (L (v i)+b)) from rfl,
    sphericalSimplexPatch_normalize_vertices _ hv]
  apply Set.ext
  intro y
  constructor
  · rintro ⟨x,⟨t,rfl⟩,rfl⟩
    refine ⟨t,?_⟩
    unfold normalizedAffineMap
    rw [affineMap_barycentric]
    rfl
  · rintro ⟨t,rfl⟩
    refine ⟨∑ i, t.val i • v i,⟨t,rfl⟩,?_⟩
    unfold normalizedAffineMap
    rw [affineMap_barycentric]
    rfl

end Paper28
