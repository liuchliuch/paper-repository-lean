import Paper28.NormalizedAffineMatrices
import Paper28.ProjectiveSimplexImages
import Paper28.RankDeficientJacobian

/-! The actual differential loses dimension when the raw spherical
vertices are linearly dependent. Restriction to the actual affine simplex
directions is essential: the ambient extension need not lose rank. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
open scoped InnerProductSpace
variable {d m k : ℕ}

def affineSimplexDirections (σ : AffineSimplexVertices d k) : Submodule ℝ (EuclideanAmbient d) :=
  Submodule.span ℝ (Set.range (fun i => σ i-σ 0))

def affineRawSpan (L : EuclideanAmbient d →L[ℝ] EuclideanAmbient m) (b : EuclideanAmbient m)
    (σ : AffineSimplexVertices d k) : Submodule ℝ (EuclideanAmbient m) :=
  Submodule.span ℝ (Set.range (fun i => L (σ i)+b))

theorem normalizationDerivative_inner_zero (u h : EuclideanAmbient m) (hu : u ≠ 0) :
    inner ℝ u (normalizationDerivative u h) = 0 := by
  rw [normalizationDerivative_apply,real_inner_smul_right,inner_sub_right,
    real_inner_smul_right,real_inner_self_eq_norm_sq]
  field_simp [norm_ne_zero_iff.mpr hu]
  <;> ring

theorem affineRawSpan_mem_point (L : EuclideanAmbient d →L[ℝ] EuclideanAmbient m)
    (b : EuclideanAmbient m) (σ : AffineSimplexVertices d k) (x : EuclideanAmbient d)
    (hx : x ∈ convexHull ℝ (Set.range σ)) : L x+b ∈ affineRawSpan L b σ := by
  rw [← affineSimplexPatch_eq_convexHull] at hx
  obtain ⟨t,rfl⟩ := hx
  rw [affineMap_barycentric]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self i)))

theorem affineRawSpan_mem_direction (L : EuclideanAmbient d →L[ℝ] EuclideanAmbient m)
    (b : EuclideanAmbient m) (σ : AffineSimplexVertices d k) (h : EuclideanAmbient d)
    (hh : h ∈ affineSimplexDirections σ) : L h ∈ affineRawSpan L b σ := by
  have hS : affineSimplexDirections σ ≤ (affineRawSpan L b σ).comap L.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro v ⟨i,rfl⟩
    change L (σ i-σ 0) ∈ affineRawSpan L b σ
    have he : L (σ i-σ 0) = (L (σ i)+b)-(L (σ 0)+b) := by rw [map_sub]; abel
    rw [he]
    exact Submodule.sub_mem _ (Submodule.subset_span (mem_range_self i)) (Submodule.subset_span (mem_range_self 0))
  exact hS hh

theorem affineRawSpan_dim_of_dependent (L : EuclideanAmbient d →L[ℝ] EuclideanAmbient m)
    (b : EuclideanAmbient m) (σ : AffineSimplexVertices d k)
    (hDep : ¬ LinearIndependent ℝ (fun i => L (σ i)+b)) : Module.finrank ℝ (affineRawSpan L b σ) ≤ k := by
  have hUpper : Module.finrank ℝ (affineRawSpan L b σ) ≤ k+1 := by
    simpa only [affineRawSpan,Fintype.card_fin] using (finrank_range_le_card (R := ℝ) (fun i => L (σ i)+b))
  have hNe : Module.finrank ℝ (affineRawSpan L b σ) ≠ k+1 := by
    intro he
    apply hDep
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    simpa only [Fintype.card_fin] using he.symm
  omega

theorem normalizedAffineDerivative_rank_drop
    (L : EuclideanAmbient d →L[ℝ] EuclideanAmbient m) (b : EuclideanAmbient m)
    (σ : AffineSimplexVertices d k) (x : EuclideanAmbient d)
    (hx : x ∈ convexHull ℝ (Set.range σ)) (hx0 : L x+b ≠ 0)
    (hDep : ¬ LinearIndependent ℝ (fun i => L (σ i)+b)) :
    ∃ W : Submodule ℝ (EuclideanAmbient m), Module.finrank ℝ W < k ∧
      ∀ h ∈ affineSimplexDirections σ, normalizedAffineDerivative L b x h ∈ W := by
  let S := affineRawSpan L b σ
  let u := L x+b
  let W := S ⊓ LinearMap.ker (innerSL ℝ u).toLinearMap
  have huS : u ∈ S := affineRawSpan_mem_point L b σ x hx
  have huW : u ∉ W := by
    intro hu
    have he : inner ℝ u u = 0 := hu.2
    exact hx0 (inner_self_eq_zero.mp he)
  have hlt : W < S := lt_of_le_of_ne inf_le_left (by
    intro he
    exact huW (he.symm ▸ huS))
  have hdim : Module.finrank ℝ W < k :=
    (Submodule.finrank_lt_finrank_of_lt hlt).trans_le (affineRawSpan_dim_of_dependent L b σ hDep)
  refine ⟨W,hdim,?_⟩
  intro h hh
  change normalizationDerivative u (L h) ∈ S ⊓ LinearMap.ker (innerSL ℝ u).toLinearMap
  constructor
  · rw [normalizationDerivative_apply]
    exact S.smul_mem _ (S.sub_mem (affineRawSpan_mem_direction L b σ h hh) (S.smul_mem _ huS))
  · exact normalizationDerivative_inner_zero u (L h) hx0

end Paper28
