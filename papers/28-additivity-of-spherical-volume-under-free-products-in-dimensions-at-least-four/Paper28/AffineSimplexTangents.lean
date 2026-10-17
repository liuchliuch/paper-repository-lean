import Paper28.ProjectiveAffineRank
import Paper28.CurrentLocalityInputs

/-! The actual support of an affine simplex integration lies in its
affine direction space, so standard rectifiable tangent locality applies. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open MeasureTheory Set
universe v

theorem affineSimplexPoint_sub_mem {d k : ℕ} (σ : AffineSimplexVertices d k)
    (x : EuclideanAmbient d) (hx : x ∈ convexHull ℝ (Set.range σ)) :
    x-σ 0 ∈ affineSimplexDirections σ := by
  rw [← affineSimplexPatch_eq_convexHull] at hx
  obtain ⟨t,rfl⟩ := hx
  have he : (∑ i, t.val i • σ i)-σ 0 = ∑ i, t.val i • (σ i-σ 0) := by
    simp only [smul_sub,Finset.sum_sub_distrib,← Finset.sum_smul,t.property.2,one_smul]
  rw [he]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self i)))

theorem affineSimplex_current_tangent_directions {d k : ℕ}
    (I : CompactIntegralCurrentAlgebraInput.{0,v} (EuclideanAmbient d) inferInstance)
    (R : EuclideanCurrentTangentInput d I) (T : EuclideanAffineSupportTangentInput I R)
    (S : EuclideanSimplexIntegrationInput d I) (σ : AffineSimplexVertices d k) :
    ∀ᵐ x ∂(R.massMeasure (S.integration k σ) : Measure (EuclideanAmbient d)),
      R.plane (S.integration k σ) x ≤ affineSimplexDirections σ :=
  T.affine_support_tangent (S.integration k σ) (σ 0) (affineSimplexDirections σ)
    (fun x hx => affineSimplexPoint_sub_mem σ x (S.support_subset k σ hx))

end Paper28
