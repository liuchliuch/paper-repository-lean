import Paper28.RelativeNormalization

/-! Equivariance of the actual weighted projection, normalization and
relative straight homotopy, derived from equivariant chart weights/projections
and the permutation of their indices. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
variable {J H : Type*} [Fintype J] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem sphericalNormalize_map (A : H ≃ₗᵢ[ℝ] H) (u : H) :
    sphericalNormalize (A u) = A (sphericalNormalize u) := by
  simp only [sphericalNormalize, A.norm_map, map_smul]

theorem weightedProjection_equivariant (φ : J → H → ℝ) (P : J → H →L[ℝ] H)
    (e : J ≃ J) (A : H ≃ₗᵢ[ℝ] H) (u : H)
    (hφ : ∀ j, φ j (A u) = φ (e j) u)
    (hP : ∀ j, P j (A u) = A (P (e j) u)) :
    weightedProjection φ P (A u) = A (weightedProjection φ P u) := by
  unfold weightedProjection
  simp_rw [hφ,hP,← map_smul]
  rw [← map_sum]
  apply congrArg A
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem normalizedProjection_equivariant (φ : J → H → ℝ) (P : J → H →L[ℝ] H)
    (e : J ≃ J) (A : H ≃ₗᵢ[ℝ] H) (u : H)
    (hφ : ∀ j, φ j (A u) = φ (e j) u)
    (hP : ∀ j, P j (A u) = A (P (e j) u)) :
    normalizedProjection φ P (A u) = A (normalizedProjection φ P u) := by
  unfold normalizedProjection
  rw [weightedProjection_equivariant φ P e A u hφ hP, sphericalNormalize_map]

theorem projectionHomotopy_equivariant (φ : J → H → ℝ) (P : J → H →L[ℝ] H)
    (e : J ≃ J) (A : H ≃ₗᵢ[ℝ] H) (u : H) (t : ℝ)
    (hφ : ∀ j, φ j (A u) = φ (e j) u)
    (hP : ∀ j, P j (A u) = A (P (e j) u)) :
    projectionHomotopy φ P t (A u) = A (projectionHomotopy φ P t u) := by
  unfold projectionHomotopy projectionHomotopyRaw
  rw [weightedProjection_equivariant φ P e A u hφ hP, ← map_smul, ← map_smul,
    ← map_add, sphericalNormalize_map]

end Paper28
