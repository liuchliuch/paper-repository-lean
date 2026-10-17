import Paper28.NJacobian

/-! Generic full-dimensional contraction bound, using the disclosed
classical Fischer inequality with an actual two-dimensional Gram block. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open scoped InnerProductSpace
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ E]

theorem linearMap_preservesFrameSums (D : E →ₗ[ℝ] F) : PreservesFrameSums D := by
  intro v a
  simp only [map_sum, map_smul]

/-- The genuine n-dimensional Gram Jacobian of a contraction is at most one. -/
theorem frameJacobian_contraction (hFischer : FischerInput) (f : E → F)
    (hf : PreservesFrameSums f) (hNorm : ∀ v, ‖f v‖ ≤ ‖v‖)
    (hn : 2 ≤ Module.finrank ℝ E) : frameJacobian f ≤ 1 := by
  classical
  let b := stdOrthonormalBasis ℝ E
  let e := fun i : Fin 2 => b (twoFrameEmbedding hn i)
  have he : Orthonormal ℝ e := b.orthonormal.comp (twoFrameEmbedding hn) (twoFrameEmbedding hn).injective
  have hbound := frameJacobian_le_two_frame hFischer f hf hNorm e he hn
  have hn0 : ‖f (e 0)‖ ≤ 1 := by simpa [he.norm_eq_one 0] using hNorm (e 0)
  have hn1 : ‖f (e 1)‖ ≤ 1 := by simpa [he.norm_eq_one 1] using hNorm (e 1)
  have hdet : (Matrix.gram ℝ (fun i => f (e i))).det ≤ 1 := by
    rw [Matrix.det_fin_two]
    simp only [Matrix.gram_apply, real_inner_self_eq_norm_sq, real_inner_comm (f (e 1)) (f (e 0))]
    have h0 : ‖f (e 0)‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (f (e 0))]
    have h1 : ‖f (e 1)‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (f (e 1))]
    have hp : ‖f (e 0)‖ ^ 2 * ‖f (e 1)‖ ^ 2 ≤ 1 := by
      calc
        _ ≤ 1 * ‖f (e 1)‖ ^ 2 := mul_le_mul_of_nonneg_right h0 (sq_nonneg _)
        _ ≤ 1 := by simpa using h1
    nlinarith [sq_nonneg ⟪f (e 0), f (e 1)⟫_ℝ]
  exact hbound.trans ((Real.sqrt_le_sqrt hdet).trans_eq Real.sqrt_one)

end Paper28
