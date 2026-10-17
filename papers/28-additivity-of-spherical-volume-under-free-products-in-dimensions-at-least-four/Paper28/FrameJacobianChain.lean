import Paper28.JacobianChain

/-! Functional form of the full-dimensional chain rule through the actual
linear image, and the rank-deficient zero case. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ G]

theorem frameJacobian_comp_range (D : E →ₗ[ℝ] F) (A : F →ₗ[ℝ] G)
    (hD : Function.Injective D) :
    frameJacobian (fun x => A (D x)) =
      frameJacobian (fun v : LinearMap.range D => A v.val) * frameJacobian D := by
  change frameJacobian (A.comp D) =
    frameJacobian (A.comp (LinearMap.range D).subtype) * frameJacobian D
  simp only [frameJacobian_eq_linearJacobian]
  exact linearJacobian_comp_range D A hD

theorem frameJacobian_comp_of_not_injective (D : E →ₗ[ℝ] F) (A : F →ₗ[ℝ] G)
    (hD : ¬ Function.Injective D) : frameJacobian (fun x => A (D x)) = 0 := by
  change frameJacobian (A.comp D) = 0
  rw [frameJacobian_eq_linearJacobian]
  exact linearJacobian_comp_of_not_injective D A hD

end Paper28
