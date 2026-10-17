import Paper28.NormalizedAffineMaps
import Paper28.EuclideanAreaInput

/-! Matrix coordinates of the actual Frechet derivative of a normalized
affine lift. Continuity is derived from smoothness, rather than supplied
as a separate geometry or mass premise. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
variable {d m : ℕ}

def euclideanCLMMatrixLinear :
    (EuclideanAmbient d →L[ℝ] EuclideanAmbient m) →ₗ[ℝ] Matrix (Fin m) (Fin d) ℝ :=
  Matrix.toEuclideanLin.symm.toLinearMap.comp (ContinuousLinearMap.coeLM ℝ)

theorem euclideanCLMMatrixLinear_continuous :
    Continuous (euclideanCLMMatrixLinear (d := d) (m := m)) :=
  LinearMap.continuous_of_finiteDimensional _

theorem euclideanCLMMatrixLinear_inverse (L : EuclideanAmbient d →L[ℝ] EuclideanAmbient m) :
    (Matrix.toEuclideanLin (euclideanCLMMatrixLinear L)).toContinuousLinearMap = L := by
  have he : Matrix.toEuclideanLin (euclideanCLMMatrixLinear L) = L.toLinearMap :=
    LinearEquiv.apply_symm_apply _ _
  apply ContinuousLinearMap.ext
  intro x
  exact congrArg (fun Q : EuclideanAmbient d →ₗ[ℝ] EuclideanAmbient m => Q x) he

def normalizedAffineMatrix (L : EuclideanAmbient d →L[ℝ] EuclideanAmbient m)
    (b : EuclideanAmbient m) (x : EuclideanAmbient d) : Matrix (Fin m) (Fin d) ℝ :=
  euclideanCLMMatrixLinear (fderiv ℝ (normalizedAffineMap L b) x)

theorem normalizedAffineMatrix_derivative (L : EuclideanAmbient d →L[ℝ] EuclideanAmbient m)
    (b : EuclideanAmbient m) (x : EuclideanAmbient d) (hx : L x+b ≠ 0) :
    HasFDerivAt (normalizedAffineMap L b)
      (Matrix.toEuclideanLin (normalizedAffineMatrix L b x)).toContinuousLinearMap x := by
  rw [normalizedAffineMatrix,euclideanCLMMatrixLinear_inverse]
  exact (normalizedAffineMap_hasFDerivAt L b x hx).differentiableAt.hasFDerivAt

theorem normalizedAffineMatrix_continuousOn (L : EuclideanAmbient d →L[ℝ] EuclideanAmbient m)
    (b : EuclideanAmbient m) (Q : Set (EuclideanAmbient d)) (hQ : ∀ x ∈ Q, L x+b ≠ 0) :
    ContinuousOn (normalizedAffineMatrix L b) Q := by
  intro x hx
  have hf : ContinuousAt (fderiv ℝ (normalizedAffineMap L b)) x :=
    ((normalizedAffineMap_contDiffAt L b x (hQ x hx) 1).fderiv_right (m := 0) (by simp)).continuousAt
  exact (euclideanCLMMatrixLinear_continuous.continuousAt.comp hf).continuousWithinAt

end Paper28
