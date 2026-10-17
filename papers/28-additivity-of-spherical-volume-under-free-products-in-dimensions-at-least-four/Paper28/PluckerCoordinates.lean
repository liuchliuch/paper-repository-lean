import Paper28.CauchyBinetInput
import Paper28.IncidentJacobian
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Actual Euclidean exterior-coordinate vectors (ordered Plucker minors)
and their genuine Gram norm. This gives the oriented tangent vectors of
the strict tangent measures without an abstract Jacobian surrogate. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open scoped InnerProductSpace
open WithLp

abbrev EuclideanExterior (d k : ℕ) := EuclideanSpace ℝ (PluckerIndex d k)

def frameCoordinateMatrix {d k : ℕ} (e : Fin k → EuclideanSpace ℝ (Fin d)) :
    Matrix (Fin d) (Fin k) ℝ := fun i j => e j i

def pluckerCoordinates {d k : ℕ} (e : Fin k → EuclideanSpace ℝ (Fin d)) : EuclideanExterior d k :=
  toLp 2 (fun s => ((frameCoordinateMatrix e).submatrix (orderedMinorIndices s) id).det)

@[simp] theorem pluckerCoordinates_apply {d k : ℕ} (e : Fin k → EuclideanSpace ℝ (Fin d))
    (s : PluckerIndex d k) : pluckerCoordinates e s =
      ((frameCoordinateMatrix e).submatrix (orderedMinorIndices s) id).det := rfl

theorem gram_eq_frame_coordinate_mul {d k : ℕ} (e : Fin k → EuclideanSpace ℝ (Fin d)) :
    Matrix.gram ℝ e = (frameCoordinateMatrix e).transpose*frameCoordinateMatrix e := by
  ext i j
  simp only [Matrix.gram_apply,PiLp.inner_apply,RCLike.inner_apply,conj_trivial,Matrix.mul_apply,
    Matrix.transpose_apply,frameCoordinateMatrix]
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem pluckerCoordinates_norm_sq (hCB : CauchyBinetInput) {d k : ℕ}
    (e : Fin k → EuclideanSpace ℝ (Fin d)) :
    ‖pluckerCoordinates e‖^2 = (Matrix.gram ℝ e).det := by
  rw [EuclideanSpace.norm_sq_eq,gram_eq_frame_coordinate_mul,hCB]
  apply Finset.sum_congr rfl
  intro s _
  rw [pluckerCoordinates_apply,Real.norm_eq_abs,sq_abs]
  have ht : (frameCoordinateMatrix e).transpose.submatrix id (orderedMinorIndices s) =
      ((frameCoordinateMatrix e).submatrix (orderedMinorIndices s) id).transpose := rfl
  rw [ht,Matrix.det_transpose]
  ring

theorem pluckerCoordinates_norm_eq_gram (hCB : CauchyBinetInput) {d k : ℕ}
    (e : Fin k → EuclideanSpace ℝ (Fin d)) :
    ‖pluckerCoordinates e‖ = Real.sqrt (Matrix.gram ℝ e).det := by
  rw [← pluckerCoordinates_norm_sq hCB e,Real.sqrt_sq (norm_nonneg _)]

theorem pluckerCoordinates_norm_of_orthonormal (hCB : CauchyBinetInput) {d k : ℕ}
    (e : Fin k → EuclideanSpace ℝ (Fin d)) (he : Orthonormal ℝ e) :
    ‖pluckerCoordinates e‖ = 1 := by
  rw [pluckerCoordinates_norm_eq_gram hCB]
  have hg : Matrix.gram ℝ e = 1 := by
    ext i j
    exact orthonormal_iff_ite.mp he i j
  rw [hg,Matrix.det_one,Real.sqrt_one]

end Paper28
