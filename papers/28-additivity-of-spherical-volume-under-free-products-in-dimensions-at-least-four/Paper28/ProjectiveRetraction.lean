import Paper28.Normalization
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! The actual deleting-and-renormalizing projective retraction formula.
Here P deletes the complementary barycentric coordinates and ell sums the
retained coordinates. Its derivative on every retained face direction is
proved to be the identity. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def projectiveRetraction (P : E →L[ℝ] E) (ell : E →L[ℝ] ℝ) (u : E) : E :=
  (ell u)⁻¹ • P u

def projectiveRetractionDerivative (P : E →L[ℝ] E) (ell : E →L[ℝ] ℝ) (u : E) : E →L[ℝ] E :=
  (ell u)⁻¹ • P - ((ell u)⁻¹)^2 • ell.smulRight (P u)

theorem projectiveRetraction_fixed (P : E →L[ℝ] E) (ell : E →L[ℝ] ℝ)
    (u : E) (hP : P u = u) (hEll : ell u = 1) : projectiveRetraction P ell u = u := by
  simp only [projectiveRetraction,hP,hEll,inv_one,one_smul]

theorem projectiveRetractionDerivative_apply (P : E →L[ℝ] E) (ell : E →L[ℝ] ℝ)
    (u v : E) : projectiveRetractionDerivative P ell u v =
      (ell u)⁻¹ • P v - (((ell u)⁻¹)^2 * ell v) • P u := by
  simp only [projectiveRetractionDerivative,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.smulRight_apply,smul_smul]

theorem projectiveRetraction_hasFDerivAt (P : E →L[ℝ] E) (ell : E →L[ℝ] ℝ)
    (u : E) (hu : ell u ≠ 0) :
    HasFDerivAt (projectiveRetraction P ell) (projectiveRetractionDerivative P ell u) u := by
  have hi := (hasFDerivAt_inv hu).comp u ell.hasFDerivAt
  have hd := hi.fun_smul P.hasFDerivAt
  apply hd.congr_fderiv
  ext v
  rw [projectiveRetractionDerivative_apply]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.smulRight_apply,
    smul_sub,smul_smul,ContinuousLinearMap.one_apply,smul_eq_mul,inv_pow,Function.comp_apply]
  module

theorem projectiveRetraction_contDiffAt (P : E →L[ℝ] E) (ell : E →L[ℝ] ℝ)
    (u : E) (hu : ell u ≠ 0) (n : ℕ∞) : ContDiffAt ℝ n (projectiveRetraction P ell) u :=
  (ell.contDiff.contDiffAt.inv hu).smul P.contDiff.contDiffAt

/-- The ambient retraction can have large norm; on a retained face tangent
its derivative is exactly the identity, which gives the sharp mass value. -/
theorem projectiveRetractionDerivative_face (P : E →L[ℝ] E) (ell : E →L[ℝ] ℝ)
    (u v : E) (hu : ell u = 1) (hPv : P v = v) (hEllv : ell v = 0) :
    projectiveRetractionDerivative P ell u v = v := by
  simp only [projectiveRetractionDerivative_apply,hu,hPv,hEllv,inv_one,one_pow,
    mul_zero,zero_smul,one_smul,sub_zero]

end Paper28
