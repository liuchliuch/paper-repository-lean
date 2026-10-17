import Paper28.ProjectiveRetraction
import Paper28.L2CoordinateProjections

/-! Actual finite barycentric coordinate deletion and renormalization,
including the retained-face tangent derivative identity. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
variable {ι : Type*} [DecidableEq ι]

def l2CoordinateEvaluation (i : ι) : CoordinateHilbert ι →ₗ[ℝ] ℝ where
  toFun u := u i
  map_add' u v := rfl
  map_smul' a u := rfl

def l2CoordinateEvaluationCLM (i : ι) : CoordinateHilbert ι →L[ℝ] ℝ :=
  (l2CoordinateEvaluation i).mkContinuous 1 (fun u => by
    simpa using lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) u i)

def retainedBarycentricSum (A : Finset ι) : CoordinateHilbert ι →L[ℝ] ℝ :=
  ∑ i ∈ A, l2CoordinateEvaluationCLM i

@[simp] theorem retainedBarycentricSum_apply (A : Finset ι) (u : CoordinateHilbert ι) :
    retainedBarycentricSum A u = ∑ i ∈ A, u i := by
  simp only [retainedBarycentricSum,ContinuousLinearMap.sum_apply,l2CoordinateEvaluationCLM,
    LinearMap.mkContinuous_apply,l2CoordinateEvaluation]
  rfl

def barycentricRetraction (A : Finset ι) : CoordinateHilbert ι → CoordinateHilbert ι :=
  projectiveRetraction (l2CoordinateProjectionCLM A) (retainedBarycentricSum A)

theorem l2CoordinateProjection_fixed_on_support (A : Finset ι) (u : CoordinateHilbert ι)
    (hu : ∀ i ∉ A, u i = 0) : l2CoordinateProjectionCLM A u = u := by
  ext i
  change l2CoordinateProjection A u i = u i
  rw [l2CoordinateProjection_apply]
  split_ifs with hi
  · rfl
  · exact (hu i hi).symm

theorem barycentricRetraction_fixed (A : Finset ι) (u : CoordinateHilbert ι)
    (hSupport : ∀ i ∉ A, u i = 0) (hSum : ∑ i ∈ A, u i = 1) :
    barycentricRetraction A u = u :=
  projectiveRetraction_fixed _ _ u (l2CoordinateProjection_fixed_on_support A u hSupport)
    (by simpa only [retainedBarycentricSum_apply] using hSum)

theorem barycentricRetraction_tangent_derivative (A : Finset ι) (u v : CoordinateHilbert ι)
    (hSum : ∑ i ∈ A, u i = 1) (hSupportV : ∀ i ∉ A, v i = 0)
    (hSumV : ∑ i ∈ A, v i = 0) :
    projectiveRetractionDerivative (l2CoordinateProjectionCLM A) (retainedBarycentricSum A) u v = v := by
  apply projectiveRetractionDerivative_face
  · simpa only [retainedBarycentricSum_apply] using hSum
  · exact l2CoordinateProjection_fixed_on_support A v hSupportV
  · simpa only [retainedBarycentricSum_apply] using hSumV

end Paper28
