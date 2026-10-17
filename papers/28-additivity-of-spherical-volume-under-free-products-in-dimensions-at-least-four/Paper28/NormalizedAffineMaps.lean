import Paper28.GlobalProjectionHomotopy
import Mathlib.Analysis.Convex.StdSimplex

/-! The actual smooth projective lifts used on retraction pieces:
normalization of an affine Euclidean map, with exact derivatives. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def normalizedAffineMap (L : E →L[ℝ] H) (b : H) (x : E) : H := sphericalNormalize (L x+b)

def normalizedAffineDerivative (L : E →L[ℝ] H) (b : H) (x : E) : E →L[ℝ] H :=
  (normalizationDerivative (L x+b)).comp L

theorem normalizedAffineMap_hasFDerivAt (L : E →L[ℝ] H) (b : H) (x : E) (hx : L x+b ≠ 0) :
    HasFDerivAt (normalizedAffineMap L b) (normalizedAffineDerivative L b x) x := by
  exact (hasFDerivAt_sphericalNormalize (L x+b) hx).comp x (L.hasFDerivAt.add_const b)

theorem normalizedAffineMap_contDiffAt (L : E →L[ℝ] H) (b : H) (x : E) (hx : L x+b ≠ 0) (n : ℕ∞) :
    ContDiffAt ℝ n (normalizedAffineMap L b) x :=
  (sphericalNormalize_contDiffAt _ hx n).comp x (L.contDiff.contDiffAt.add contDiffAt_const)

theorem normalizedAffineMap_norm (L : E →L[ℝ] H) (b : H) (x : E) (hx : L x+b ≠ 0) :
    ‖normalizedAffineMap L b x‖ = 1 := sphericalNormalize_norm _ hx

theorem sphericalNormalize_pos_smul (a : ℝ) (ha : 0 < a) (x : H) :
    sphericalNormalize (a • x) = sphericalNormalize x := by
  unfold sphericalNormalize
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos ha,smul_smul,mul_inv_rev]
  have he : ‖x‖⁻¹*a⁻¹*a = ‖x‖⁻¹ := by rw [mul_assoc,inv_mul_cancel₀ (ne_of_gt ha),mul_one]
  rw [he]

theorem affineMap_barycentric {k : ℕ} (L : E →L[ℝ] H) (b : H)
    (v : Fin (k+1) → E) (t : stdSimplex ℝ (Fin (k+1))) :
    L (∑ i, t.val i • v i)+b = ∑ i, t.val i • (L (v i)+b) := by
  rw [map_sum]
  simp only [map_smul,smul_add,Finset.sum_add_distrib]
  rw [← Finset.sum_smul,t.property.2,one_smul]

end Paper28
