import Paper28.RelativeProjection
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-! Actual Frechet differentiation of the local finite projection map.
The zero sum of cutoff derivatives is derived from the partition identity. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter
open scoped Topology
variable {J H : Type*} [Fintype J] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem partition_derivatives_sum_zero (φ : J → H → ℝ) (dφ : J → H → H →L[ℝ] ℝ)
    (u : H) (hφ : ∀ j, HasFDerivAt (φ j) (dφ j u) u)
    (hSum : (fun x => ∑ j, φ j x) =ᶠ[𝓝 u] (fun _ => (1 : ℝ))) :
    (∑ j, dφ j u) = 0 := by
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => hφ j)
  exact hs.unique ((hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) u).congr_of_eventuallyEq hSum)

/-- The explicit error-form operator is the actual Frechet derivative
of the weighted projection, with the cancellation derived above. -/
theorem hasFDerivAt_weightedProjection (φ : J → H → ℝ)
    (dφ : J → H → H →L[ℝ] ℝ) (P : J → H →L[ℝ] H)
    (u : H) (hφ : ∀ j, HasFDerivAt (φ j) (dφ j u) u)
    (hSum : (fun x => ∑ j, φ j x) =ᶠ[𝓝 u] (fun _ => (1 : ℝ))) :
    HasFDerivAt (weightedProjection φ P) (weightedProjectionDerivative φ dφ P u) u := by
  have hzero := partition_derivatives_sum_zero φ dφ u hφ hSum
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    (hφ j).fun_smul (P j).hasFDerivAt)
  apply hs.congr_fderiv
  ext h
  have hz : (∑ j, dφ j u h) = 0 := by
    have hz := congrArg (fun D : H →L[ℝ] ℝ => D h) hzero
    simpa only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.zero_apply] using hz
  simp only [weightedProjectionDerivative, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, Finset.sum_add_distrib]
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hz, zero_smul, sub_zero]

end Paper28
