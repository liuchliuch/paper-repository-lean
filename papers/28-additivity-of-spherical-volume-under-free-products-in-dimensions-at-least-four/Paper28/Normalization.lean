import Paper28.FoldingDifferential
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! The actual spherical normalization map and its sharp differential norm.
This supplies the near-isometry constant in the relative deformation. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def sphericalNormalize (u : H) : H := ‖u‖⁻¹ • u

def normalizationDerivative (u : H) : H →L[ℝ] H :=
  (1 / ‖u‖) • (ContinuousLinearMap.id ℝ H -
    (1 / ‖u‖ ^ 2) • (innerSL ℝ u).smulRight u)

theorem normalizationDerivative_apply (u h : H) :
    normalizationDerivative u h = (1 / ‖u‖) • (h - (⟪u,h⟫_ℝ / ‖u‖ ^ 2) • u) := by
  simp only [normalizationDerivative, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply, smul_smul]
  congr 2
  ring

theorem sphericalNormalize_norm (u : H) (hu : u ≠ 0) : ‖sphericalNormalize u‖ = 1 := by
  rw [sphericalNormalize, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg u))]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu)

theorem sphericalNormalize_fixed (u : H) (hu : ‖u‖ = 1) : sphericalNormalize u = u := by
  simp [sphericalNormalize, hu]

/-- Removing the radial projection is a contraction, with exact constant one. -/
theorem radial_complement_norm_le (u h : H) :
    ‖h - (⟪u,h⟫_ℝ / ‖u‖ ^ 2) • u‖ ≤ ‖h‖ := by
  by_cases hu : u = 0
  · simp [hu]
  · let c := ⟪u,h⟫_ℝ / ‖u‖ ^ 2
    have hn : ‖u‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hu)
    have hp : ⟪h - c • u, c • u⟫_ℝ = 0 := by
      rw [inner_sub_left, real_inner_smul_right, real_inner_smul_left,
        real_inner_smul_right, real_inner_self_eq_norm_sq, real_inner_comm u h]
      dsimp [c]
      field_simp
      <;> ring
    have hs : ‖h‖ ^ 2 = ‖h - c • u‖ ^ 2 + ‖c • u‖ ^ 2 := by
      calc
        _ = ‖(h - c • u) + c • u‖ ^ 2 := by rw [sub_add_cancel]
        _ = _ := by rw [norm_add_sq_real, hp]; ring
    change ‖h - c • u‖ ≤ ‖h‖
    nlinarith [sq_nonneg ‖c • u‖, norm_nonneg h, norm_nonneg (h - c • u)]

/-- The normalization derivative has norm at most 1 / norm(u), as used
in the sharp relative-deformation estimate. -/
theorem normalizationDerivative_norm_le (u h : H) :
    ‖normalizationDerivative u h‖ ≤ ‖h‖ / ‖u‖ := by
  rw [normalizationDerivative_apply, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (by norm_num) (norm_nonneg u))]
  have hb := mul_le_mul_of_nonneg_left (radial_complement_norm_le u h)
    (show 0 ≤ 1 / ‖u‖ from div_nonneg (by norm_num) (norm_nonneg u))
  simpa [div_eq_mul_inv, mul_comm] using hb

/-- The explicitly bounded operator is the actual Frechet derivative. -/
theorem hasFDerivAt_sphericalNormalize (u : H) (hu : u ≠ 0) :
    HasFDerivAt sphericalNormalize (normalizationDerivative u) u := by
  have hn := hasFDerivAt_hilbertNorm u hu
  have hi := (hasFDerivAt_inv (norm_ne_zero_iff.mpr hu)).comp u hn
  have hd := hi.fun_smul (hasFDerivAt_id u)
  apply hd.congr_fderiv
  ext h
  rw [normalizationDerivative_apply]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, hilbertNormDerivative, innerSL_apply,
    smul_sub, smul_smul, Function.comp_apply, id_eq, one_mul,
    ContinuousLinearMap.one_apply, div_eq_mul_inv, smul_eq_mul, inv_pow]
  module

end Paper28
