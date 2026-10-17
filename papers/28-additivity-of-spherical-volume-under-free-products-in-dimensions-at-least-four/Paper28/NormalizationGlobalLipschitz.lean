import Paper28.Normalization

/-! A native global comparison for normalized nonzero vectors. This
ordinary bound is used for the carrier intrinsic/ambient metric comparison;
sharp near-isometric deformation constants remain separate native proofs. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem sphericalNormalize_sub_le (u v : H) (hu : u ≠ 0) (hv : v ≠ 0) :
    ‖sphericalNormalize u-sphericalNormalize v‖ ≤ (2/‖u‖)*‖u-v‖ := by
  have hnu : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hCoeff : ‖u‖⁻¹*(‖v‖-‖u‖)*‖v‖⁻¹ = ‖u‖⁻¹-‖v‖⁻¹ := by
    field_simp
  have hEq : sphericalNormalize u-sphericalNormalize v =
      ‖u‖⁻¹ • (u-v)+(‖u‖⁻¹*(‖v‖-‖u‖)) • sphericalNormalize v := by
    unfold sphericalNormalize
    rw [smul_smul,hCoeff]
    module
  have hNorm : |‖v‖-‖u‖| ≤ ‖u-v‖ := by
    simpa only [abs_sub_comm] using abs_norm_sub_norm_le u v
  rw [hEq]
  calc
    _ ≤ ‖‖u‖⁻¹ • (u-v)‖+‖(‖u‖⁻¹*(‖v‖-‖u‖)) • sphericalNormalize v‖ := norm_add_le _ _
    _ = ‖u‖⁻¹*‖u-v‖+‖u‖⁻¹*|‖v‖-‖u‖| := by
      rw [norm_smul,norm_smul,sphericalNormalize_norm v hv,Real.norm_eq_abs,Real.norm_eq_abs,
        abs_mul,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg u)),mul_one]
    _ ≤ ‖u‖⁻¹*‖u-v‖+‖u‖⁻¹*‖u-v‖ :=
      add_le_add_left (mul_le_mul_of_nonneg_left hNorm (inv_nonneg.mpr (norm_nonneg u))) _
    _ = _ := by ring

theorem sphericalNormalize_sub_le_of_lower_norm (u v : H) (ρ : ℝ) (hρ : 0 < ρ)
    (hu : ρ ≤ ‖u‖) (hv : ρ ≤ ‖v‖) :
    ‖sphericalNormalize u-sphericalNormalize v‖ ≤ (2/ρ)*‖u-v‖ := by
  have hnu : u ≠ 0 := norm_pos_iff.mp (hρ.trans_le hu)
  have hnv : v ≠ 0 := norm_pos_iff.mp (hρ.trans_le hv)
  exact (sphericalNormalize_sub_le u v hnu hnv).trans
    (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) hρ hu) (norm_nonneg _))

end Paper28
