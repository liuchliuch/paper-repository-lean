import Paper28.ChordAngularComparison

/-! A uniform coarse round/chord bound for finite-cell Lipschitz gluing.
The sharp local estimate is already proved separately; this global bound
is only used to establish ordinary geometric regularity of the realization. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem angular_le_pi_half_chord (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    angular u v ≤ (Real.pi/2)*‖u-v‖ := by
  have hn : 0 ≤ ‖u-v‖/2 := by positivity
  have h1 : ‖u-v‖/2 ≤ 1 := by
    have he := norm_sub_le u v
    rw [hu,hv] at he
    linarith
  have hs := Real.mul_le_sin (Real.arcsin_nonneg.mpr hn) (Real.arcsin_le_pi_div_two (‖u-v‖/2))
  rw [Real.sin_arcsin (by linarith) h1] at hs
  rw [angular_eq_two_arcsin_chord u v hu hv]
  have hp : 0 < Real.pi := Real.pi_pos
  have he := mul_le_mul_of_nonneg_left hs hp.le
  field_simp at he
  nlinarith

end Paper28
