import Paper28.RegularCoefficientDecay

/-! Native finite-isotropy facts for the actual regular Hilbert sphere,
derived from its proved coefficient decay. No proper-action or stabilizer
finiteness assumption is introduced. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open scoped InnerProductSpace
variable {G : Type*} [Group G] [DecidableEq G]

def regularStabilizer (u : CoordinateHilbert G) : Subgroup G where
  carrier := {γ | leftRegular γ u = u}
  one_mem' := leftRegular_one u
  mul_mem' := by
    intro γ δ hγ hδ
    change leftRegular (γ*δ) u = u
    change leftRegular γ u = u at hγ
    change leftRegular δ u = u at hδ
    rw [leftRegular_mul, hδ, hγ]
  inv_mem' := by
    intro γ hγ
    have h := congrArg (fun z => leftRegular γ⁻¹ z) hγ
    change leftRegular γ⁻¹ (leftRegular γ u) = leftRegular γ⁻¹ u at h
    rw [← leftRegular_mul, inv_mul_cancel, leftRegular_one] at h
    exact h.symm

theorem regularStabilizer_finite (u : CoordinateHilbert G) (hu : ‖u‖ = 1) :
    (regularStabilizer u : Set G).Finite := by
  have hf := Filter.eventually_cofinite.mp (regular_inner_eventually_small u u (1/2) (by norm_num))
  apply hf.subset
  intro γ hγ
  change ¬ |⟪u,leftRegular γ u⟫_ℝ| < 1/2
  have he : ⟪u,leftRegular γ u⟫_ℝ = 1 := by
    rw [show leftRegular γ u = u from hγ, real_inner_self_eq_norm_sq, hu]
    norm_num
  rw [he]
  norm_num

/-- Only finitely many orbit translates of one unit vector come within
ambient distance one of a second unit vector. -/
theorem regular_near_translates_finite (u v : CoordinateHilbert G)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    {γ : G | dist u (leftRegular γ v) < 1}.Finite := by
  have hf := Filter.eventually_cofinite.mp (regular_inner_eventually_small u v (1/2) (by norm_num))
  apply hf.subset
  intro γ hγ
  change dist u (leftRegular γ v) < 1 at hγ
  have hs : ‖u-leftRegular γ v‖ ^ 2 < 1 := by
    rw [dist_eq_norm] at hγ
    nlinarith [norm_nonneg (u-leftRegular γ v)]
  rw [norm_sub_sq_real, hu, (leftRegular γ).norm_map, hv] at hs
  have hi : 1/2 < ⟪u,leftRegular γ v⟫_ℝ := by linarith
  exact not_lt_of_ge (le_trans (by linarith) (le_abs_self _))

end Paper28
