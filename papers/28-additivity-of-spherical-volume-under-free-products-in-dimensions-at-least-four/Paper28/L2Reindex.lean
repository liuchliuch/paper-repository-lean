import Paper28.L2CoordinateProjections

/-! Native coordinate permutation isometries of the actual l2 Hilbert space,
and the left regular action. These supply the equivariance and coefficient
estimates for the relative finite-carrier construction. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
variable {ι κ : Type*}

def l2ReindexFun (e : ι ≃ κ) (u : CoordinateHilbert ι) : CoordinateHilbert κ :=
  ⟨fun j => u (e.symm j), by
    apply memℓp_gen
    exact e.symm.summable_iff.mpr ((memℓp_gen_iff (p := 2) (by norm_num)).mp u.property)⟩

@[simp] theorem l2ReindexFun_apply (e : ι ≃ κ) (u : CoordinateHilbert ι) (j : κ) :
    l2ReindexFun e u j = u (e.symm j) := rfl

theorem l2ReindexFun_norm (e : ι ≃ κ) (u : CoordinateHilbert ι) :
    ‖l2ReindexFun e u‖ = ‖u‖ := by
  have hv := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (l2ReindexFun e u)
  have hu := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) u
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, l2ReindexFun_apply] at hv hu
  have hsum : (∑' j : κ, ‖u (e.symm j)‖ ^ 2) = ∑' i : ι, ‖u i‖ ^ 2 :=
    e.symm.tsum_eq (fun i => ‖u i‖ ^ 2)
  have hs : ‖l2ReindexFun e u‖ ^ 2 = ‖u‖ ^ 2 := hv.trans (hsum.trans hu.symm)
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

def l2Reindex (e : ι ≃ κ) : CoordinateHilbert ι ≃ₗᵢ[ℝ] CoordinateHilbert κ where
  toFun := l2ReindexFun e
  invFun := l2ReindexFun e.symm
  left_inv u := by
    ext i
    simp only [l2ReindexFun_apply, Equiv.symm_symm, Equiv.symm_apply_apply]
  right_inv v := by
    ext j
    simp only [l2ReindexFun_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  map_add' u v := rfl
  map_smul' a u := rfl
  norm_map' := l2ReindexFun_norm e

@[simp] theorem l2Reindex_apply (e : ι ≃ κ) (u : CoordinateHilbert ι) (j : κ) :
    l2Reindex e u j = u (e.symm j) := rfl

variable {G : Type*} [Group G]

def leftRegular (γ : G) : CoordinateHilbert G ≃ₗᵢ[ℝ] CoordinateHilbert G :=
  l2Reindex (Equiv.mulLeft γ)

@[simp] theorem leftRegular_apply (γ : G) (u : CoordinateHilbert G) (g : G) :
    leftRegular γ u g = u (γ⁻¹*g) := rfl

theorem leftRegular_one (u : CoordinateHilbert G) : leftRegular (1 : G) u = u := by
  ext g
  simp

theorem leftRegular_mul (γ δ : G) (u : CoordinateHilbert G) :
    leftRegular (γ*δ) u = leftRegular γ (leftRegular δ u) := by
  ext g
  simp [mul_assoc]

end Paper28
