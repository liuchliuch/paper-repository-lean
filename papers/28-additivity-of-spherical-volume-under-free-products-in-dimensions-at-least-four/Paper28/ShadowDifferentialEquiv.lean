import Paper28.ShadowDifferential
import Paper28.ShadowCuts

/-! Coordinate reindexing preserves the derivative Gram form on every
compatible coordinate stratum, including zero coordinates. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open scoped InnerProductSpace
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

theorem shadowDifferential_equiv_apply (e : ι ≃ κ) (u h : EuclideanSpace ℝ ι) (b : ι) :
    shadowDifferential e u h (e b) = u b * h b / |u b| := by
  have hf : Finset.univ.filter (fun i => e i = e b) = {b} := by
    ext i
    simp
  rw [shadowDifferential_apply, finiteShadow_equiv_apply, hf, Finset.sum_singleton]

/-- The sign differential preserves inner products along a coordinate
stratum. Its convention at zero is harmless because tangent coordinates vanish. -/
theorem signed_coordinate_inner (u h k : ℝ) (hh : u = 0 → h = 0) (hk : u = 0 → k = 0) :
    (u * h / |u|) * (u * k / |u|) = h * k := by
  by_cases hu : u = 0
  · simp [hu, hh hu, hk hu]
  · calc
      _ = (u ^ 2 / |u| ^ 2) * (h * k) := by ring
      _ = h * k := by rw [sq_abs, div_self (pow_ne_zero 2 hu), one_mul]

/-- Gram invariance for a bijective partition, on compatible strata. -/
theorem shadowDifferential_equiv_inner (e : ι ≃ κ) (u h k : EuclideanSpace ℝ ι)
    (hh : ∀ i, u i = 0 → h i = 0) (hk : ∀ i, u i = 0 → k i = 0) :
    ⟪shadowDifferential e u h, shadowDifferential e u k⟫_ℝ = ⟪h,k⟫_ℝ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [← Fintype.sum_equiv e (fun i =>
    shadowDifferential e u k (e i) * shadowDifferential e u h (e i))
    (fun b => shadowDifferential e u k b * shadowDifferential e u h b) (fun _ => rfl)]
  simp_rw [shadowDifferential_equiv_apply]
  exact Finset.sum_congr rfl (fun i _ => signed_coordinate_inner (u i) (k i) (h i) (hk i) (hh i))

end Paper28
