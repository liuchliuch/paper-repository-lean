import Paper28.ShadowDifferential

/-! Exact covariance of the actual finite shadow and its differential under
coordinate isometries. These are changes of indices, preserving signs. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open WithLp
variable {ι ι' κ κ' : Type*} [Fintype ι] [Fintype ι'] [Fintype κ] [Fintype κ']
  [DecidableEq κ] [DecidableEq κ']

def reindexCoordinates (e : ι ≃ ι') : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι' :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e

@[simp] theorem reindexCoordinates_apply (e : ι ≃ ι') (u : EuclideanSpace ℝ ι) (i : ι') :
    reindexCoordinates e u i = u (e.symm i) := rfl

theorem sum_reindex_fiber (e : ι ≃ ι') (q : κ ≃ κ') (g : ι → κ) (f : ι' → κ')
    (hroute : ∀ i, q (g i) = f (e i)) (r : ι → ℝ) (b : κ) :
    (∑ i ∈ Finset.univ.filter (fun i => g i = b), r i) =
      ∑ j ∈ Finset.univ.filter (fun j => f j = q b), r (e.symm j) := by
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Fintype.sum_equiv e
  intro i
  simp only [e.symm_apply_apply]
  have hr : g i = b ↔ f (e i) = q b := by rw [← hroute i, q.injective.eq_iff]
  simp only [hr]

/-- The finite branch norm commutes with arbitrary coordinate reindexing. -/
theorem finiteShadow_reindex (e : ι ≃ ι') (q : κ ≃ κ') (g : ι → κ) (f : ι' → κ')
    (hroute : ∀ i, q (g i) = f (e i)) (u : EuclideanSpace ℝ ι) (b : κ) :
    finiteShadow g u b = finiteShadow f (reindexCoordinates e u) (q b) := by
  change Real.sqrt _ = Real.sqrt _
  congr 1
  exact sum_reindex_fiber e q g f hroute (fun i => u i ^ 2) b

/-- The same exact covariance holds for the canonical differential. -/
theorem shadowDifferential_reindex (e : ι ≃ ι') (q : κ ≃ κ') (g : ι → κ) (f : ι' → κ')
    (hroute : ∀ i, q (g i) = f (e i)) (u h : EuclideanSpace ℝ ι) (b : κ) :
    shadowDifferential g u h b =
      shadowDifferential f (reindexCoordinates e u) (reindexCoordinates e h) (q b) := by
  rw [shadowDifferential_apply, shadowDifferential_apply, finiteShadow_reindex e q g f hroute]
  congr 1
  exact sum_reindex_fiber e q g f hroute (fun i => u i * h i) b

open scoped InnerProductSpace

/-- Reindexing the actual partition preserves its differential Gram form. -/
theorem shadowDifferential_reindex_inner (e : ι ≃ ι') (q : κ ≃ κ')
    (g : ι → κ) (f : ι' → κ') (hroute : ∀ i, q (g i) = f (e i))
    (u h k : EuclideanSpace ℝ ι) :
    ⟪shadowDifferential g u h, shadowDifferential g u k⟫_ℝ =
      ⟪shadowDifferential f (reindexCoordinates e u) (reindexCoordinates e h),
        shadowDifferential f (reindexCoordinates e u) (reindexCoordinates e k)⟫_ℝ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  calc
    _ = ∑ b, shadowDifferential f (reindexCoordinates e u) (reindexCoordinates e k) (q b) *
        shadowDifferential f (reindexCoordinates e u) (reindexCoordinates e h) (q b) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [shadowDifferential_reindex e q g f hroute u h b,
        shadowDifferential_reindex e q g f hroute u k b]
    _ = _ := Fintype.sum_equiv q _ _ (fun _ => rfl)

end Paper28
