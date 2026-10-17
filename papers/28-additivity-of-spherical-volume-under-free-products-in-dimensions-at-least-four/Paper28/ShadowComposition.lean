import Paper28.FiniteShadows

/-! Exact finite branch-norm composition identities, used to factor shadows
through the edge-cut foldings. No Jacobian estimate is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open WithLp
open scoped InnerProductSpace
variable {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]
  [DecidableEq κ] [DecidableEq τ]

theorem sum_composed_fibers (f : κ → τ) (g : ι → κ) (r : ι → ℝ) (c : τ) :
    (∑ b ∈ Finset.univ.filter (fun b => f b = c),
      ∑ i ∈ Finset.univ.filter (fun i => g i = b), r i) =
    ∑ i ∈ Finset.univ.filter (fun i => f (g i) = c), r i := by
  classical
  calc
    _ = ∑ b, if f b = c then (∑ i ∈ Finset.univ.filter (fun i => g i = b), r i) else 0 := by
      rw [Finset.sum_filter]
    _ = ∑ b, ∑ i ∈ (Finset.univ.filter (fun i => f (g i) = c)).filter (fun i => g i = b), r i := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : f b = c
      · rw [if_pos hb]
        apply Finset.sum_congr
        · ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun h => ⟨by simpa [h] using hb, h⟩, fun h => h.2⟩
        · intro i _
          rfl
      · rw [if_neg hb]
        symm
        apply Finset.sum_eq_zero
        intro i hi
        have hgi := (Finset.mem_filter.mp hi).2
        have hfi := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
        exact False.elim (hb (by simpa [hgi] using hfi))
    _ = _ := Finset.sum_fiberwise _ g r

/-- Folding a partition and then a coarser partition is exactly folding
the composite partition, including empty fibers and arbitrary coordinate signs. -/
theorem finiteShadow_comp (f : κ → τ) (g : ι → κ) (u : EuclideanSpace ℝ ι) :
    finiteShadow f (finiteShadow g u) = finiteShadow (f ∘ g) u := by
  ext c
  change Real.sqrt (∑ b ∈ Finset.univ.filter (fun b => f b = c), (finiteShadow g u b) ^ 2) =
    Real.sqrt (∑ i ∈ Finset.univ.filter (fun i => f (g i) = c), u i ^ 2)
  simp_rw [finiteShadow_sq]
  rw [sum_composed_fibers]

/-- Shadows depend on the actual coordinate squares, not their signs. -/
theorem finiteShadow_eq_of_sq_eq (f : ι → κ) (u v : EuclideanSpace ℝ ι)
    (h : ∀ i, u i ^ 2 = v i ^ 2) : finiteShadow f u = finiteShadow f v := by
  ext b
  change Real.sqrt _ = Real.sqrt _
  congr 1
  exact Finset.sum_congr rfl (fun i _ => h i)

/-- All shadows are ambient Hilbert contractions as well as angular contractions. -/
theorem finiteShadow_dist (f : ι → κ) (u v : EuclideanSpace ℝ ι) :
    dist (finiteShadow f u) (finiteShadow f v) ≤ dist u v := by
  have hi := finiteShadow_inner f u v
  have hs : ‖finiteShadow f u - finiteShadow f v‖ ^ 2 ≤ ‖u - v‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_sub_sq_real, finiteShadow_norm, finiteShadow_norm]
    linarith
  rw [dist_eq_norm, dist_eq_norm]
  nlinarith [norm_nonneg (finiteShadow f u - finiteShadow f v), norm_nonneg (u - v)]

/-- At a leaf there is only one branch, so the shadow is constant on the
unit sphere. This is the exact base-case map used by the tree proof. -/
theorem finiteShadow_single_branch [Subsingleton κ] (f : ι → κ)
    (u : EuclideanSpace ℝ ι) (b : κ) : finiteShadow f u b = ‖u‖ := by
  have hb : ∀ i, f i = b := fun _ => Subsingleton.elim _ _
  simp [finiteShadow, hb, EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs]

end Paper28
