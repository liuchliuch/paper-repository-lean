import Paper17.Interpolation
import Paper17.NerveLabels

/-! Convexity, chain membership and support control for the glued finite interpolation. -/
noncomputable section
open scoped Topology BigOperators
namespace Paper17

/-- Barycentric-subdivision coefficient at the prefix of length `j+1`. -/
def baryCoeff {n : ℕ} (w : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (j : Fin n) : ℝ :=
  ((j.val : ℝ) + 1) *
    (w (σ j) - if hj : j.val + 1 < n then w (σ ⟨j.val + 1, hj⟩) else 0)

theorem baryCoeff_nonneg {n : ℕ} {w : Fin n → ℝ} {σ : Equiv.Perm (Fin n)}
    (hw : ∀ i, 0 ≤ w i) (hs : Decreasing w σ) (j : Fin n) : 0 ≤ baryCoeff w σ j := by
  apply mul_nonneg (by positivity)
  by_cases hj : j.val + 1 < n
  · simp only [dif_pos hj]
    exact sub_nonneg.mpr (hs j ⟨j.val + 1, hj⟩ (by change j.val ≤ j.val + 1; omega))
  · simp only [dif_neg hj, sub_zero]
    exact hw _

theorem sum_baryCoeff {n : ℕ} (w : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    ∑ j, baryCoeff w σ j = ∑ i, w i := by
  let a : ℕ → ℝ := fun j => if hj : j < n then w (σ ⟨j, hj⟩) else 0
  have hcoeff : ∑ j : Fin n, baryCoeff w σ j =
      ∑ j ∈ Finset.range n, ((j : ℝ) + 1) * (a j - a (j + 1)) := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j _
    simp only [baryCoeff, a, dif_pos j.isLt]
  rw [hcoeff, sum_range_mul_sub]
  have hsum : ∑ j ∈ Finset.range n, a j = ∑ j : Fin n, w (σ j) := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j _
    exact dif_pos j.isLt
  rw [hsum]
  simpa [a] using Equiv.sum_comp σ w

theorem seg_nonempty {k : ℕ} (σ : Equiv.Perm (Fin (k + 1))) (j : Fin (k + 1)) :
    (seg σ (j.val + 1)).Nonempty := by
  refine ⟨σ 0, (mem_seg σ).mpr ?_⟩
  simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A normalized interpolation is a convex combination of labels on one face flag. -/
theorem finiteInterpolation_mem {k : ℕ} {Y : Set E} {r : E → E → Prop}
    (h : ExtensionHypotheses Y r) (q : Finset (Fin (k + 1)) → E)
    (hq : ∀ s, s.Nonempty → q s ∈ Y)
    (hchain : ∀ s t, s.Nonempty → s ⊆ t → r (q s) (q t))
    (w : Fin (k + 1) → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) :
    finiteInterpolation q w ∈ Y := by
  obtain ⟨σ, hσ⟩ := exists_decreasing_perm w
  rw [finiteInterpolation_eq q w σ hσ]
  apply convexComb_mem_of_chain h
    (ys := fun j => q (seg σ (j.val + 1)))
    (fun j => hq _ (seg_nonempty σ j))
    (fun i j hij => hchain _ _ (seg_nonempty σ i) (seg_mono σ (by omega)))
    (w := baryCoeff w σ) (p := fun j => q (seg σ (j.val + 1)))
    (fun j _ => baryCoeff_nonneg hw hσ j)
    (by rw [sum_baryCoeff, hsum])
    (fun j _ => ⟨j, rfl⟩)

/-- Every positively weighted prefix contains only indices of positive input weights. -/
theorem positive_prefix_support {k : ℕ} {w : Fin (k + 1) → ℝ}
    (hw : ∀ i, 0 ≤ w i) {σ : Equiv.Perm (Fin (k + 1))} (hs : Decreasing w σ)
    (j : Fin (k + 1)) (hj : 0 < baryCoeff w σ j) {i : Fin (k + 1)}
    (hi : i ∈ seg σ (j.val + 1)) : 0 < w i := by
  have hd : 0 < w (σ j) := by
    have hdiff : 0 < w (σ j) -
        (if h : j.val + 1 < k + 1 then w (σ ⟨j.val + 1, h⟩) else 0) :=
      (mul_pos_iff_of_pos_left (by positivity)).mp hj
    have hnext : 0 ≤ (if h : j.val + 1 < k + 1 then w (σ ⟨j.val + 1, h⟩) else 0) := by
      split_ifs
      · exact hw _
      · exact le_rfl
    linarith
  have hidx : (σ.symm i).val ≤ j.val := by
    have hh := (mem_seg σ).mp hi
    omega
  have hle := hs (σ.symm i) j hidx
  simpa only [Equiv.apply_symm_apply] using hd.trans_le hle

/-- Uniform label control passes to the interpolation without a dimension factor. -/
theorem finiteInterpolation_dist_le {k : ℕ} (q : Finset (Fin (k + 1)) → E)
    (w : Fin (k + 1) → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (p : E) (ε : ℝ)
    (herr : ∀ s, s.Nonempty → (∀ i ∈ s, 0 < w i) → dist (q s) p ≤ ε) :
    dist (finiteInterpolation q w) p ≤ ε := by
  obtain ⟨σ, hσ⟩ := exists_decreasing_perm w
  rw [finiteInterpolation_eq q w σ hσ, dist_eq_norm]
  let c := baryCoeff w σ
  let q' := fun j : Fin (k + 1) => q (seg σ (j.val + 1))
  have hsumc : ∑ j, c j = 1 := (sum_baryCoeff w σ).trans hsum
  have hsumpos : ∃ j, 0 < c j := by
    by_contra! hn
    have hz : ∀ j, c j = 0 := fun j => le_antisymm (hn j) (baryCoeff_nonneg hw hσ j)
    simp [hz] at hsumc
  let t := Finset.univ.filter fun j => 0 < c j
  have hsumt : ∑ j ∈ t, c j = 1 := by
    rw [← hsumc]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j _ hj
    have hn : ¬0 < c j := by simpa [t] using hj
    exact le_antisymm (le_of_not_gt hn) (baryCoeff_nonneg hw hσ j)
  have hsumq : interpPerm q σ w = ∑ j ∈ t, c j • q' j := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j _ hj
    have hn : ¬0 < c j := by simpa [t] using hj
    have hz := le_antisymm (le_of_not_gt hn) (baryCoeff_nonneg hw hσ j)
    simp only [hz, zero_smul]
  rw [hsumq]
  apply convexComb_norm_sub_le (fun j _ => baryCoeff_nonneg hw hσ j) hsumt
  intro j hj
  rw [← dist_eq_norm]
  have hj' : 0 < c j := (Finset.mem_filter.mp hj).2
  exact herr _ (seg_nonempty σ j) (fun i hi => positive_prefix_support hw hσ j hj' hi)

end Paper17
