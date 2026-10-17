import Paper17.Extension
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Gluing the finite barycentric interpolation

The formula on a sorted chamber is independent of every tie-breaking choice.
Strict jumps determine the entire prefix set; a zero jump has coefficient
zero. This proves agreement on all closed chamber intersections.
-/
noncomputable section
open scoped Topology BigOperators
namespace Paper17
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every finite real weight vector admits a decreasing ordering. -/
theorem exists_decreasing_perm {n : ℕ} (w : Fin n → ℝ) :
    ∃ σ : Equiv.Perm (Fin n), Decreasing w σ := by
  let σ := Tuple.sort (fun i => OrderDual.toDual (w i))
  refine ⟨σ, ?_⟩
  intro i j hij
  exact Tuple.monotone_sort (fun i => OrderDual.toDual (w i))
    (show i ≤ j from hij)

/-- At a strict drop, the prefix consists precisely of weights above the lower level. -/
theorem mem_seg_iff_weight_gt {n : ℕ} {w : Fin n → ℝ} {σ : Equiv.Perm (Fin n)}
    (hs : Decreasing w σ) (j : Fin n) (hj : j.val + 1 < n)
    (hdrop : w (σ ⟨j.val + 1, hj⟩) < w (σ j)) (x : Fin n) :
    x ∈ seg σ (j.val + 1) ↔ w (σ ⟨j.val + 1, hj⟩) < w x := by
  rw [mem_seg]
  constructor
  · intro hx
    have hle : (σ.symm x).val ≤ j.val := by omega
    have hw := hs (σ.symm x) j hle
    simpa only [Equiv.apply_symm_apply] using hdrop.trans_le hw
  · intro hx
    by_contra hn
    have hle : j.val + 1 ≤ (σ.symm x).val := by omega
    have hw := hs ⟨j.val + 1, hj⟩ (σ.symm x) hle
    simp only [Equiv.apply_symm_apply] at hw
    exact (not_lt_of_ge hw) hx

@[simp] theorem seg_full {n : ℕ} (σ : Equiv.Perm (Fin n)) : seg σ n = Finset.univ := by
  ext x
  simp [mem_seg, (σ.symm x).isLt]

/-- All sorted chamber formulas agree, including on every tie locus. -/
theorem interpPerm_eq {n : ℕ} (q : Finset (Fin n) → E) (w : Fin n → ℝ)
    {σ τ : Equiv.Perm (Fin n)} (hσ : Decreasing w σ) (hτ : Decreasing w τ) :
    interpPerm q σ w = interpPerm q τ w := by
  have hvals : ∀ i, w (σ i) = w (τ i) :=
    congrFun (Tuple.unique_antitone (fun i j hij => hσ i j hij)
      (fun i j hij => hτ i j hij))
  unfold interpPerm
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val + 1 < n
  · simp only [dif_pos hj]
    by_cases hz : w (σ j) - w (σ ⟨j.val + 1, hj⟩) = 0
    · rw [← hvals j, ← hvals ⟨j.val + 1, hj⟩, hz]
      simp
    · have hdσ : w (σ ⟨j.val + 1, hj⟩) < w (σ j) := by
        have hle := hσ j ⟨j.val + 1, hj⟩ (by change j.val ≤ j.val + 1; omega)
        exact lt_of_le_of_ne hle (by intro heq; exact hz (sub_eq_zero.mpr heq.symm))
      have hdτ : w (τ ⟨j.val + 1, hj⟩) < w (τ j) := by simpa only [hvals] using hdσ
      have hseg : seg σ (j.val + 1) = seg τ (j.val + 1) := by
        ext x
        rw [mem_seg_iff_weight_gt hσ j hj hdσ, mem_seg_iff_weight_gt hτ j hj hdτ, hvals]
      rw [hseg, hvals j, hvals ⟨j.val + 1, hj⟩]
  · have hn : j.val + 1 = n := by omega
    simp only [dif_neg hj, hn, seg_full, hvals]

/-- Canonical interpolation obtained from any sorted ordering. -/
def finiteInterpolation {n : ℕ} (q : Finset (Fin n) → E) (w : Fin n → ℝ) : E :=
  interpPerm q (Classical.choose (exists_decreasing_perm w)) w

theorem finiteInterpolation_eq {n : ℕ} (q : Finset (Fin n) → E) (w : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) (hσ : Decreasing w σ) :
    finiteInterpolation q w = interpPerm q σ w :=
  interpPerm_eq q w (Classical.choose_spec (exists_decreasing_perm w)) hσ

/-- Continuity of the finite barycentric interpolation, after gluing all chambers. -/
theorem continuous_finiteInterpolation {n : ℕ} (q : Finset (Fin n) → E) :
    Continuous (finiteInterpolation q) := by
  apply continuous_of_finite_closed_cover (s := sortedBy) isClosed_sortedBy
  · intro w _
    obtain ⟨σ, hσ⟩ := exists_decreasing_perm w
    exact Set.mem_iUnion.mpr ⟨σ, hσ⟩
  · intro σ
    apply (continuous_interpPerm q σ).continuousOn.congr
    intro w hw
    exact finiteInterpolation_eq q w σ hw

end Paper17
