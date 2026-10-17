import CalibrationDistance.Core
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Pi

/-! The finite calibrated comparator set and attained infimum claimed in §2.1.
These are proved from the literal bin constraints, rather than assumed as an
abstract property of the loss. -/

open scoped BigOperators

namespace CalibrationDistance

noncomputable section
variable {α : Type*} [Fintype α]

def subsetMean (y : α → ℝ) (s : Finset α) : ℝ :=
  (∑ t ∈ s, y t) / s.card

def subsetMeanVector (y : α → ℝ) (s : α → Finset α) : α → ℝ :=
  fun t => subsetMean y (s t)

lemma calibrated_eq_binMean {y r : α → ℝ} (hr : Calibrated y r) (t : α) :
    r t = binMean r y (r t) := by
  classical
  have hz : r t ∈ Finset.univ.image r := Finset.mem_image_of_mem r (Finset.mem_univ t)
  have hc : ((bucket r (r t)).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr (bucket_nonempty hz))
  have he : binResidual r y (r t) = 0 := by
    simpa only [binResidual, bucket, Finset.sum_filter] using hr.2 (r t)
  rw [binResidual_eq_card_mul hz] at he
  have hzero : binMean r y (r t) - r t = 0 := (mul_eq_zero.mp he).resolve_left hc
  linarith

/-- Every calibrated vector consists of empirical means of subsets of the
same fixed outcome vector. This implies finiteness even for real-valued y. -/
theorem calibratedSet_finite (y : α → ℝ) :
    {r : α → ℝ | Calibrated y r}.Finite := by
  classical
  apply (Set.finite_range (subsetMeanVector y)).subset
  intro r hr
  refine ⟨fun t => bucket r (r t), ?_⟩
  funext t
  exact (calibrated_eq_binMean hr t).symm

theorem calibratedCosts_finite (p y : α → ℝ) : (calibratedCosts p y).Finite := by
  have he : calibratedCosts p y =
      (l1Dist p) '' {r : α → ℝ | Calibrated y r} := by
    ext c
    simp only [calibratedCosts, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨r, hr, hcost⟩
      exact ⟨r, hr, hcost.symm⟩
    · rintro ⟨r, hr, hcost⟩
      exact ⟨r, hr, hcost.symm⟩
  rw [he]
  exact (calibratedSet_finite y).image (l1Dist p)

/-- The source infimum (2.2) is achieved by an actual perfectly calibrated
sequence. -/
theorem calDist_attained (p : α → ℝ) {y : α → ℝ} (hy : Valid y) :
    ∃ r, Calibrated y r ∧ calDist p y = l1Dist p r := by
  exact (calibratedCosts_nonempty (p := p) hy).csInf_mem (calibratedCosts_finite p y)

theorem calDist_le_card {p y : α → ℝ} (hp : Valid p) (hy : Valid y) :
    calDist p y ≤ Fintype.card α := by
  calc
    calDist p y ≤ l1Dist p y := calDist_le_of_calibrated (self_calibrated hy)
    _ ≤ ∑ _t : α, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      rw [abs_sub_comm]
      exact abs_outcome_sub_le_one hp hy t
    _ = Fintype.card α := by simp

end
end CalibrationDistance
