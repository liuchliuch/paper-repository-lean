import Paper10.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

noncomputable section
namespace Paper10

/-- Splitting a symmetric double sum into its diagonal and its strict upper half. -/
theorem twice_sum_upper {q : ℕ} (f : Fin q → Fin q → ℝ)
    (hf : ∀ i j, f i j = f j i) :
    2 * (∑ p : {x : Fin q × Fin q // x.1 < x.2}, f p.1.1 p.1.2)
      = (∑ i, ∑ j, f i j) - ∑ i, f i i := by
  classical
  have hu : (∑ p : {x : Fin q × Fin q // x.1 < x.2}, f p.1.1 p.1.2)
      = ∑ i, ∑ j, if i < j then f i j else 0 := by
    rw [← Finset.sum_subtype (Finset.univ.filter (fun p : Fin q × Fin q => p.1 < p.2))
      (by simp) (fun p => f p.1 p.2), Finset.sum_filter]
    exact Fintype.sum_prod_type _
  have hl : (∑ i, ∑ j, if j < i then f i j else 0)
      = ∑ i, ∑ j, if i < j then f i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hf j i]
  have hd : (∑ i, ∑ j, if i = j then f i j else 0) = ∑ i, f i i := by simp
  have hh : (∑ i, ∑ j, f i j) =
      (∑ i, ∑ j, if i < j then f i j else 0) +
      (∑ i, ∑ j, if j < i then f i j else 0) +
      (∑ i, ∑ j, if i = j then f i j else 0) := by
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rcases lt_trichotomy i j with h | h | h <;> simp [h, not_lt_of_ge, le_of_lt, ne_of_lt, ne_of_gt, *]
  rw [hl, hd, ← hu] at hh
  linarith

/-- Finite-dimensional Cauchy–Schwarz against the constant vector. -/
theorem sum_sq_le (q : ℕ) (k : Fin q → ℝ) :
    (∑ i, k i) ^ 2 ≤ (q : ℝ) * ∑ i, k i ^ 2 := by
  simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin q => (1 : ℝ)) k
/-- Reversing three independent finite summation indices. -/
theorem sum_three_reverse {ι M : Type*} [Fintype ι] [AddCommMonoid M]
    (f : ι → ι → ι → M) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ a, ∑ b, ∑ c, f c b a := by
  calc
    _ = ∑ b, ∑ c, ∑ a, f a b c := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

/-- Reversing four independent finite summation indices. -/
theorem sum_four_reverse {ι M : Type*} [Fintype ι] [AddCommMonoid M]
    (f : ι → ι → ι → ι → M) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ a, ∑ b, ∑ c, ∑ d, f d c b a := by
  calc
    _ = ∑ b, ∑ c, ∑ d, ∑ a, f a b c d := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]
    _ = ∑ c, ∑ d, ∑ b, ∑ a, f a b c d := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

end Paper10
