import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import GeometricMedianCoresets.VarianceCount

/-!
# Double-sum count over `m`-subsets (pure Finset)

For `a : Fin n → Fin n → ℝ`, `2 ≤ m ≤ n`, and
`Ω = (univ : Finset (Fin n)).powersetCard m`,

  `∑ I ∈ Ω, ∑ i ∈ I, ∑ j ∈ I, a i j
    = C(n-1,m-1) · ∑ i, a i i
      + C(n-2,m-2) · ∑ i, ∑ j ∈ univ.erase i, a i j`.
-/

noncomputable section

open scoped BigOperators

namespace GeometricMedianCoresets
namespace VarianceDoubleSum

theorem sum_eq_univ_ite {n : ℕ} (f : Fin n → ℝ) (I : Finset (Fin n)) :
    ∑ i ∈ I, f i
      = ∑ i ∈ (Finset.univ : Finset (Fin n)), (if i ∈ I then f i else 0) := by
  classical
  rw [← Finset.sum_filter]
  simp

theorem double_sum_univ {n : ℕ} (a : Fin n → Fin n → ℝ) (I : Finset (Fin n)) :
    ∑ i ∈ I, ∑ j ∈ I, a i j
      = ∑ i ∈ (Finset.univ : Finset (Fin n)),
          ∑ j ∈ (Finset.univ : Finset (Fin n)),
            (if i ∈ I ∧ j ∈ I then a i j else 0) := by
  classical
  have h1 : ∑ i ∈ I, ∑ j ∈ I, a i j
      = ∑ i ∈ (Finset.univ : Finset (Fin n)),
          (if i ∈ I then ∑ j ∈ I, a i j else 0) :=
    sum_eq_univ_ite (fun i => ∑ j ∈ I, a i j) I
  rw [h1]
  have h2 : ∀ i : Fin n,
      (if i ∈ I then ∑ j ∈ I, a i j else 0)
        = ∑ j ∈ (Finset.univ : Finset (Fin n)),
            (if i ∈ I ∧ j ∈ I then a i j else 0) := by
    intro i
    by_cases hi : i ∈ I
    · have hL : (if i ∈ I then ∑ j ∈ I, a i j else 0) = ∑ j ∈ I, a i j := if_pos hi
      have hR : ∑ j ∈ (Finset.univ : Finset (Fin n)),
          (if i ∈ I ∧ j ∈ I then a i j else 0)
          = ∑ j ∈ I, a i j := by
        have : ∀ j : Fin n, (if i ∈ I ∧ j ∈ I then a i j else 0)
            = (if j ∈ I then a i j else 0) := by
          intro j
          simp [hi]
        rw [Finset.sum_congr rfl (fun j _ => this j), ← Finset.sum_filter]
        simp
      rw [hL, hR]
    · have hL : (if i ∈ I then ∑ j ∈ I, a i j else 0) = (0:ℝ) := if_neg hi
      have hR : ∑ j ∈ (Finset.univ : Finset (Fin n)),
          (if i ∈ I ∧ j ∈ I then a i j else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro j _hj
        simp [hi]
      rw [hL, hR]
  exact Finset.sum_congr rfl fun i _ => h2 i

theorem swap_I {n m : ℕ} (a : Fin n → Fin n → ℝ) :
    (∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
      ∑ i ∈ (Finset.univ : Finset (Fin n)),
        ∑ j ∈ (Finset.univ : Finset (Fin n)),
          (if i ∈ I ∧ j ∈ I then a i j else 0))
      = ∑ i ∈ (Finset.univ : Finset (Fin n)),
          ∑ j ∈ (Finset.univ : Finset (Fin n)),
            ∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
              (if i ∈ I ∧ j ∈ I then a i j else 0) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  exact Finset.sum_comm

theorem collect_I {n m : ℕ} (a : Fin n → Fin n → ℝ) (i j : Fin n) :
    (∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
      (if i ∈ I ∧ j ∈ I then a i j else 0))
      = a i j * (((Finset.univ : Finset (Fin n)).powersetCard m).filter
          (fun s => i ∈ s ∧ j ∈ s)).card := by
  classical
  have h : (∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
      (if i ∈ I ∧ j ∈ I then a i j else 0))
      = ∑ I ∈ ((Finset.univ : Finset (Fin n)).powersetCard m).filter
          (fun s => i ∈ s ∧ j ∈ s), a i j := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  rw [h, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- Split `∑ j ∈ univ` into `j = i` and `j ∈ univ.erase i`. -/
theorem sum_univ_split {n : ℕ} (i : Fin n) (f : Fin n → ℝ) :
    ∑ j ∈ (Finset.univ : Finset (Fin n)), f j
      = f i + ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, f j := by
  have hnot : i ∉ (Finset.univ : Finset (Fin n)).erase i :=
    Finset.notMem_erase i (Finset.univ : Finset (Fin n))
  have h : (Finset.univ : Finset (Fin n))
      = insert i ((Finset.univ : Finset (Fin n)).erase i) := by
    ext x
    by_cases hx : x = i
    · subst hx; simp
    · simp [hx]
  conv_lhs => rw [h]
  rw [Finset.sum_insert hnot]

/-- Main pure-Finset double-sum identity. -/
theorem sum_double_mem_mem {n m : ℕ} (a : Fin n → Fin n → ℝ)
    (hm : 2 ≤ m) (hmn : m ≤ n) :
    (∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
      ∑ i ∈ I, ∑ j ∈ I, a i j)
      = (n - 1).choose (m - 1) * (∑ i, a i i)
        + (n - 2).choose (m - 2) * (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, a i j) := by
  classical
  have h1 : (∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
      ∑ i ∈ I, ∑ j ∈ I, a i j)
      = ∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
          ∑ i ∈ (Finset.univ : Finset (Fin n)),
            ∑ j ∈ (Finset.univ : Finset (Fin n)),
              (if i ∈ I ∧ j ∈ I then a i j else 0) :=
    Finset.sum_congr rfl fun I _ => double_sum_univ a I
  rw [h1, swap_I]
  have h2 : ∀ i j : Fin n,
      (∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
        (if i ∈ I ∧ j ∈ I then a i j else 0))
      = a i j * (((Finset.univ : Finset (Fin n)).powersetCard m).filter
          (fun s => i ∈ s ∧ j ∈ s)).card := fun i j => collect_I a i j
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => h2 i j))]
  have h3 : ∀ i : Fin n,
      (∑ j ∈ (Finset.univ : Finset (Fin n)),
        a i j * (((Finset.univ : Finset (Fin n)).powersetCard m).filter
          (fun s => i ∈ s ∧ j ∈ s)).card)
      = a i i * (((Finset.univ : Finset (Fin n)).powersetCard m).filter
            (fun s => i ∈ s ∧ i ∈ s)).card
        + ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i,
            a i j * (((Finset.univ : Finset (Fin n)).powersetCard m).filter
              (fun s => i ∈ s ∧ j ∈ s)).card := by
    intro i
    exact sum_univ_split i _
  rw [Finset.sum_congr rfl (fun i _ => h3 i), Finset.sum_add_distrib]
  have hdiag_card : ∀ i : Fin n,
      (((Finset.univ : Finset (Fin n)).powersetCard m).filter
        (fun s => i ∈ s ∧ i ∈ s)).card
        = (n - 1).choose (m - 1) := by
    intro i
    have hset : ((Finset.univ : Finset (Fin n)).powersetCard m).filter
        (fun s => i ∈ s ∧ i ∈ s)
        = ((Finset.univ : Finset (Fin n)).powersetCard m).filter (fun s => i ∈ s) := by
      ext s
      simp [and_self]
    rw [hset]
    exact VarianceCount.card_filter_mem n m i (by omega) hmn
  have hdiag_sum : (∑ i : Fin n, a i i * (((Finset.univ : Finset (Fin n)).powersetCard m).filter
      (fun s => i ∈ s ∧ i ∈ s)).card)
      = (n - 1).choose (m - 1) * (∑ i, a i i) := by
    have h : ∀ i : Fin n,
        a i i * (((Finset.univ : Finset (Fin n)).powersetCard m).filter
          (fun s => i ∈ s ∧ i ∈ s)).card
          = a i i * (n - 1).choose (m - 1) := fun i => by rw [hdiag_card i]
    rw [Finset.sum_congr rfl (fun i _ => h i)]
    rw [← Finset.sum_mul]
    ring
  have hoff_count : ∀ i j : Fin n, i ≠ j →
      (((Finset.univ : Finset (Fin n)).powersetCard m).filter
        (fun s => i ∈ s ∧ j ∈ s)).card
        = (n - 2).choose (m - 2) := fun i j hij =>
    VarianceCount.card_filter_mem_mem n m i j hij hm hmn
  have hoff_sum : (∑ i : Fin n, ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i,
      a i j * (((Finset.univ : Finset (Fin n)).powersetCard m).filter
        (fun s => i ∈ s ∧ j ∈ s)).card)
      = (n - 2).choose (m - 2) * (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, a i j) := by
    have h : ∀ i : Fin n,
        (∑ j ∈ (Finset.univ : Finset (Fin n)).erase i,
          a i j * (((Finset.univ : Finset (Fin n)).powersetCard m).filter
            (fun s => i ∈ s ∧ j ∈ s)).card)
        = ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i,
            a i j * (n - 2).choose (m - 2) := by
      intro i
      apply Finset.sum_congr rfl
      intro j hj
      have hij : i ≠ j := by
        intro hh
        rw [hh] at hj
        simp at hj
      rw [hoff_count i j hij]
    have hmul : ∀ i : Fin n,
        (∑ j ∈ (Finset.univ : Finset (Fin n)).erase i,
          a i j * (n - 2).choose (m - 2))
          = (n - 2).choose (m - 2) * ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, a i j := by
      intro i
      rw [← Finset.sum_mul]
      ring
    rw [Finset.sum_congr rfl (fun i _ => (h i).trans (hmul i))]
    rw [← Finset.mul_sum]
  rw [hdiag_sum, hoff_sum]

end VarianceDoubleSum
end GeometricMedianCoresets
