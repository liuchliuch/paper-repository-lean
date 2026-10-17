import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# Perron–Frobenius uniqueness of the positive eigenvector

Elementary Collatz–Wielandt squeeze: two positive eigenvectors of a strictly
positive matrix for a common eigenvalue are proportional.
-/

noncomputable section

open Classical

universe u

open scoped BigOperators

namespace Paper18

/-- Positive eigenvectors of a nonnegative matrix compare their eigenvalues
by a maximal coordinate ratio. -/
theorem nonnegMatrix_positive_eigenvalue_le
    {κ : Type u} [Fintype κ] [Nonempty κ] (A : Matrix κ κ ℝ)
    (lam mu : ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (v w : κ → ℝ) (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (hve : ∀ i, ∑ j, A i j * v j = lam * v i)
    (hwe : ∀ i, ∑ j, A i j * w j = mu * w i) : lam ≤ mu := by
  obtain ⟨i, hi⟩ : ∃ i : κ, ∀ j, v j / w j ≤ v i / w i := Finite.exists_max _
  let R := v i / w i
  have hle (j : κ) : v j ≤ R * w j := by
    exact (div_le_iff₀ (hw j)).mp (hi j)
  have hei : R * w i = v i := div_mul_cancel₀ _ (ne_of_gt (hw i))
  have hbound : lam * v i ≤ mu * v i := by
    calc
      lam * v i = ∑ j, A i j * v j := (hve i).symm
      _ ≤ ∑ j, A i j * (R * w j) :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hle j) (hA i j))
      _ = R * (∑ j, A i j * w j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _; ring
      _ = mu * v i := by
        rw [hwe i]
        calc
          R * (mu * w i) = mu * (R * w i) := by ring
          _ = mu * v i := by rw [hei]
  exact (mul_le_mul_iff_left₀ (hv i)).mp hbound

/-- The eigenvalue admitting a strictly positive eigenvector is unique. -/
theorem nonnegMatrix_positive_eigenvalue_unique
    {κ : Type u} [Fintype κ] [Nonempty κ] (A : Matrix κ κ ℝ)
    (lam mu : ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (v w : κ → ℝ) (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (hve : ∀ i, ∑ j, A i j * v j = lam * v i)
    (hwe : ∀ i, ∑ j, A i j * w j = mu * w i) : lam = mu :=
  le_antisymm (nonnegMatrix_positive_eigenvalue_le A lam mu hA v w hv hw hve hwe)
    (nonnegMatrix_positive_eigenvalue_le A mu lam hA w v hw hv hwe hve)

/-- **PF uniqueness (same eigenvalue).**
If `A` is strictly positive and `v, w > 0` are eigenvectors for the same
eigenvalue `lam`, then `v` and `w` are proportional with a positive ratio. -/
theorem posMatrix_positive_eigenspace_one_dim
    {κ : Type u} [Fintype κ] [Nonempty κ] (A : Matrix κ κ ℝ) (lam : ℝ)
    (hA : ∀ i j, 0 < A i j)
    (v w : κ → ℝ)
    (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (hve : ∀ i, ∑ j, A i j * v j = lam * v i)
    (hwe : ∀ i, ∑ j, A i j * w j = lam * w i) :
    ∃ c : ℝ, 0 < c ∧ ∀ i, v i = c * w i := by
  classical
  obtain ⟨iStar, hiMax⟩ : ∃ i : κ, ∀ j, v j / w j ≤ v i / w i :=
    Finite.exists_max _
  set R := v iStar / w iStar
  have hR_pos : 0 < R := div_pos (hv iStar) (hw iStar)
  have hle : ∀ j, v j ≤ R * w j := by
    intro j
    have hwj : 0 < w j := hw j
    have h2 : v j / w j ≤ R := hiMax j
    have := (div_le_iff₀ hwj).mp h2
    simpa [R, mul_comm, mul_left_comm, mul_assoc] using this
  have hrow : ∑ j, A iStar j * v j = lam * v iStar := hve iStar
  have hroww : ∑ j, A iStar j * w j = lam * w iStar := hwe iStar
  have hsum_le : ∑ j, A iStar j * v j ≤ ∑ j, A iStar j * (R * w j) := by
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left (hle j) (le_of_lt (hA iStar j))
  have hsum_R : ∑ j, A iStar j * (R * w j) = R * (lam * w iStar) := by
    have h : ∀ j, A iStar j * (R * w j) = R * (A iStar j * w j) := fun j => by ring
    calc ∑ j, A iStar j * (R * w j)
        = ∑ j, R * (A iStar j * w j) := Finset.sum_congr rfl (fun j _ => h j)
      _ = R * ∑ j, A iStar j * w j := (Finset.mul_sum _ _ _).symm
      _ = R * (lam * w iStar) := by rw [hroww]
  have hvi : v iStar = R * w iStar := by
    have hw0 : w iStar ≠ 0 := ne_of_gt (hw iStar)
    simp only [R]
    exact (div_mul_cancel₀ _ hw0).symm
  have heq : lam * v iStar = R * (lam * w iStar) := by
    have h1 : lam * v iStar = ∑ j, A iStar j * v j := hrow.symm
    have h2 : ∑ j, A iStar j * v j ≤ R * (lam * w iStar) := by
      rw [← hsum_R]; exact hsum_le
    have h3 : R * (lam * w iStar) = lam * v iStar := by
      rw [hvi]; ring
    linarith
  have hterm : ∀ j, A iStar j * v j = A iStar j * (R * w j) := by
    intro j
    by_contra hne
    have hlt : A iStar j * v j < A iStar j * (R * w j) := by
      apply mul_lt_mul_of_pos_left
      · apply lt_of_le_of_ne (hle j)
        intro heqj
        exact hne (congrArg (fun t => A iStar j * t) heqj)
      · exact hA iStar j
    have hsum_lt : ∑ k, A iStar k * v k < ∑ k, A iStar k * (R * w k) := by
      refine Finset.sum_lt_sum (fun k _ => ?_) ⟨j, Finset.mem_univ _, hlt⟩
      exact mul_le_mul_of_nonneg_left (hle k) (le_of_lt (hA iStar k))
    rw [hrow, hsum_R] at hsum_lt
    linarith
  refine ⟨R, hR_pos, ?_⟩
  intro j
  have hAj : 0 < A iStar j := hA iStar j
  exact mul_left_cancel₀ (ne_of_gt hAj) (hterm j)

end Paper18
