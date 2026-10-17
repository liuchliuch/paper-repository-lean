import Paper26.Normalization
import Mathlib.Analysis.Convex.Jensen

/-!
The finite averaging step in Lemma 2.3. Cyclic coordinate permutations suffice;
no hypothesis asserts the desired scalar-spectrum maximization. The geometric
application must establish concavity and orbit invariance independently.
-/
noncomputable section
open scoped BigOperators ComplexOrder

namespace Paper26.SpectralAveraging

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup ι] [Nonempty ι]

theorem cyclic_diagonal_average (a : ι → ℝ) :
    (∑ j : ι, (1 / (Fintype.card ι : ℝ)) •
      Normalization.diagonalMatrix (fun i => a (i + j))) =
      Normalization.diagonalMatrix (fun _ : ι => (∑ i, a i) / Fintype.card ι) := by
  ext i k
  by_cases hik : i = k
  · subst k
    have hshift : ∑ j : ι, a (i + j) = ∑ j : ι, a j :=
      by simpa using (Equiv.addLeft i).sum_comp Finset.univ a
    simp only [Matrix.sum_apply, Matrix.smul_apply, Normalization.diagonalMatrix,
      Matrix.diagonal_apply_eq, Complex.real_smul, ← Complex.ofReal_mul,
      ← Complex.ofReal_sum, ← Finset.mul_sum, hshift]
    congr 1
    ring
  · simp [Matrix.sum_apply, Matrix.smul_apply, Normalization.diagonalMatrix,
      Matrix.diagonal_apply_ne _ hik, hik]

/-- Concavity and invariance on cyclic coordinate permutations imply the
uniform spectrum maximizes any such functional at fixed trace. -/
theorem uniform_diagonal_maximal_of_concavity
    (v : Matrix ι ι ℂ → ℝ)
    (hv : ConcaveOn ℝ {A : Matrix ι ι ℂ | A.PosDef} v)
    (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (horbit : ∀ j : ι, v (Normalization.diagonalMatrix (fun i => a (i + j))) =
      v (Normalization.diagonalMatrix a)) :
    v (Normalization.diagonalMatrix a) ≤
      v (Normalization.diagonalMatrix (fun _ : ι => (∑ i, a i) / Fintype.card ι)) := by
  have hc : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hs : ∑ _j : ι, (1 / (Fintype.card ι : ℝ)) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_one_div_cancel (ne_of_gt hc)
  have hm : ∀ j : ι, Normalization.diagonalMatrix (fun i => a (i + j)) ∈
      {A : Matrix ι ι ℂ | A.PosDef} := by
    intro j
    exact Matrix.posDef_diagonal_iff.mpr fun i => RCLike.ofReal_pos.mpr (ha (i + j))
  have h := hv.le_map_sum (t := Finset.univ)
    (w := fun _ : ι => 1 / (Fintype.card ι : ℝ))
    (p := fun j => Normalization.diagonalMatrix (fun i => a (i + j)))
    (fun _ _ => by positivity) hs (fun j _ => hm j)
  rw [cyclic_diagonal_average] at h
  simp_rw [horbit] at h
  simp only [smul_eq_mul] at h
  rw [← Finset.sum_mul, hs, one_mul] at h
  exact h

end Paper26.SpectralAveraging
