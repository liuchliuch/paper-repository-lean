import PsgEst.SourceExamples
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Complete ordered spectrum of the four-state shift-register example

The explicit orthogonal diagonalization proves the entire Gram spectrum,
including multiplicities. The ordered singular values are then obtained by
nonnegative square roots, rather than only computing the second singular value.
-/

open Matrix BigOperators Real Finset Classical Polynomial

namespace PsgEst

private noncomputable def shiftHadamard : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(1 / 2 : ℝ), 1 / 2, 1 / 2, 1 / 2;
     1 / 2, 1 / 2, -1 / 2, -1 / 2;
     1 / 2, -1 / 2, 1 / 2, -1 / 2;
     1 / 2, -1 / 2, -1 / 2, 1 / 2]

private def shiftGramDiag : Fin 4 → ℝ := ![1, 1, 0, 0]

private theorem shiftHadamard_orthogonal :
    shiftHadamard.transpose * shiftHadamard = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [shiftHadamard, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.one_apply, Fin.sum_univ_succ]

/-- Explicit orthogonal diagonalization of the shift-register Gram matrix. -/
theorem shiftRegister_gram_diagonalization :
    gram shiftRegisterP = shiftHadamard * Matrix.diagonal shiftGramDiag * shiftHadamard.transpose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gram, shiftRegisterP, shiftHadamard, shiftGramDiag,
      Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply, Matrix.vecMul_diagonal, Fin.sum_univ_succ]

/-- The characteristic polynomial agrees with that of `diag(1,1,0,0)`. -/
theorem shiftRegister_gram_charpoly_diagonal :
    (gram shiftRegisterP).charpoly = (Matrix.diagonal shiftGramDiag).charpoly := by
  rw [shiftRegister_gram_diagonalization, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
    shiftHadamard_orthogonal, Matrix.one_mul]

/-- The Gram characteristic polynomial retains both copies of each root. -/
theorem shiftRegister_gram_charpoly :
    (gram shiftRegisterP).charpoly = (X - 1) ^ 2 * X ^ 2 := by
  rw [shiftRegister_gram_charpoly_diagonal, Matrix.charpoly_diagonal]
  norm_num [shiftGramDiag, Fin.prod_univ_succ]
  ring

/-- The full Gram root multiset is `{1,1,0,0}`, with algebraic multiplicities. -/
theorem shiftRegister_gram_roots :
    (gram shiftRegisterP).charpoly.roots = (([1, 1, 0, 0] : List ℝ) : Multiset ℝ) := by
  have hpoly : (gram shiftRegisterP).charpoly =
      ((([1, 1, 0, 0] : List ℝ) : Multiset ℝ).map (fun a => X - C a)).prod := by
    rw [shiftRegister_gram_charpoly]
    norm_num
    ring
  rw [hpoly, Polynomial.roots_multiset_prod_X_sub_C]

/-- The complete decreasingly ordered Gram eigenvalue list. -/
theorem shiftRegister_ordered_gram_spectrum :
    List.ofFn (gramEig₀ shiftRegisterP) = [1, 1, 0, 0] := by
  have h := (gram_isHermitian shiftRegisterP).sort_roots_charpoly_eq_eigenvalues₀
  rw [shiftRegister_gram_roots] at h
  have hs : (([1, 1, 0, 0] : List ℝ) : Multiset ℝ).sort (· ≥ ·) = [1, 1, 0, 0] := by
    rw [Multiset.coe_sort, List.mergeSort_of_sorted]
    norm_num [List.Sorted]
  simpa only [Multiset.map_coe, List.map_cons, List.map_nil, RCLike.re_to_real,
    hs, gramEig₀] using h.symm

/-- Pointwise form of the full ordered Gram spectrum, with two eigenvalues one
followed by two eigenvalues zero. -/
theorem shiftRegister_gramEig₀ (j : Fin (Fintype.card (Fin 4))) :
    gramEig₀ shiftRegisterP j = if j.val < 2 then 1 else 0 := by
  have hv : List.ofFn (fun i : Fin (Fintype.card (Fin 4)) =>
      if i.val < 2 then (1 : ℝ) else 0) = [1, 1, 0, 0] := by
    norm_num [List.ofFn_succ]
  have hf := List.ofFn_inj.mp (shiftRegister_ordered_gram_spectrum.trans hv.symm)
  exact congrFun hf j

/-- The complete ordered singular-value list is `(1,1,0,0)`.
Every Gram eigenvalue appears exactly once, so multiplicities are preserved. -/
theorem shiftRegister_ordered_singular_spectrum :
    List.ofFn (fun j : Fin (Fintype.card (Fin 4)) =>
      Real.sqrt (max 0 (gramEig₀ shiftRegisterP j))) = [1, 1, 0, 0] := by
  rw [List.ofFn_comp' (gramEig₀ shiftRegisterP) (fun a : ℝ => Real.sqrt (max 0 a)),
    shiftRegister_ordered_gram_spectrum]
  norm_num

/-- Pointwise nonnegative-square-root form of the complete singular spectrum. -/
theorem shiftRegister_ordered_singular_value (j : Fin (Fintype.card (Fin 4))) :
    Real.sqrt (max 0 (gramEig₀ shiftRegisterP j)) = if j.val < 2 then 1 else 0 := by
  rw [shiftRegister_gramEig₀]
  split_ifs <;> norm_num

end PsgEst
