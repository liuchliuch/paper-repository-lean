import Paper26.ShellAccounting
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Order
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Appendix C: replacement of a principal block

The error identity is proved for actual complex block matrices, including the
conjugation by `U ⊕ I`. No comparison between the old global error and the new
local error is assumed. The numerical counterexample consists of positive
semidefinite, trace-one matrices of dimension four.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder

namespace Paper26.BlockReplacement

open Paper26.ShellAccounting

/-- Direct sum of two square matrices, with zero cross blocks. -/
def directSum {f r : Type*} (D : Matrix f f ℂ) (E : Matrix r r ℂ) :
    Matrix (f ⊕ r) (f ⊕ r) ℂ := Matrix.fromBlocks D 0 0 E

/-- Subtraction is compatible with the concrete four-block representation. -/
theorem fromBlocks_sub {f r : Type*}
    (A A' : Matrix f f ℂ) (B B' : Matrix f r ℂ)
    (C C' : Matrix r f ℂ) (D D' : Matrix r r ℂ) :
    Matrix.fromBlocks A B C D - Matrix.fromBlocks A' B' C' D' =
      Matrix.fromBlocks (A - A') (B - B') (C - C') (D - D') := by
  ext i k
  cases i <;> cases k <;> rfl

/-- The actual block conjugation occurring before replacement in Appendix C. -/
theorem conjugate_by_directSum_identity
    {f r : Type*} [Fintype f] [Fintype r] [DecidableEq r]
    (R : Matrix f f ℂ) (C : Matrix f r ℂ) (B : Matrix r r ℂ)
    (U : Matrix f f ℂ) :
    directSum U (1 : Matrix r r ℂ) * Matrix.fromBlocks R C Cᴴ B *
        (directSum U (1 : Matrix r r ℂ))ᴴ =
      Matrix.fromBlocks (U * R * Uᴴ) (U * C) (Cᴴ * Uᴴ) B := by
  simp [directSum, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]

/-- Equation (54). It holds for arbitrary blocks `D`, `E`, and `D₂`, so in
particular for the diagonal estimate blocks used in the paper. -/
theorem block_replacement_error_identity
    {f r : Type*} [Fintype f] [Fintype r] [DecidableEq f] [DecidableEq r]
    (R D D₂ : Matrix f f ℂ) (C : Matrix f r ℂ) (B E : Matrix r r ℂ)
    (U : Matrix f f ℂ) (hU : Uᴴ * U = 1) :
    frobeniusSq
      (directSum U (1 : Matrix r r ℂ) * Matrix.fromBlocks R C Cᴴ B *
        (directSum U (1 : Matrix r r ℂ))ᴴ - directSum D₂ E) =
      frobeniusSq (Matrix.fromBlocks R C Cᴴ B - directSum D E) -
        frobeniusSq (R - D) + frobeniusSq (U * R * Uᴴ - D₂) := by
  rw [conjugate_by_directSum_identity]
  simp only [directSum, fromBlocks_sub, sub_zero, frobeniusSq_fromBlocks]
  rw [frobeniusSq_unitary_mul C U hU,
    frobeniusSq_mul_unitary Cᴴ Uᴴ (by simpa using hU)]
  ring

/-- Trace changes by precisely the trace change of the replaced block. -/
theorem trace_replacement
    {f r : Type*} [Fintype f] [Fintype r]
    (D D₂ : Matrix f f ℂ) (E : Matrix r r ℂ) :
    Matrix.trace (directSum D₂ E) - Matrix.trace (directSum D E) =
      Matrix.trace D₂ - Matrix.trace D := by
  simp only [directSum, Matrix.trace, Matrix.diag_apply, Fintype.sum_sum_type,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂]
  ring

/-- Density matrices here have actual positive-semidefinite complex matrix
entries and complex trace exactly one. -/
def IsDensity {n : Type*} [Fintype n] (ρ : Matrix n n ℂ) : Prop :=
  ρ.PosSemidef ∧ Matrix.trace ρ = 1

/-- The ordinary nonnegative diagonal criterion yields genuine density matrices. -/
theorem diagonal_isDensity {n : Type*} [Fintype n] [DecidableEq n]
    (p : n → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    IsDensity (Matrix.diagonal fun i => (p i : ℂ)) := by
  constructor
  · apply Matrix.PosSemidef.diagonal
    intro i
    exact Complex.nonneg_iff.mpr ⟨by simpa using hp i, by simp⟩
  · rw [Matrix.trace_diagonal, ← Complex.ofReal_sum, hsum]
    rfl

def inputDiagonal : Fin 4 → ℝ := ![3 / 10, 3 / 10, 1 / 5, 1 / 5]
def oldDiagonal : Fin 4 → ℝ := ![3 / 10, 3 / 10, 1 / 4, 3 / 20]
def newDiagonal : Fin 4 → ℝ := ![8 / 25, 7 / 25, 1 / 4, 3 / 20]

def exampleInput : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal fun i => (inputDiagonal i : ℂ)
def exampleOld : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal fun i => (oldDiagonal i : ℂ)
def exampleNew : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal fun i => (newDiagonal i : ℂ)

theorem exampleInput_isDensity : IsDensity exampleInput := by
  apply diagonal_isDensity
  · intro i
    fin_cases i <;> norm_num [inputDiagonal]
  · norm_num [inputDiagonal, Fin.sum_univ_succ]

theorem exampleOld_isDensity : IsDensity exampleOld := by
  apply diagonal_isDensity
  · intro i
    fin_cases i <;> norm_num [oldDiagonal]
  · norm_num [oldDiagonal, Fin.sum_univ_succ]

theorem exampleNew_isDensity : IsDensity exampleNew := by
  apply diagonal_isDensity
  · intro i
    fin_cases i <;> norm_num [newDiagonal]
  · norm_num [newDiagonal, Fin.sum_univ_succ]

/-- A matrix-level reduction of Frobenius error for real diagonal matrices. -/
theorem diagonal_frobenius_error {n : Type*} [Fintype n] [DecidableEq n]
    (p q : n → ℝ) :
    frobeniusSq ((Matrix.diagonal fun i => (p i : ℂ)) -
      (Matrix.diagonal fun i => (q i : ℂ))) = ∑ i, (p i - q i) ^ 2 := by
  rw [Matrix.diagonal_sub]
  unfold frobeniusSq
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply_eq, Complex.sq_norm]
    simp [Complex.normSq_apply, pow_two]
  · intro k _ hki
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hki)]
    simp
  · simp

/-- The old global squared error is exactly `.005`. -/
theorem example_old_global_error : frobeniusSq (exampleInput - exampleOld) = 1 / 200 := by
  rw [exampleInput, exampleOld, diagonal_frobenius_error]
  norm_num [inputDiagonal, oldDiagonal, Fin.sum_univ_succ]

/-- The new global squared error is exactly `.0058`. -/
theorem example_new_global_error : frobeniusSq (exampleInput - exampleNew) = 29 / 5000 := by
  rw [exampleInput, exampleNew, diagonal_frobenius_error]
  norm_num [inputDiagonal, newDiagonal, Fin.sum_univ_succ]

/-- Restriction to the first two coordinates is an actual matrix subblock. -/
def firstBlock (X : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  X.submatrix (Fin.castAdd 2) (Fin.castAdd 2)


theorem firstBlock_diagonal (p : Fin 4 → ℝ) :
    firstBlock (Matrix.diagonal fun i => (p i : ℂ)) =
      Matrix.diagonal (fun i => (p (Fin.castAdd 2 i) : ℂ)) := by
  exact Matrix.submatrix_diagonal _ _ (Fin.castAdd_injective 2 2)

theorem example_old_first_block_error :
    frobeniusSq (firstBlock exampleInput - firstBlock exampleOld) = 0 := by
  rw [exampleInput, exampleOld, firstBlock_diagonal, firstBlock_diagonal,
    diagonal_frobenius_error]
  norm_num [inputDiagonal, oldDiagonal, Fin.sum_univ_succ, Fin.castAdd]

/-- The new first-block squared error is exactly `.0008`. -/
theorem example_new_first_block_error :
    frobeniusSq (firstBlock exampleInput - firstBlock exampleNew) = 1 / 1250 := by
  rw [exampleInput, exampleNew, firstBlock_diagonal, firstBlock_diagonal,
    diagonal_frobenius_error]
  norm_num [inputDiagonal, newDiagonal, Fin.sum_univ_succ, Fin.castAdd]

/-- Even a new local error smaller than the old global error can increase the
actual global error, as stated in Appendix C. -/
theorem example_block_replacement_increases_global_error :
    frobeniusSq (firstBlock exampleInput - firstBlock exampleNew) <
        frobeniusSq (exampleInput - exampleOld) ∧
      frobeniusSq (exampleInput - exampleOld) <
        frobeniusSq (exampleInput - exampleNew) := by
  rw [example_new_first_block_error, example_old_global_error, example_new_global_error]
  norm_num

/-- The trace counterexample in Appendix C: a positive diagonal replacement
changes the trace of a two-dimensional estimate from one to `1.1`. -/
theorem example_trace_not_preserved :
    Matrix.trace (Matrix.diagonal (![1 / 2, 1 / 2] : Fin 2 → ℂ)) = 1 ∧
      Matrix.trace (Matrix.diagonal (![3 / 5, 1 / 2] : Fin 2 → ℂ)) = 11 / 10 := by
  norm_num [Matrix.trace_diagonal, Fin.sum_univ_two]

end Paper26.BlockReplacement
