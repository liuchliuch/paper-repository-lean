import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Liouville matrices of elementary channels

Vectorization: `vec(|i⟩⟨j|) = |i⟩|j|`. A unitary conjugation by `G` has
Liouville matrix `G ⊗ conj(G)`. One-qubit dephasing has Liouville matrix
`(I⊗I + Z⊗Z)/2`. The reset channel `X ↦ |0⟩⟨0| Tr X` has Liouville matrix
`|00⟩⟨00| + |00⟩⟨11|`, expanded in the paper's (11) as eight Pauli terms.
-/

noncomputable section

open Kronecker
open scoped ComplexConjugate

namespace Paper25

/-! ## Pauli matrices -/

/-- Pauli-I on `Fin 2`. -/
def pauliI : Matrix (Fin 2) (Fin 2) ℂ := 1

/-- Pauli-X. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of ![![0, 1], ![1, 0]]

/-- Pauli-Y. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of ![![0, -Complex.I], ![Complex.I, 0]]

/-- Pauli-Z. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of ![![1, 0], ![0, -1]]

lemma pauliX_sq : pauliX * pauliX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.mul_apply, Matrix.of_apply]
  <;> norm_num <;> ring_nf <;> simp

lemma pauliZ_sq : pauliZ * pauliZ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ, Matrix.mul_apply, Matrix.of_apply]
  <;> norm_num <;> ring_nf <;> simp

lemma conjugate_pauli : pauliX * pauliZ * pauliX = -pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, pauliZ, Matrix.mul_apply, Matrix.of_apply]
  <;> norm_num <;> ring_nf <;> simp

/-! ## Liouville matrix of a unitary conjugation -/

/-- Liouville matrix of conjugation by `G` on a `d`-dimensional system,
represented as `G ⊗ conj(G)` on `d²` dimensions, indexed by `Fin d × Fin d`. -/
def unitaryL {d : ℕ} (G : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  Matrix.kronecker G (G.map conj)

lemma map_conj_one {d : ℕ} : (1 : Matrix (Fin d) (Fin d) ℂ).map conj = 1 := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.one_apply]
  · simp [Matrix.one_apply, h]

/-! ## Elementary one-qubit Liouville matrices -/

/-- Liouville matrix of one-qubit dephasing `(I⊗I + Z⊗Z)/2`, on `Fin 2 × Fin 2`. -/
def dephasingL : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (1 / 2 : ℂ) • (Matrix.kronecker pauliI pauliI + Matrix.kronecker pauliZ pauliZ)

/-- Liouville matrix of the one-qubit reset `X ↦ |0⟩⟨0| Tr X`:
`|00⟩⟨00| + |00⟩⟨11|`. Index by `Fin 2 × Fin 2`. -/
def resetL : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun i j =>
    if i = (0, 0) ∧ j = (0, 0) then (1 : ℂ)
    else if i = (0, 0) ∧ j = (1, 1) then 1
    else 0

/-- Equation (11): the eight signed Pauli terms
`II + IZ + ZI + ZZ + XX + i XY + i YX - YY`, with overall factor `1/4`.
Their average encodes `S_reset / 2`. -/
def resetPauliSum : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (1 / 4 : ℂ) • (
    Matrix.kronecker pauliI pauliI + Matrix.kronecker pauliI pauliZ +
    Matrix.kronecker pauliZ pauliI + Matrix.kronecker pauliZ pauliZ +
    Matrix.kronecker pauliX pauliX +
    Complex.I • Matrix.kronecker pauliX pauliY +
    Complex.I • Matrix.kronecker pauliY pauliX -
    Matrix.kronecker pauliY pauliY)

/-- Signed average of `S` with weights `1, -1, 1, -1` is zero. -/
lemma signed_average_zero (S : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    (1 / 4 : ℂ) • (S + -S + S + -S) = 0 := by
  have h : S + -S + S + -S = (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
    abel
  rw [h, smul_zero]

/-! ## Vec of matrix units -/

/-- Vectorization of the matrix unit `|i⟩⟨j|` is the computational basis vector
`|i⟩|j|` on `Fin d × Fin d`. -/
def vecMatrixUnit {d : ℕ} (i j : Fin d) : Fin d × Fin d → ℂ :=
  fun p => if p = (i, j) then 1 else 0

lemma vecMatrixUnit_norm {d : ℕ} (i j : Fin d) :
    ∑ p, Complex.normSq (vecMatrixUnit (d := d) i j p) = 1 := by
  classical
  unfold vecMatrixUnit
  rw [Finset.sum_eq_single (i, j)]
  · simp
  · intro p _ hp
    simp [hp]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Paper25
