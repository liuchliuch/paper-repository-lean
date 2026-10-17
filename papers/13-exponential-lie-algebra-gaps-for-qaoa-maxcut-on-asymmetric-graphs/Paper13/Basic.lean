import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic

/-!
# Shared conventions for Paper 13

Basis states of `n` qubits are functions `Fin n → Fin 2`.
Operators are complex matrices on that basis type.
-/

noncomputable section

open Matrix
open scoped BigOperators

namespace Paper13

/-- Computational basis of `n` qubits. -/
abbrev QubitBasis (n : ℕ) := Fin n → Fin 2

/-- Operators on `n` qubits. -/
abbrev Op (n : ℕ) := Matrix (QubitBasis n) (QubitBasis n) ℂ

/-- Single-qubit operators. -/
abbrev Op1 := Matrix (Fin 2) (Fin 2) ℂ

/-- Pauli X. -/
def pauliX : Op1 := !![0, 1; 1, 0]

/-- Pauli Y. -/
def pauliY : Op1 := !![0, -Complex.I; Complex.I, 0]

/-- Pauli Z. -/
def pauliZ : Op1 := !![1, 0; 0, -1]

/-- Single-qubit identity. -/
def pauliI : Op1 := 1

lemma pauliX_mul : pauliX * pauliX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two]

lemma pauliZ_mul : pauliZ * pauliZ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

lemma pauliX_conjTranspose : conjTranspose pauliX = pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.conjTranspose]

lemma pauliZ_conjTranspose : conjTranspose pauliZ = pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ, Matrix.conjTranspose]

lemma pauliX_pauliZ_anticommute : pauliX * pauliZ = -(pauliZ * pauliX) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

lemma pauliX_trace_zero : Matrix.trace pauliX = 0 := by
  simp [Matrix.trace, pauliX, Matrix.diag]

lemma pauliZ_trace_zero : Matrix.trace pauliZ = 0 := by
  simp [Matrix.trace, pauliZ, Matrix.diag]

/-- Flip one bit in a basis state. -/
def flipBit {n : ℕ} (v : Fin n) (x : QubitBasis n) : QubitBasis n :=
  Function.update x v (1 - x v)

/-- Swap the values at positions `a` and `b`. -/
def swapBasis {n : ℕ} (a b : Fin n) (x : QubitBasis n) : QubitBasis n :=
  Function.update (Function.update x a (x b)) b (x a)

lemma swapBasis_self {n : ℕ} (a : Fin n) (x : QubitBasis n) :
    swapBasis a a x = x := by
  funext w
  by_cases h : w = a
  · subst h
    simp only [swapBasis]
    simp [Function.update]
  · simp only [swapBasis]
    simp [Function.update, h]

lemma swapBasis_involutive {n : ℕ} (a b : Fin n) (x : QubitBasis n) :
    swapBasis a b (swapBasis a b x) = x := by
  by_cases hab : a = b
  · subst hab
    rw [swapBasis_self]
    exact swapBasis_self a x
  · funext w
    by_cases hw : w = a
    · subst hw
      simp only [swapBasis]
      simp [Function.update, hab]
    · by_cases hw2 : w = b
      · subst hw2
        simp only [swapBasis]
        simp [Function.update, hab]
      · simp only [swapBasis]
        simp [Function.update, hw, hw2]

/-- Embed a single-qubit operator at site `v`. -/
def embed {n : ℕ} (A : Op1) (v : Fin n) : Op n :=
  fun x y => if (∀ w, w ≠ v → x w = y w) then A (x v) (y v) else 0

/-- Local bit flip `X_v`. -/
def Xv {n : ℕ} (v : Fin n) : Op n := embed pauliX v

/-- Local `Z_v`. -/
def Zv {n : ℕ} (v : Fin n) : Op n := embed pauliZ v

/-- Two-qubit coupling `Z_u Z_v`. -/
def ZZ {n : ℕ} (u v : Fin n) : Op n := Zv u * Zv v

/-- SWAP of qubits `a` and `b`. -/
def swapAt {n : ℕ} (a b : Fin n) : Op n :=
  fun x y => if x = swapBasis a b y then (1 : ℂ) else 0

/-- Singlet projector `q_{ab} = (I - SWAP_{ab}) * 2⁻¹`. -/
def singletProj {n : ℕ} (a b : Fin n) : Op n :=
  (2 : ℂ)⁻¹ • (1 - swapAt a b)

/-- Commutator of operators. -/
def comm {n : ℕ} (A B : Op n) : Op n := A * B - B * A

lemma comm_self {n : ℕ} (A : Op n) : comm A A = 0 := by
  simp [comm]

lemma comm_antisymm {n : ℕ} (A B : Op n) : comm A B = - comm B A := by
  simp only [comm]
  abel

/-- An operator is skew-Hermitian. -/
def IsSkewHerm {n : ℕ} (A : Op n) : Prop := conjTranspose A = -A

/-- An operator is idempotent. -/
def IsProj {n : ℕ} (A : Op n) : Prop := A * A = A

/-- An operator is Hermitian. -/
def IsHerm {n : ℕ} (A : Op n) : Prop := conjTranspose A = A

/-- Orthogonal projector: Hermitian and idempotent. -/
def IsOrthProj {n : ℕ} (A : Op n) : Prop := IsHerm A ∧ IsProj A

/-- Collective two-qubit operator `A_a + A_b`. -/
def collective {n : ℕ} (A : Op1) (a b : Fin n) : Op n :=
  embed A a + embed A b

/-- Sum of `X_v` over `Fin n`. -/
def HXFull (n : ℕ) : Op n := ∑ v : Fin n, Xv v

/-- Sum of `Z_v` over `Fin n`. -/
def HZFull (n : ℕ) : Op n := ∑ v : Fin n, Zv v

end Paper13
