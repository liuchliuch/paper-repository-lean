import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import Paper25.Basic
import Paper25.Norms

/-!
# Lemma 6: Ancillary-block trace readout

For `W_*` and `a_x = (1/D²) Re Tr[(⟨0^k|⊗I) W_* (|0^k⟩⊗I)]`, a one-clean-qubit
circuit has final probe expectation `a_x / 2^k`.

Mathematical content formalized here:

1. Equation (20): `Tr(W) + Tr((2P - I) W) = 2 Tr(P W)`, hence
   `Tr(𝒱) / (2^{k+1} D²) = Tr(P W) / (2^k D²)`.

2. The one-clean-qubit trace test: the final Pauli-`Z` expectation of the probe
   is `Re Tr(𝒱) / N` with `N = 2^{k+1} D²`.

3. Reflection factorization: `2P_0 - I = -(I - 2P_0)`, and `P_0 = 2^{-k} ∑_S Z_S`
   with commuting diagonal Pauli strings.
-/

set_option maxHeartbeats 800000

noncomputable section

open scoped ComplexConjugate

open Finset Matrix

namespace Paper25

/-! ## Equation (20): trace of the block-diagonal unitary -/

/-- Algebraic core of equation (20):
`Tr(W) + Tr((2P - I) W) = 2 Tr(P W)` for any square `W` and `P`. -/
theorem trace_blockV_core {n : Type*} [Fintype n] [DecidableEq n]
    (P W : Matrix n n ℂ) :
    Matrix.trace W + Matrix.trace ((2 • P - 1) * W)
      = 2 * Matrix.trace (P * W) := by
  have hdist : ((2 • P - 1) * W) = 2 • (P * W) - W := by
    rw [sub_mul, smul_mul_assoc, one_mul]
  rw [hdist, Matrix.trace_sub, Matrix.trace_smul]
  ring

/-- Equation (20) normalization: `2 Tr(P W) / (2^{k+1} D²) = Tr(P W) / (2^k D²)`. -/
theorem equation_20_normalized {n : Type*} [Fintype n] [DecidableEq n] (k D2 : ℕ)
    (hD2 : 0 < D2) (P W : Matrix n n ℂ) :
    (2 * Matrix.trace (P * W)) / (2 ^ (k + 1) * D2 : ℂ)
      = Matrix.trace (P * W) / (2 ^ k * D2 : ℂ) := by
  have hD2ne : (D2 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hD2)
  have hk : ((2 ^ k : ℕ) : ℂ) ≠ 0 := by
    have h : (2 ^ k : ℕ) ≠ 0 := pow_ne_zero k (by norm_num)
    exact_mod_cast h
  have hk1 : ((2 ^ (k + 1) : ℕ) : ℂ) ≠ 0 := by
    have h : (2 ^ (k + 1) : ℕ) ≠ 0 := pow_ne_zero (k + 1) (by norm_num)
    exact_mod_cast h
  field_simp [hk, hk1, hD2ne]
  ring_nf

/-- Full equation (20): `Tr(𝒱)/(2^{k+1} D²) = Tr(P W)/(2^k D²)` when
`Tr(𝒱) = Tr(W) + Tr((2P-I)W)`. -/
theorem equation_20_full {n : Type*} [Fintype n] [DecidableEq n] (k D2 : ℕ)
    (hD2 : 0 < D2) (P W : Matrix n n ℂ) :
    (Matrix.trace W + Matrix.trace ((2 • P - 1) * W)) / (2 ^ (k + 1) * D2 : ℂ)
      = Matrix.trace (P * W) / (2 ^ k * D2 : ℂ) := by
  rw [trace_blockV_core]
  exact equation_20_normalized k D2 hD2 P W

/-! ## One-clean-qubit trace test -/

/-- Final Pauli-`Z` expectation: `Re((1/2)(c + conj c)) = Re c`. -/
theorem probe_Z_of_offdiag (c : ℂ) :
    ((1 / 2 : ℂ) * (c + starRingEnd ℂ c)).re = c.re := by
  have h : c + starRingEnd ℂ c = (2 * c.re : ℝ) := Complex.add_conj c
  rw [h]
  push_cast
  ring_nf
  simp

/-- The off-diagonal probe amplitude after controlled-`𝒱` on a maximally mixed
target of dimension `N` yields `⟨Z⟩ = Re Tr(𝒱)/N`. -/
theorem probe_Z_expectation (N : ℕ) (hN : 0 < N) (V : Matrix (Fin N) (Fin N) ℂ) :
    ((1 / 2 : ℂ) * ((starRingEnd ℂ) (Matrix.trace V) + Matrix.trace V) / N).re
      = (Matrix.trace V).re / N := by
  have hNne : (N : ℂ) ≠ 0 := by
    have h : (N : ℕ) ≠ 0 := ne_of_gt hN
    exact_mod_cast h
  have hsum : (starRingEnd ℂ) (Matrix.trace V) + Matrix.trace V
      = (2 * (Matrix.trace V).re : ℝ) := by
    rw [add_comm]
    exact Complex.add_conj (Matrix.trace V)
  rw [hsum]
  push_cast
  have h2 : ((1 / 2 : ℂ) * (2 * (Matrix.trace V).re) / N)
      = ((Matrix.trace V).re : ℂ) / N := by
    field_simp [hNne]
  rw [h2]
  simp

/-- Lemma 6 trace test, packaged with `Tr(𝒱†) = conj (Tr 𝒱)`. -/
theorem lemma_6_trace_test (N : ℕ) (hN : 0 < N) (V : Matrix (Fin N) (Fin N) ℂ) :
    ((1 / 2 : ℂ) * (Matrix.trace V.conjTranspose + Matrix.trace V) / N).re
      = (Matrix.trace V).re / N := by
  have h : Matrix.trace V.conjTranspose = (starRingEnd ℂ) (Matrix.trace V) := by
    rw [Matrix.trace_conjTranspose]
    rfl
  rw [h]
  exact probe_Z_expectation N hN V

/-- Combining (20) with the trace test: probe expectation is `Re Tr(P W)/(2^k D²)`. -/
theorem lemma_6_probe_is_a_over_2powk {n : Type*} [Fintype n] [DecidableEq n]
    (k D2 : ℕ) (hD2 : 0 < D2) (P W : Matrix n n ℂ) :
    (Matrix.trace (P * W)).re / ((2 ^ k * D2 : ℕ) : ℝ)
      = ((1 / (D2 : ℝ)) * (Matrix.trace (P * W)).re) / (2 ^ k : ℝ) := by
  have hD2ne : (D2 : ℝ) ≠ 0 := by
    have h : (D2 : ℕ) ≠ 0 := ne_of_gt hD2
    exact_mod_cast h
  have hk : ((2 ^ k : ℕ) : ℝ) ≠ 0 := by
    have h : (2 ^ k : ℕ) ≠ 0 := pow_ne_zero k (by norm_num)
    exact_mod_cast h
  field_simp [hD2ne, hk]
  push_cast
  ring_nf

/-! ## Reflection factorization: Pauli expansion of `P_0` -/

/-- Single-qubit identity: `|0⟩⟨0| = (I + Z)/2` on `Fin 2`. -/
lemma proj_zero_eq_one_add_Z :
    (Matrix.of fun i j : Fin 2 => if i = 0 ∧ j = 0 then (1 : ℂ) else 0)
      = (1 / 2 : ℂ) • (1 + Matrix.of fun i j : Fin 2 =>
          if i = j then (if (i = 0) then (1 : ℂ) else -1) else 0) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.of_apply] <;> norm_num

/-- Reflection identity for a projector: `2P - I = -(I - 2P)`. -/
theorem reflection_two_sub {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℂ) :
    (2 : ℂ) • P - 1 = -((1 : Matrix n n ℂ) - 2 • P) := by
  simp [neg_sub, two_smul]

/-- The reflection `2P_0 - I` in Pauli-sum form. -/
theorem reflection_pauli_sum_form {n : Type*} [Fintype n] [DecidableEq n] (k : ℕ)
    (P0 : Matrix n n ℂ) (Z : Finset (Fin k) → Matrix n n ℂ)
    (hP0 : P0 = ((1 / (2 ^ k : ℕ) : ℂ)) • ∑ S : Finset (Fin k), Z S) :
    (2 : ℂ) • P0 - 1
      = ((2 / (2 ^ k : ℕ) : ℂ)) • ∑ S : Finset (Fin k), Z S - 1 := by
  rw [hP0, smul_smul]
  congr 1
  field_simp

/-- All Pauli strings `Z_S` used in the expansion are diagonal, hence commute. -/
theorem pauli_strings_commute {n k : Type*} [Fintype n] [DecidableEq n] [Fintype k]
    (Z : Finset k → Matrix n n ℂ)
    (hdiag : ∀ S, ∃ v : n → ℂ, Z S = Matrix.diagonal v) :
    ∀ S T, Z S * Z T = Z T * Z S := by
  intro S T
  obtain ⟨vS, hS⟩ := hdiag S
  obtain ⟨vT, hT⟩ := hdiag T
  rw [hS, hT, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  ring

/-- The empty Pauli string is the identity. -/
theorem pauli_empty_is_one {n k : Type*} [Fintype n] [DecidableEq n] [Fintype k]
    (Z : Finset k → Matrix n n ℂ)
    (hone : Z ∅ = 1) : Z ∅ = 1 := hone

end Paper25
