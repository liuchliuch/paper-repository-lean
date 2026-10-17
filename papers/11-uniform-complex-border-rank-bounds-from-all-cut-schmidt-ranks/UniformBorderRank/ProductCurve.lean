import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic
import UniformBorderRank.Flattening

/-!
# Product curves and their Taylor coefficients

For local vectors `v i, w i` the product curve is
`P(t) = ⊗_i (v i + t • w i)`, with coefficient array
`P(t)(idx) = ∏_i (v i (idx i) + t * w i (idx i))`.

The coefficient of `t^k` is
`[t^k]P (idx) = ∑_{|S|=k} (∏_{i∈S} w i (idx i)) (∏_{i∉S} v i (idx i))`.

This file defines these objects and the finite-difference approximants
used in paper (13).
-/

noncomputable section

namespace UniformBorderRank

open Finset

variable {N : ℕ}

/-- Product-curve coefficient array at parameter `t`. -/
def prodCurve {N : ℕ} (d : Fin N → ℕ)
    (v w : ∀ i : Fin N, Fin (d i) → ℂ) (t : ℂ) : Coeffs d :=
  fun idx => ∏ i : Fin N, (v i (idx i) + t * w i (idx i))

/-- Coefficient of `t^k` in the product curve (Taylor coefficient). -/
def prodCurveCoeff {N : ℕ} (d : Fin N → ℕ)
    (v w : ∀ i : Fin N, Fin (d i) → ℂ) (k : ℕ) : Coeffs d :=
  fun idx =>
    ∑ S ∈ powersetCard k (univ : Finset (Fin N)),
      (∏ i ∈ S, w i (idx i)) * (∏ i ∈ Sᶜ, v i (idx i))

/-- Finite-difference approximant (paper (13)):
    `(1/k!) • ε^(-k) • ∑_{j=0}^k (-1)^{k-j} C(k,j) P(j•ε)`. -/
def fdApprox {N : ℕ} (d : Fin N → ℕ)
    (v w : ∀ i : Fin N, Fin (d i) → ℂ) (k : ℕ) (ε : ℂ) : Coeffs d :=
  fun idx =>
    ((1 : ℂ) / (Nat.factorial k : ℂ)) * (ε ^ k)⁻¹ *
      ∑ j ∈ range (k + 1),
        (-1 : ℂ) ^ (k - j) * (Nat.choose k j : ℂ) *
          ∏ i : Fin N, (v i (idx i) + ((j : ℂ) * ε) * w i (idx i))

/-- At `ε = 0` the product curve is `⊗ v`. -/
lemma prodCurve_zero {N : ℕ} (d : Fin N → ℕ)
    (v w : ∀ i : Fin N, Fin (d i) → ℂ) :
    prodCurve d v w 0 = fun idx => ∏ i : Fin N, v i (idx i) := by
  funext idx
  simp [prodCurve]

/-- `prodCurve` is a product tensor for every `t`. -/
lemma isProduct_prodCurve {N : ℕ} (d : Fin N → ℕ)
    (v w : ∀ i : Fin N, Fin (d i) → ℂ) (t : ℂ) :
    isProduct (prodCurve d v w t) := by
  refine ⟨fun i a => v i a + t * w i a, ?_⟩
  intro idx
  rfl

/-- Coefficient of `t^0` is the constant term `∏ v`. -/
lemma prodCurveCoeff_zero {N : ℕ} (d : Fin N → ℕ)
    (v w : ∀ i : Fin N, Fin (d i) → ℂ) :
    prodCurveCoeff d v w 0 = fun idx => ∏ i : Fin N, v i (idx i) := by
  funext idx
  simp [prodCurveCoeff]

end UniformBorderRank
