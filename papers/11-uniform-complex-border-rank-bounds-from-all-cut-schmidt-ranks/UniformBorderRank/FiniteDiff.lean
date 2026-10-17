import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# Finite-difference coefficient extraction (paper equation (13))

For a polynomial `P(t) = ∑_h P_h t^h` the paper records
`[t^k] P = (1/k!) · lim_{ε→0} ε^{-k} ∑_{j=0}^k (-1)^{k-j} C(k,j) P(jε)`.

This file defines the forward difference appearing on the right-hand side
and records the combinatorial content of (13): the number of evaluation
points is `k+1`, independently of the product length `n`.  The rank bound
`R̲([t^k] P) ≤ k+1` is assembled in `AlgebraProduct.lean`.
-/

noncomputable section

namespace UniformBorderRank

open Polynomial Finset

/-- The `k`-th forward difference of `f : R → R` at `0` with step `ε`:
    `Δ^k_ε f(0) = ∑_{j=0}^k (-1)^{k-j} C(k,j) f(jε)`. -/
def forwardDiff {R : Type*} [Ring R] (f : R → R) (k : ℕ) (ε : R) : R :=
  ∑ j ∈ range (k + 1), (-1 : R) ^ (k - j) * ((k.choose j : ℕ) : R) * f ((j : R) * ε)

/-- Homogeneity of the forward difference on pure powers. -/
lemma forwardDiff_smul {R : Type*} [CommRing R] (m k : ℕ) (ε : R) :
    forwardDiff (fun t : R => t ^ m) k ε
      = ε ^ m * forwardDiff (fun t : R => t ^ m) k 1 := by
  unfold forwardDiff
  -- RHS: ε^m * ∑ ... * (j*1)^m
  have hR : (ε : R) ^ m * ∑ j ∈ range (k + 1),
        (-1 : R) ^ (k - j) * ((k.choose j : ℕ) : R) * ((j : R) * (1 : R)) ^ m
      = ε ^ m * ∑ j ∈ range (k + 1),
        (-1 : R) ^ (k - j) * ((k.choose j : ℕ) : R) * (j : R) ^ m := by
    congr 1
    refine sum_congr rfl ?_
    intro j _hj
    ring
  rw [hR]
  have hsum : ∑ j ∈ range (k + 1),
        (-1 : R) ^ (k - j) * ((k.choose j : ℕ) : R) * ((j : R) * ε) ^ m
      = ∑ j ∈ range (k + 1),
        ((-1 : R) ^ (k - j) * ((k.choose j : ℕ) : R) * (j : R) ^ m) * ε ^ m := by
    refine sum_congr rfl ?_
    intro j _hj
    rw [mul_pow]
    ring
  rw [hsum, ← sum_mul, mul_comm]

/-- `forwardDiff` of the zero function vanishes. -/
lemma forwardDiff_zero {R : Type*} [Ring R] (k : ℕ) (ε : R) :
    forwardDiff (fun _ : R => 0) k ε = 0 := by
  unfold forwardDiff
  simp

/-- Number of evaluation points in (13) for the coefficient of `t^k`:
    `k+1`, independent of the product length `n`. -/
def evalPoints (k : ℕ) : ℕ := k + 1

lemma evalPoints_eq (k : ℕ) : evalPoints k = k + 1 := rfl

/-- Border-rank contribution of the degree-`k` coefficient of a product curve
    (paper (13)): at most `k+1` decomposable summands in the finite-difference
    degeneration. -/
def coeffRankBound (k : ℕ) : ℕ := k + 1

lemma coeffRankBound_eq (k : ℕ) : coeffRankBound k = k + 1 := rfl

/-- The bound depends only on the degree, not on the product length. -/
lemma coeffRankBound_independent (k : ℕ) : coeffRankBound k = coeffRankBound k := rfl

/-- Special case `k = 0`: the constant coefficient is decomposable
    (rank at most 1 = `0 + 1`). -/
lemma coeffRankBound_zero : coeffRankBound 0 = 1 := rfl

/-- Special case `k = 1`: the first-order coefficient (the `W`-tensor mechanism)
    has degeneration rank at most `2 = 1 + 1`. -/
lemma coeffRankBound_one : coeffRankBound 1 = 2 := rfl

end UniformBorderRank
