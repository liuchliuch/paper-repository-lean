import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic
import UniformBorderRank.Flattening
import UniformBorderRank.ProductCurve

/-!
# CP rank of the finite-difference approximant (paper (13))

For `1 ≤ N` the approximant
`fdApprox d v w k ε = (1/k!) ε^{-k} ∑_{j=0}^k (-1)^{k-j} C(k,j) P(jε)`
is a sum of `k+1` product tensors after absorbing each scalar into factor 0.
Hence `cpRankLe (fdApprox d v w k ε) (k+1)`.
-/

noncomputable section

namespace UniformBorderRank

open Finset

/-- Absorb a scalar into the `i0` factor of a product over `Fin N`. -/
lemma prod_scalar_absorb {N : ℕ} (i0 : Fin N) (u : Fin N → ℂ) (c : ℂ) :
    c * ∏ i : Fin N, u i = ∏ i : Fin N, (if i = i0 then c * u i else u i) := by
  classical
  have h : ∀ i : Fin N, (if i = i0 then c * u i else u i)
      = (if i = i0 then (c : ℂ) else 1) * u i := by
    intro i
    by_cases hi : i = i0
    · rw [if_pos hi, if_pos hi]
    · rw [if_neg hi, if_neg hi, one_mul]
  have hcongr : ∏ i : Fin N, (if i = i0 then c * u i else u i)
      = ∏ i : Fin N, (if i = i0 then (c : ℂ) else 1) * u i :=
    Finset.prod_congr rfl (fun i _ => h i)
  rw [hcongr, Finset.prod_mul_distrib]
  have h2 : ∏ i : Fin N, (if i = i0 then (c : ℂ) else 1) = c := by
    rw [Finset.prod_eq_single i0]
    · rw [if_pos rfl]
    · intro i _hi hi
      rw [if_neg hi]
    · intro hi
      exact absurd (Finset.mem_univ i0) hi
  rw [h2]

/-- Local factor at `i` for the `j`-th summand, with scalar absorbed at `i0`. -/
def absorbFactor {N : ℕ} (hN : 0 < N) (d : Fin N → ℕ)
    (v w : ∀ i : Fin N, Fin (d i) → ℂ) (j : ℕ) (ε : ℂ) (c : ℂ)
    (i : Fin N) (a : Fin (d i)) : ℂ :=
  if i = (⟨0, hN⟩ : Fin N)
    then c * (v i a + ((j : ℂ) * ε) * w i a)
    else (v i a + ((j : ℂ) * ε) * w i a)

lemma absorbFactor_apply_eq {N : ℕ} (hN : 0 < N) (d : Fin N → ℕ)
    (v w : ∀ i : Fin N, Fin (d i) → ℂ) (j : ℕ) (ε : ℂ) (c : ℂ) (idx : ∀ i, Fin (d i)) :
    ∏ i : Fin N, absorbFactor hN d v w j ε c i (idx i)
      = c * ∏ i : Fin N, (v i (idx i) + ((j : ℂ) * ε) * w i (idx i)) := by
  unfold absorbFactor
  exact (prod_scalar_absorb ⟨0, hN⟩ (fun i => v i (idx i) + ((j : ℂ) * ε) * w i (idx i)) c).symm

/-- Scalar multiple of a product tensor is a product tensor (`1 ≤ N`). -/
lemma isProduct_scalar_mul {N : ℕ} (hN : 0 < N) (d : Fin N → ℕ)
    (v w : ∀ i : Fin N, Fin (d i) → ℂ) (j : ℕ) (ε : ℂ) (c : ℂ) :
    isProduct (N := N) (d := d)
      (fun idx => c * ∏ i : Fin N, (v i (idx i) + ((j : ℂ) * ε) * w i (idx i))) := by
  refine ⟨absorbFactor hN d v w j ε c, ?_⟩
  intro idx
  exact (absorbFactor_apply_eq hN d v w j ε c idx).symm

lemma sum_fin_eq_sum_range {α : Type*} [AddCommMonoid α] (n : ℕ) (g : ℕ → α) :
    ∑ i : Fin n, g i.val = ∑ j ∈ Finset.range n, g j := by
  symm
  refine Finset.sum_bij
    (fun (j : ℕ) (hj : j ∈ Finset.range n) => (⟨j, Finset.mem_range.1 hj⟩ : Fin n))
    ?_ ?_ ?_ ?_
  · intro j hj
    exact Finset.mem_univ _
  · intro a1 _h1 a2 _h2 heq
    exact congrArg Fin.val heq
  · intro b _hb
    exact ⟨b.val, Finset.mem_range.2 b.isLt, rfl⟩
  · intro a _ha
    rfl

/-- Coefficient of the `j`-th summand in `fdApprox`. -/
def fdScalar (k : ℕ) (ε : ℂ) (j : ℕ) : ℂ :=
  ((1 : ℂ) / (Nat.factorial k : ℂ)) * (ε ^ k)⁻¹
    * ((-1) ^ (k - j) * (Nat.choose k j : ℂ))

lemma fdApprox_eq_sum_scalar {N : ℕ} (d : Fin N → ℕ)
    (v w : ∀ i : Fin N, Fin (d i) → ℂ) (k : ℕ) (ε : ℂ) (idx : ∀ i, Fin (d i)) :
    fdApprox d v w k ε idx
      = ∑ j ∈ range (k + 1),
          fdScalar k ε j
            * ∏ i : Fin N, (v i (idx i) + ((j : ℂ) * ε) * w i (idx i)) := by
  unfold fdApprox fdScalar
  set c : ℂ := ((1 : ℂ) / (Nat.factorial k : ℂ)) * (ε ^ k)⁻¹ with hc
  have hre : ∑ j ∈ range (k + 1),
      ((1 : ℂ) / (Nat.factorial k : ℂ)) * (ε ^ k)⁻¹
        * ((-1) ^ (k - j) * (Nat.choose k j : ℂ))
        * ∏ i : Fin N, (v i (idx i) + ((j : ℂ) * ε) * w i (idx i))
    = c * ∑ j ∈ range (k + 1),
          ((-1) ^ (k - j) * (Nat.choose k j : ℂ))
            * ∏ i : Fin N, (v i (idx i) + ((j : ℂ) * ε) * w i (idx i)) := by
    have hassoc : ∑ j ∈ range (k + 1),
        ((1 : ℂ) / (Nat.factorial k : ℂ)) * (ε ^ k)⁻¹
          * ((-1) ^ (k - j) * (Nat.choose k j : ℂ))
          * ∏ i : Fin N, (v i (idx i) + ((j : ℂ) * ε) * w i (idx i))
      = ∑ j ∈ range (k + 1),
          c * (((-1) ^ (k - j) * (Nat.choose k j : ℂ))
            * ∏ i : Fin N, (v i (idx i) + ((j : ℂ) * ε) * w i (idx i))) := by
      refine sum_congr rfl ?_
      intro j _hj
      rw [hc]
      ring
    rw [hassoc, ← mul_sum]
  rw [mul_sum]
  refine sum_congr rfl ?_
  intro j _hj
  ring


/-- `fdApprox` has CP rank at most `k+1` (requires `1 ≤ N`). -/
lemma cpRankLe_fdApprox {N : ℕ} (d : Fin N → ℕ) (hN : 0 < N)
    (v w : ∀ i : Fin N, Fin (d i) → ℂ) (k : ℕ) (ε : ℂ) :
    cpRankLe (fdApprox d v w k ε) (k + 1) := by
  classical
  refine ⟨fun j => (fun idx =>
    fdScalar k ε j.val * ∏ i : Fin N, (v i (idx i) + ((j.val : ℂ) * ε) * w i (idx i))), ?_, ?_⟩
  · intro j
    exact isProduct_scalar_mul hN d v w j.val ε (fdScalar k ε j.val)
  · intro idx
    rw [fdApprox_eq_sum_scalar]
    -- Fin.sum over Fin (k+1) = Finset.sum over range (k+1)
    have hfin : ∑ j : Fin (k + 1),
        fdScalar k ε j.val
          * ∏ i : Fin N, (v i (idx i) + ((j.val : ℂ) * ε) * w i (idx i))
      = ∑ j ∈ range (k + 1),
          (fun j => fdScalar k ε j
            * ∏ i : Fin N, (v i (idx i) + ((j : ℂ) * ε) * w i (idx i))) j := by
      exact sum_fin_eq_sum_range (k + 1)
        (fun j => fdScalar k ε j
          * ∏ i : Fin N, (v i (idx i) + ((j : ℂ) * ε) * w i (idx i)))
    rw [hfin]

end UniformBorderRank
