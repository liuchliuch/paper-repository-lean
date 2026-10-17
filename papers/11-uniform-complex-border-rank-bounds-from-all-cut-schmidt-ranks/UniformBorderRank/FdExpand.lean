import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic
import UniformBorderRank.DiffSum
import UniformBorderRank.ProductCurve
import UniformBorderRank.FdRank
import UniformBorderRank.FdLimit

/-!
# Product expansion and finite-difference assembly (paper (13))

Using `Finset.prod_add`:
`∏ (α_i + t β_i) = ∑_S t^{|S|} (∏_{i∈S} β_i) (∏_{i∈Sᶜ} α_i)`.

Exchanging the `j`-sum and `S`-sum in `fdApprox`, the inner sum is `S(|S|, k)`:
* `|S| < k`  → `S(|S|,k) = 0`           (`S_of_lt`)
* `|S| = k`  → `S(k,k) = k!`            (`S_self`), giving `prodCurveCoeff`
* `|S| > k`  → `ε^{|S|-k} · const`      (tail → 0)

This yields `borderRankLe (prodCurveCoeff d v w k) (k+1)` for `0 < N`.
-/

noncomputable section

namespace UniformBorderRank

open Finset

/-- `∏ (α_i + t β_i) = ∑_{S} t^{|S|} (∏_{i∈S} β_i) (∏_{i∉S} α_i)`. -/
lemma prod_two_term_expansion {N : ℕ} (α β : Fin N → ℂ) (t : ℂ) :
    ∏ i : Fin N, (α i + t * β i)
      = ∑ S : Finset (Fin N),
          t ^ S.card * (∏ i ∈ S, β i) * (∏ i ∈ Sᶜ, α i) := by
  classical
  have h := Finset.prod_add (fun i => t * β i) (fun i => α i) (univ : Finset (Fin N))
  have hL : ∏ i : Fin N, (α i + t * β i)
      = ∏ i ∈ (univ : Finset (Fin N)), (t * β i + α i) := by
    refine prod_congr rfl ?_
    intro i _hi
    ring
  rw [hL, h]
  have hpow : (univ : Finset (Fin N)).powerset = univ := by
    ext S
    simp
  rw [hpow]
  refine sum_congr rfl ?_
  intro S _hS
  have hprod : (∏ i ∈ S, t * β i) = t ^ S.card * (∏ i ∈ S, β i) := by
    rw [prod_mul_distrib, prod_const]
  have hcomp : (univ : Finset (Fin N)) \ S = Sᶜ := by
    ext i
    simp
  calc (∏ i ∈ S, t * β i) * ∏ i ∈ (univ : Finset (Fin N)) \ S, α i
      = (t ^ S.card * (∏ i ∈ S, β i)) * (∏ i ∈ Sᶜ, α i) := by
        rw [hprod, hcomp]
    _ = t ^ S.card * (∏ i ∈ S, β i) * (∏ i ∈ Sᶜ, α i) := by
        ring

/-- `powersetCard k univ` is the set of `S` with `S.card = k`. -/
lemma powersetCard_eq_filter {N : ℕ} (k : ℕ) :
    powersetCard k (univ : Finset (Fin N))
      = (univ : Finset (Finset (Fin N))).filter (fun S => S.card = k) := by
  ext S
  simp [mem_powersetCard]

/-- Coefficient `e_S = (∏_{i∈S} β_i) (∏_{i∈Sᶜ} α_i)` at index `idx`. -/
def eS {N : ℕ} (d : Fin N → ℕ) (v w : ∀ i : Fin N, Fin (d i) → ℂ)
    (idx : ∀ i, Fin (d i)) (S : Finset (Fin N)) : ℂ :=
  (∏ i ∈ S, w i (idx i)) * (∏ i ∈ Sᶜ, v i (idx i))

/-- `prodCurve t idx = ∑_S t^{S.card} eS S`. -/
lemma prodCurve_eq_sum {N : ℕ} (d : Fin N → ℕ)
    (v w : ∀ i : Fin N, Fin (d i) → ℂ) (t : ℂ) (idx : ∀ i, Fin (d i)) :
    prodCurve d v w t idx
      = ∑ S : Finset (Fin N), t ^ S.card * eS d v w idx S := by
  unfold prodCurve eS
  rw [prod_two_term_expansion (fun i => v i (idx i)) (fun i => w i (idx i)) t]
  refine sum_congr rfl ?_
  intro S _hS
  ring

/-- `prodCurveCoeff k idx = ∑_{|S|=k} eS S`. -/
lemma prodCurveCoeff_eq_sum {N : ℕ} (d : Fin N → ℕ)
    (v w : ∀ i : Fin N, Fin (d i) → ℂ) (k : ℕ) (idx : ∀ i, Fin (d i)) :
    prodCurveCoeff d v w k idx
      = ∑ S ∈ powersetCard k (univ : Finset (Fin N)), eS d v w idx S := by
  rfl




/-- `∑_{j=0}^k (-1)^{k-j} C(k,j) (jε)^m = ε^m · S m k`. -/
lemma sum_alt_pow (k m : ℕ) (ε : ℂ) :
    ∑ j ∈ range (k + 1),
        (-1 : ℂ) ^ (k - j) * (Nat.choose k j : ℂ) * ((j : ℂ) * ε) ^ m
      = ε ^ m * UniformBorderRank.S m k := by
  unfold UniformBorderRank.S
  have h : ∑ j ∈ range (k + 1),
      (-1 : ℂ) ^ (k - j) * (Nat.choose k j : ℂ) * ((j : ℂ) * ε) ^ m
    = ∑ j ∈ range (k + 1),
        ((-1 : ℂ) ^ (k - j) * (Nat.choose k j : ℂ) * (j : ℂ) ^ m) * ε ^ m := by
    refine sum_congr rfl ?_
    intro j _hj
    rw [mul_pow]
    ring
  rw [h, ← sum_mul]
  ring

/-- `fdApprox` as a sum over subsets, before splitting by cardinality. -/
lemma fdApprox_eq_sum_A {N : ℕ} (d : Fin N → ℕ)
    (v w : ∀ i : Fin N, Fin (d i) → ℂ) (k : ℕ) (ε : ℂ) (idx : ∀ i, Fin (d i)) :
    fdApprox d v w k ε idx
      = ∑ A : Finset (Fin N),
          ((1 : ℂ) / (Nat.factorial k : ℂ)) * (ε ^ k)⁻¹
            * (ε ^ A.card * eS d v w idx A * UniformBorderRank.S A.card k) := by
  unfold fdApprox
  have hP : ∀ j : ℕ,
      ∏ i : Fin N, (v i (idx i) + ((j : ℂ) * ε) * w i (idx i))
        = ∑ A : Finset (Fin N), ((j : ℂ) * ε) ^ A.card * eS d v w idx A := by
    intro j
    exact prodCurve_eq_sum d v w ((j : ℂ) * ε) idx
  have hsum : ∑ j ∈ range (k + 1),
      (-1 : ℂ) ^ (k - j) * (Nat.choose k j : ℂ)
        * ∏ i : Fin N, (v i (idx i) + ((j : ℂ) * ε) * w i (idx i))
    = ∑ j ∈ range (k + 1),
      (-1 : ℂ) ^ (k - j) * (Nat.choose k j : ℂ)
        * ∑ A : Finset (Fin N), ((j : ℂ) * ε) ^ A.card * eS d v w idx A := by
    refine sum_congr rfl ?_
    intro j _hj
    rw [hP j]
  rw [hsum]
  have hswap : ∑ j ∈ range (k + 1),
      (-1 : ℂ) ^ (k - j) * (Nat.choose k j : ℂ)
        * ∑ A : Finset (Fin N), ((j : ℂ) * ε) ^ A.card * eS d v w idx A
    = ∑ A : Finset (Fin N),
        ∑ j ∈ range (k + 1),
          (-1 : ℂ) ^ (k - j) * (Nat.choose k j : ℂ)
            * (((j : ℂ) * ε) ^ A.card * eS d v w idx A) := by
    rw [sum_comm]
    refine sum_congr rfl ?_
    intro A _hA
    rw [← mul_sum]
  rw [hswap]
  have hinner : ∀ A : Finset (Fin N),
      ∑ j ∈ range (k + 1),
        (-1 : ℂ) ^ (k - j) * (Nat.choose k j : ℂ)
          * (((j : ℂ) * ε) ^ A.card * eS d v w idx A)
      = ε ^ A.card * eS d v w idx A * UniformBorderRank.S A.card k := by
    intro A
    have h : ∑ j ∈ range (k + 1),
        (-1 : ℂ) ^ (k - j) * (Nat.choose k j : ℂ)
          * (((j : ℂ) * ε) ^ A.card * eS d v w idx A)
      = eS d v w idx A * ∑ j ∈ range (k + 1),
          (-1 : ℂ) ^ (k - j) * (Nat.choose k j : ℂ) * ((j : ℂ) * ε) ^ A.card := by
      have h1 : ∑ j ∈ range (k + 1),
          (-1 : ℂ) ^ (k - j) * (Nat.choose k j : ℂ)
            * (((j : ℂ) * ε) ^ A.card * eS d v w idx A)
        = ∑ j ∈ range (k + 1),
            eS d v w idx A *
              ((-1 : ℂ) ^ (k - j) * (Nat.choose k j : ℂ) * ((j : ℂ) * ε) ^ A.card) := by
        refine sum_congr rfl ?_
        intro j _hj
        ring
      rw [h1, ← mul_sum]
    rw [h, sum_alt_pow]
    ring
  rw [show (∑ A : Finset (Fin N),
      ∑ j ∈ range (k + 1),
        (-1 : ℂ) ^ (k - j) * (Nat.choose k j : ℂ)
          * (((j : ℂ) * ε) ^ A.card * eS d v w idx A))
      = ∑ A : Finset (Fin N), ε ^ A.card * eS d v w idx A * UniformBorderRank.S A.card k from
      sum_congr rfl (fun A _ => hinner A)]
  rw [mul_sum]

/-- Terms with `|A| < k` vanish (`S_of_lt`). -/
lemma fdTerm_lt {N : ℕ} (d : Fin N → ℕ)
    (v w : ∀ i : Fin N, Fin (d i) → ℂ) (k : ℕ) (ε : ℂ) (idx : ∀ i, Fin (d i))
    (A : Finset (Fin N)) (hlt : A.card < k) :
    ((1 : ℂ) / (Nat.factorial k : ℂ)) * (ε ^ k)⁻¹
      * (ε ^ A.card * eS d v w idx A * UniformBorderRank.S A.card k) = 0 := by
  have hS0 : UniformBorderRank.S A.card k = 0 := S_of_lt A.card k hlt
  rw [hS0]
  ring

/-- Diagonal term `|A| = k` equals `eS` (`S_self` cancels `k!`), for `ε ≠ 0`. -/
lemma fdTerm_eq {N : ℕ} (d : Fin N → ℕ)
    (v w : ∀ i : Fin N, Fin (d i) → ℂ) (k : ℕ) (ε : ℂ) (idx : ∀ i, Fin (d i))
    (A : Finset (Fin N)) (heq : A.card = k) (hε : ε ≠ 0) :
    ((1 : ℂ) / (Nat.factorial k : ℂ)) * (ε ^ k)⁻¹
      * (ε ^ A.card * eS d v w idx A * UniformBorderRank.S A.card k)
      = eS d v w idx A := by
  have hS : UniformBorderRank.S k k = (Nat.factorial k : ℂ) := S_self k
  by_cases hk0 : k = 0
  · subst hk0
    have hA : A.card = 0 := heq
    simp [hA, hS]
  · have hpow : ε ^ k ≠ 0 := pow_ne_zero k hε
    have hfact : ((Nat.factorial k : ℂ)) ≠ 0 :=
      by exact_mod_cast (Nat.factorial_ne_zero k)
    have hcalc : ((1 : ℂ) / (Nat.factorial k : ℂ)) * (ε ^ k)⁻¹
        * (ε ^ k * eS d v w idx A * (Nat.factorial k : ℂ))
      = eS d v w idx A := by
      field_simp [hpow, hfact]
    rw [heq, hS]
    exact hcalc

/-- Tail term `|A| > k` carries a factor `ε^{|A|-k}`. -/
lemma fdTerm_tail_form {N : ℕ} (d : Fin N → ℕ)
    (v w : ∀ i : Fin N, Fin (d i) → ℂ) (k : ℕ) (ε : ℂ) (idx : ∀ i, Fin (d i))
    (A : Finset (Fin N)) (hgt : k < A.card) (hε : ε ≠ 0) :
    ((1 : ℂ) / (Nat.factorial k : ℂ)) * (ε ^ k)⁻¹
      * (ε ^ A.card * eS d v w idx A * UniformBorderRank.S A.card k)
      = ε ^ (A.card - k) *
          (eS d v w idx A * (UniformBorderRank.S A.card k / (Nat.factorial k : ℂ))) := by
  have hk : k ≤ A.card := by omega
  have hpow : ε ^ A.card * (ε ^ k)⁻¹ = ε ^ (A.card - k) := by
    have h1 : ε ^ A.card = ε ^ ((A.card - k) + k) := by
      congr 1
      omega
    rw [h1, pow_add, mul_assoc]
    rw [mul_inv_cancel₀ (pow_ne_zero k hε), mul_one]
  calc ((1 : ℂ) / (Nat.factorial k : ℂ)) * (ε ^ k)⁻¹
        * (ε ^ A.card * eS d v w idx A * UniformBorderRank.S A.card k)
      = ((1 : ℂ) / (Nat.factorial k : ℂ)) * (ε ^ A.card * (ε ^ k)⁻¹)
          * (eS d v w idx A * UniformBorderRank.S A.card k) := by
        ring
    _ = ε ^ (A.card - k) * ((1 : ℂ) / (Nat.factorial k : ℂ))
          * (eS d v w idx A * UniformBorderRank.S A.card k) := by
        rw [hpow]
        ring
    _ = ε ^ (A.card - k) *
          (eS d v w idx A * (UniformBorderRank.S A.card k / (Nat.factorial k : ℂ))) := by
        rw [div_eq_mul_inv]
        ring

end UniformBorderRank
