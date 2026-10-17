import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-!
# Finite differences of monomials (paper (13) algebra)

`S m k = ∑_{j=0}^k (-1)^{k-j} C(k,j) * (j:ℂ)^m`.

* `S m k = 0` for `m < k`  (low-order differences vanish)
* `S k k = (k! : ℂ)`       (the `k`-th difference of `t^k` is `k!`)
-/

noncomputable section

namespace UniformBorderRank

open Finset

/-- `k`-th forward difference of `j ↦ j^m` at `0` with step `1`, over `ℂ`. -/
def S (m k : ℕ) : ℂ :=
  ∑ j ∈ range (k + 1), (-1 : ℂ) ^ (k - j) * (Nat.choose k j : ℂ) * (j : ℂ) ^ m

/-- `C(k, j-1)` with the convention `C(k, -1) = 0`. -/
def choosePred (k j : ℕ) : ℕ := if j = 0 then 0 else Nat.choose k (j - 1)

lemma pow_add_one (i m : ℕ) :
    ((i + 1 : ℕ) : ℂ) ^ m = ∑ r ∈ range (m + 1), (Nat.choose m r : ℂ) * (i : ℂ) ^ r := by
  have h := add_pow (i : ℂ) (1 : ℂ) m
  rw [Nat.cast_add_one, h]
  refine sum_congr rfl ?_
  intro r _hr
  rw [one_pow, mul_one, mul_comm]

lemma hpascal (k j : ℕ) : (Nat.choose (k + 1) j : ℂ)
    = (Nat.choose k j : ℂ) + (choosePred k j : ℂ) := by
  unfold choosePred
  by_cases h0 : j = 0
  · subst h0
    simp
  · rw [if_neg h0]
    by_cases h1 : k + 1 < j
    · have h2 : k < j := by omega
      have ha : (Nat.choose (k + 1) j : ℂ) = 0 := by
        rw [Nat.choose_eq_zero_of_lt h1]; norm_cast
      have hb : (Nat.choose k j : ℂ) = 0 := by
        rw [Nat.choose_eq_zero_of_lt h2]; norm_cast
      have hc : (Nat.choose k (j - 1) : ℂ) = 0 := by
        rw [Nat.choose_eq_zero_of_lt (by omega : k < j - 1)]; norm_cast
      rw [ha, hb, hc]; ring
    · have hjk : j ≤ k ∨ j = k + 1 := by omega
      rcases hjk with hjk | hjk
      · have hj1 : 0 < j := by omega
        have h := Nat.choose_succ_succ k (j - 1)
        have h2 : (j - 1).succ = j := Nat.succ_pred_eq_of_ne_zero hj1.ne'
        rw [h2] at h
        have h3 : k.succ = k + 1 := rfl
        rw [h3] at h
        rw [h]
        push_cast
        ring
      · subst hjk
        simp [Nat.choose_self]

lemma S_succ (m k : ℕ) :
    S m (k + 1) = ∑ i ∈ range m, (Nat.choose m i : ℂ) * S i k := by
  unfold S
  have hsplit :
      ∑ j ∈ range (k + 2),
        (-1 : ℂ) ^ (k + 1 - j) * (Nat.choose (k + 1) j : ℂ) * (j : ℂ) ^ m
      = (∑ j ∈ range (k + 1),
          (-1 : ℂ) ^ (k + 1 - j) * (Nat.choose k j : ℂ) * (j : ℂ) ^ m)
        + (∑ i ∈ range (k + 1),
          (-1 : ℂ) ^ (k - i) * (Nat.choose k i : ℂ) * ((i + 1 : ℕ) : ℂ) ^ m) := by
    have h1 : ∑ j ∈ range (k + 2),
        (-1 : ℂ) ^ (k + 1 - j) * (Nat.choose (k + 1) j : ℂ) * (j : ℂ) ^ m
      = ∑ j ∈ range (k + 2),
        (-1 : ℂ) ^ (k + 1 - j) *
          ((Nat.choose k j : ℂ) + (choosePred k j : ℂ)) * (j : ℂ) ^ m := by
      refine sum_congr rfl ?_
      intro j _hj
      rw [hpascal k j]
    rw [h1]
    have h2 : ∑ j ∈ range (k + 2),
        (-1 : ℂ) ^ (k + 1 - j) *
          ((Nat.choose k j : ℂ) + (choosePred k j : ℂ)) * (j : ℂ) ^ m
      = (∑ j ∈ range (k + 2),
          (-1 : ℂ) ^ (k + 1 - j) * (Nat.choose k j : ℂ) * (j : ℂ) ^ m)
        + (∑ j ∈ range (k + 2),
          (-1 : ℂ) ^ (k + 1 - j) * (choosePred k j : ℂ) * (j : ℂ) ^ m) := by
      rw [← sum_add_distrib]
      refine sum_congr rfl ?_
      intro j _hj
      ring
    rw [h2]
    have hfirst : ∑ j ∈ range (k + 2),
        (-1 : ℂ) ^ (k + 1 - j) * (Nat.choose k j : ℂ) * (j : ℂ) ^ m
      = ∑ j ∈ range (k + 1),
          (-1 : ℂ) ^ (k + 1 - j) * (Nat.choose k j : ℂ) * (j : ℂ) ^ m := by
      rw [sum_range_succ]
      have : (Nat.choose k (k + 1) : ℂ) = 0 := by
        rw [Nat.choose_eq_zero_of_lt (by omega)]; norm_cast
      rw [this]
      simp
    have hsecond : ∑ j ∈ range (k + 2),
        (-1 : ℂ) ^ (k + 1 - j) * (choosePred k j : ℂ) * (j : ℂ) ^ m
      = ∑ i ∈ range (k + 1),
          (-1 : ℂ) ^ (k - i) * (Nat.choose k i : ℂ) * ((i + 1 : ℕ) : ℂ) ^ m := by
      have hshift : ∑ j ∈ range (k + 2),
          (-1 : ℂ) ^ (k + 1 - j) * (choosePred k j : ℂ) * (j : ℂ) ^ m
        = ∑ i ∈ range (k + 1),
          (-1 : ℂ) ^ (k - i) * (Nat.choose k i : ℂ) * ((i + 1 : ℕ) : ℂ) ^ m := by
        rw [sum_range_succ']
        have h0 : (-1 : ℂ) ^ (k + 1 - 0) * (choosePred k 0 : ℂ) * ((0 : ℕ) : ℂ) ^ m = 0 := by
          unfold choosePred
          simp
        rw [h0]
        simp
        refine sum_congr rfl ?_
        intro i _hi
        rfl
      exact hshift
    rw [hfirst, hsecond]
  have hA : ∑ j ∈ range (k + 1),
      (-1 : ℂ) ^ (k + 1 - j) * (Nat.choose k j : ℂ) * (j : ℂ) ^ m = - S m k := by
    have : ∑ j ∈ range (k + 1),
        (-1 : ℂ) ^ (k + 1 - j) * (Nat.choose k j : ℂ) * (j : ℂ) ^ m
      = - ∑ j ∈ range (k + 1),
          (-1 : ℂ) ^ (k - j) * (Nat.choose k j : ℂ) * (j : ℂ) ^ m := by
      have hneg : ∑ j ∈ range (k + 1),
          (-1 : ℂ) ^ (k + 1 - j) * (Nat.choose k j : ℂ) * (j : ℂ) ^ m
        = ∑ j ∈ range (k + 1),
          - ((-1 : ℂ) ^ (k - j) * (Nat.choose k j : ℂ) * (j : ℂ) ^ m) := by
        refine sum_congr rfl ?_
        intro j hj
        have hj' : j ≤ k := by
          have := mem_range.1 hj
          omega
        have hz : (-1 : ℂ) ^ (k + 1 - j) = - ((-1 : ℂ) ^ (k - j)) := by
          have h : k + 1 - j = (k - j) + 1 := by omega
          rw [h, pow_succ]
          ring
        rw [hz]
        ring
      rw [hneg, sum_neg_distrib]
    rw [this]
    rfl
  have hB : ∑ i ∈ range (k + 1),
      (-1 : ℂ) ^ (k - i) * (Nat.choose k i : ℂ) * ((i + 1 : ℕ) : ℂ) ^ m
    = ∑ r ∈ range (m + 1), (Nat.choose m r : ℂ) * S r k := by
    have hexp : ∑ i ∈ range (k + 1),
        (-1 : ℂ) ^ (k - i) * (Nat.choose k i : ℂ) * ((i + 1 : ℕ) : ℂ) ^ m
      = ∑ i ∈ range (k + 1),
        (-1 : ℂ) ^ (k - i) * (Nat.choose k i : ℂ) *
          (∑ r ∈ range (m + 1), (Nat.choose m r : ℂ) * (i : ℂ) ^ r) := by
      refine sum_congr rfl ?_
      intro i _hi
      rw [pow_add_one i m]
    rw [hexp]
    have hmul : ∑ i ∈ range (k + 1),
        (-1 : ℂ) ^ (k - i) * (Nat.choose k i : ℂ) *
          (∑ r ∈ range (m + 1), (Nat.choose m r : ℂ) * (i : ℂ) ^ r)
      = ∑ i ∈ range (k + 1),
          ∑ r ∈ range (m + 1),
            (-1 : ℂ) ^ (k - i) * (Nat.choose k i : ℂ) *
              ((Nat.choose m r : ℂ) * (i : ℂ) ^ r) := by
      refine sum_congr rfl ?_
      intro i _hi
      rw [Finset.mul_sum]
    rw [hmul, Finset.sum_comm]
    refine sum_congr rfl ?_
    intro r _hr
    have hfac : ∑ i ∈ range (k + 1),
        (-1 : ℂ) ^ (k - i) * (Nat.choose k i : ℂ) *
          ((Nat.choose m r : ℂ) * (i : ℂ) ^ r)
      = (Nat.choose m r : ℂ) * S r k := by
      have hre2 : ∑ i ∈ range (k + 1),
          (-1 : ℂ) ^ (k - i) * (Nat.choose k i : ℂ) *
            ((Nat.choose m r : ℂ) * (i : ℂ) ^ r)
        = ∑ i ∈ range (k + 1),
            (Nat.choose m r : ℂ) *
              ((-1 : ℂ) ^ (k - i) * (Nat.choose k i : ℂ) * (i : ℂ) ^ r) := by
        refine sum_congr rfl ?_
        intro i _hi
        ring
      rw [hre2, ← Finset.mul_sum]
      rfl
    rw [hfac]
  -- Assemble: LHS = first + second = -S m k + ∑_{r≤m} C(m,r) S r k
  rw [hsplit, hA, hB, sum_range_succ]
  have hsm : (Nat.choose m m : ℂ) * S m k = S m k := by
    rw [Nat.choose_self]; norm_cast; ring
  rw [hsm]
  -- cancel -S m k + S m k
  have hcancel : - S m k + (∑ i ∈ range m, (Nat.choose m i : ℂ) * S i k + S m k)
      = ∑ i ∈ range m, (Nat.choose m i : ℂ) * S i k := by
    ring
  rw [hcancel]
  -- RHS uses unfolded S; convert
  have hS : ∀ i, S i k = ∑ j ∈ range (k + 1),
      (-1 : ℂ) ^ (k - j) * (Nat.choose k j : ℂ) * (j : ℂ) ^ i := fun _ => rfl
  refine sum_congr rfl ?_
  intro i _hi
  rw [hS]

lemma S_of_lt (m k : ℕ) (h : m < k) : S m k = 0 := by
  induction k generalizing m with
  | zero => omega
  | succ k ih =>
    rw [S_succ]
    apply sum_eq_zero
    intro i hi
    have hi' : i < m := mem_range.1 hi
    have hik : i < k := by omega
    rw [ih i hik, mul_zero]

lemma S_self : ∀ k : ℕ, S k k = (Nat.factorial k : ℂ)
  | 0 => by simp [S]
  | k + 1 => by
    rw [S_succ]
    have hsplit : ∑ i ∈ range (k + 1), (Nat.choose (k + 1) i : ℂ) * S i k
        = (Nat.choose (k + 1) k : ℂ) * S k k := by
      rw [sum_range_succ]
      have h1 : ∑ i ∈ range k, (Nat.choose (k + 1) i : ℂ) * S i k = 0 := by
        apply sum_eq_zero
        intro i hi
        have hi' : i < k := mem_range.1 hi
        rw [S_of_lt i k hi', mul_zero]
      rw [h1, zero_add]
    rw [hsplit, S_self k]
    have hch : (Nat.choose (k + 1) k : ℂ) = (k + 1 : ℂ) := by
      have := Nat.choose_succ_self_right k
      rw [this]
      norm_cast
    rw [hch]
    norm_cast

end UniformBorderRank
