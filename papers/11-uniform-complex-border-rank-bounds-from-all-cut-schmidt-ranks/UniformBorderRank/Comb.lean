import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

/-!
# Lemma 3.1: the combinatorial function `F`

Formalization of Lemma 3.1 of
"Uniform complex border-rank bounds from all-cut Schmidt ranks".
-/

namespace UniformBorderRank

open Nat Finset

/-- Sum form of `F`. -/
def Fsum (q : ℕ) : ℕ :=
  ∑ k ∈ range q, (k + 1) * (q + k - 2).choose k

/-- Closed form of `F` (official definition). -/
def F (q : ℕ) : ℕ :=
  if q = 1 then 1
  else (2 * q - 2).choose (q - 1) + (q - 1) * (2 * q - 2).choose (q - 2)

@[simp] lemma F_one : F 1 = 1 := by
  simp [F]

lemma F_of_two_le {q : ℕ} (hq : 2 ≤ q) :
    F q = (2 * q - 2).choose (q - 1) + (q - 1) * (2 * q - 2).choose (q - 2) := by
  have hne : q ≠ 1 := by omega
  simp [F, hne]

/-- `k * C(n,k) = (n - (k-1)) * C(n, k-1)` for `k ≥ 1`. -/
lemma mul_choose_pred (n k : ℕ) (hk : 1 ≤ k) :
    k * n.choose k = (n - (k - 1)) * n.choose (k - 1) := by
  have h := Nat.choose_succ_right_eq n (k - 1)
  have hk1 : k - 1 + 1 = k := by omega
  rw [hk1] at h
  have : k * n.choose k = n.choose k * k := by ring
  rw [this, h, mul_comm]

/-- Paper identity: `k * C(q+k-2, k) = (q-1) * C(q+k-2, k-1)` for `k ≥ 1`. -/
lemma k_choose_identity (q k : ℕ) (hk : 1 ≤ k) :
    k * (q + k - 2).choose k = (q - 1) * (q + k - 2).choose (k - 1) := by
  have h := mul_choose_pred (q + k - 2) k hk
  have hs : (q + k - 2) - (k - 1) = q - 1 := by omega
  rw [hs] at h
  exact h

lemma choose_symm' {n k : ℕ} (hk : k ≤ n) : n.choose k = n.choose (n - k) :=
  (Nat.choose_symm hk).symm

/-- Unweighted sum: `∑_{k=0}^{q-1} C(q+k-2, k) = C(2q-2, q-1)` for `q ≥ 2`. -/
lemma sum_choose_F_unweighted (q : ℕ) (hq : 2 ≤ q) :
    ∑ k ∈ range q, (q + k - 2).choose k = (2 * q - 2).choose (q - 1) := by
  have hterm : ∀ k ∈ range q, (q + k - 2).choose k = ((q - 2) + k).choose (q - 2) := by
    intro k hk
    have hk' : k < q := mem_range.mp hk
    have heq : q + k - 2 = (q - 2) + k := by omega
    rw [heq]
    have hle : k ≤ (q - 2) + k := Nat.le_add_left _ _
    have h := choose_symm' hle
    have hsub : (q - 2) + k - k = q - 2 := by omega
    rw [hsub] at h
    exact h
  rw [sum_congr rfl hterm]
  have h := sum_range_add_choose (q - 1) (q - 2)
  have hL : ∑ i ∈ range ((q - 1) + 1), (i + (q - 2)).choose (q - 2)
      = ∑ k ∈ range q, ((q - 2) + k).choose (q - 2) := by
    have hrange : (q - 1) + 1 = q := by omega
    rw [hrange]
    exact sum_congr rfl (fun k _ => by rw [add_comm])
  have hR : q - 1 + (q - 2) + 1 = 2 * q - 2 := by omega
  have hRk : (q - 2) + 1 = q - 1 := by omega
  rw [hR, hRk] at h
  rw [← hL]
  exact h

/-- Weighted sum: `∑_{k=0}^{q-1} k * C(q+k-2, k) = (q-1) * C(2q-2, q-2)` for `q ≥ 2`. -/
lemma sum_choose_F_weighted (q : ℕ) (hq : 2 ≤ q) :
    ∑ k ∈ range q, k * (q + k - 2).choose k = (q - 1) * (2 * q - 2).choose (q - 2) := by
  have hsplit :
      ∑ k ∈ range q, k * (q + k - 2).choose k
        = ∑ k ∈ range q, (if k = 0 then 0 else (q - 1) * (q + k - 2).choose (k - 1)) := by
    refine sum_congr rfl ?_
    intro k _hk
    by_cases hk0 : k = 0
    · subst hk0; simp
    · have hk1 : 1 ≤ k := by omega
      rw [if_neg hk0]
      exact k_choose_identity q k hk1
  rw [hsplit]
  have hshift :
      ∑ k ∈ range q, (if k = 0 then 0 else (q - 1) * (q + k - 2).choose (k - 1))
        = ∑ j ∈ range (q - 1), (q - 1) * ((q - 1) + j).choose j := by
    have hsum : ∑ k ∈ range q, (if k = 0 then 0 else (q - 1) * (q + k - 2).choose (k - 1))
        = ∑ k ∈ range ((q - 1) + 1), (if k = 0 then 0 else (q - 1) * (q + k - 2).choose (k - 1)) := by
      congr 1
      exact congr_arg range (Nat.sub_add_cancel (by omega : 1 ≤ q)).symm
    rw [hsum, sum_range_succ']
    have h0 : (if (0 : ℕ) = 0 then 0 else (q - 1) * (q + 0 - 2).choose (0 - 1)) = 0 := by
      simp
    rw [h0, add_zero]
    refine sum_congr rfl ?_
    intro j hj
    have hj' : j < q - 1 := mem_range.mp hj
    have hne : (j + 1 : ℕ) ≠ 0 := by omega
    rw [if_neg hne]
    have heq : q + (j + 1) - 2 = (q - 1) + j := by omega
    rw [heq, Nat.add_sub_cancel]
  rw [hshift, ← mul_sum]
  have hterm : ∀ j ∈ range (q - 1), ((q - 1) + j).choose j = ((q - 1) + j).choose (q - 1) := by
    intro j hj
    have hj' : j < q - 1 := mem_range.mp hj
    have hle : q - 1 ≤ (q - 1) + j := Nat.le_add_right _ _
    have h := choose_symm' hle
    have hsub : (q - 1) + j - (q - 1) = j := by omega
    rw [hsub] at h
    exact h.symm
  rw [sum_congr rfl hterm]
  have h := sum_range_add_choose (q - 2) (q - 1)
  have hrange : (q - 2) + 1 = q - 1 := by omega
  have hR : (q - 2) + (q - 1) + 1 = 2 * q - 2 := by omega
  have hRk : (q - 1) + 1 = q := by omega
  rw [hrange, hR, hRk] at h
  have hsum : ∑ j ∈ range (q - 1), ((q - 1) + j).choose (q - 1)
      = ∑ i ∈ range (q - 1), (i + (q - 1)).choose (q - 1) :=
    sum_congr rfl (fun j _ => by rw [add_comm])
  rw [hsum, h]
  have hle : q ≤ 2 * q - 2 := by omega
  have hsym := choose_symm' hle
  have hsub : 2 * q - 2 - q = q - 2 := by omega
  rw [hsub] at hsym
  have key : (q - 1) * (2 * q - 2).choose q = (q - 1) * (2 * q - 2).choose (q - 2) := by
    rw [hsym]
  have hmul : (q - 1) * (2 * q - 2).choose (q - 2) = (q - 1) * (2 * q - 2).choose (q - 2) := rfl
  rw [← key, hsym]

/-- Lemma 3.1 (first half): the two expressions for `F` agree. -/
lemma Fsum_eq_F (q : ℕ) (hq : 2 ≤ q) : Fsum q = F q := by
  rw [F_of_two_le hq]
  unfold Fsum
  have hsplit :
      ∑ k ∈ range q, (k + 1) * (q + k - 2).choose k
        = (∑ k ∈ range q, (q + k - 2).choose k)
          + (∑ k ∈ range q, k * (q + k - 2).choose k) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl (fun k _ => by ring)
  rw [hsplit, sum_choose_F_unweighted q hq, sum_choose_F_weighted q hq]



/-- `n^2 * C(2n, n) = 2n * (2n-1) * C(2n-2, n-1)` for `n ≥ 1`. -/
lemma sq_mul_choose_two (n : ℕ) (hn : 1 ≤ n) :
    (n : ℕ) ^ 2 * (2 * n).choose n = 2 * n * (2 * n - 1) * (2 * n - 2).choose (n - 1) := by
  have h1 : (2 * n).choose n * n ! * n ! = (2 * n) ! := by
    have h := Nat.choose_mul_factorial_mul_factorial (k := n) (by omega : n ≤ 2 * n)
    have : 2 * n - n = n := by omega
    rw [this] at h
    exact h
  have hk : n - 1 ≤ 2 * n - 2 := by omega
  have h2 : (2 * n - 2).choose (n - 1) * (n - 1) ! * ((2 * n - 2) - (n - 1)) ! = (2 * n - 2) ! :=
    Nat.choose_mul_factorial_mul_factorial hk
  have hsub : (2 * n - 2) - (n - 1) = n - 1 := by omega
  rw [hsub] at h2
  have hnfac : (n : ℕ)! = n * (n - 1) ! := by
    rw [← Nat.mul_factorial_pred (by omega : n ≠ 0)]
  have h2n : (2 * n : ℕ)! = 2 * n * (2 * n - 1) * (2 * n - 2) ! := by
    have e1 : (2 * n)! = 2 * n * (2 * n - 1) ! := by
      rw [← Nat.mul_factorial_pred (by omega : 2 * n ≠ 0)]
    have e2 : (2 * n - 1)! = (2 * n - 1) * (2 * n - 2) ! := by
      exact (Nat.mul_factorial_pred (by omega : 2 * n - 1 ≠ 0)).symm
    rw [e1, e2]
    ring
  have hne : ((n - 1 : ℕ)!) ^ 2 ≠ 0 := pow_ne_zero 2 (Nat.factorial_ne_zero _)
  have h2' : (2 * n - 2).choose (n - 1) * ((n - 1) !) ^ 2 = (2 * n - 2) ! := by
    have hs : (n - 1 : ℕ)! * (n - 1)! = ((n - 1)!) ^ 2 := by ring
    rw [← hs, ← mul_assoc]
    exact h2
  have h1' : (2 * n).choose n * n ! * n ! = 2 * n * (2 * n - 1) * (2 * n - 2) ! :=
    h1.trans h2n
  have hsqr : (n : ℕ) ^ 2 * ((n - 1)!) ^ 2 = (n !) ^ 2 := by
    have e : (n !) ^ 2 = (n * (n - 1) !) ^ 2 := by rw [← hnfac]
    rw [e]
    ring
  have key : (n ^ 2 * (2 * n).choose n) * ((n - 1)!) ^ 2
      = (2 * n * (2 * n - 1) * (2 * n - 2).choose (n - 1)) * ((n - 1)!) ^ 2 := by
    have hL : (n : ℕ) ^ 2 * (2 * n).choose n * ((n - 1)!) ^ 2
        = (2 * n).choose n * n ! * n ! := by
      have e : n ^ 2 * (2 * n).choose n * ((n - 1)!) ^ 2
          = (2 * n).choose n * (n ^ 2 * ((n - 1)!) ^ 2) := by ring
      rw [e, hsqr]
      ring
    rw [hL, h1', ← h2']
    ring
  exact Nat.mul_right_cancel (Nat.pos_of_ne_zero hne) key

/-- `n * C(2n-2, n-2) = (n-1) * C(2n-2, n-1)` for `n ≥ 2`. -/
lemma n_mul_choose_complement (n : ℕ) (hn : 2 ≤ n) :
    n * (2 * n - 2).choose (n - 2) = (n - 1) * (2 * n - 2).choose (n - 1) := by
  have h := Nat.choose_succ_right_eq (2 * n - 2) (n - 2)
  have hsub : 2 * n - 2 - (n - 2) = n := by omega
  have hk : (n - 2) + 1 = n - 1 := by omega
  rw [hk, hsub, mul_comm] at h
  linarith

/-- `n^2 * (2n-1) ≥ (n-1)^2 * (n+1)` for `n ≥ 2`. -/
lemma growth_sq (n : ℕ) (hn : 2 ≤ n) :
    n ^ 2 * (2 * n - 1) ≥ (n - 1) ^ 2 * (n + 1) := by
  have hz : (((n - 1 : ℕ) ^ 2 * (n + 1) : ℕ) : ℤ) ≤ (((n : ℕ) ^ 2 * (2 * n - 1) : ℕ) : ℤ) := by
    have hc1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
    have hc2 : ((2 * n - 1 : ℕ) : ℤ) = 2 * (n : ℤ) - 1 := by omega
    have hc3 : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by omega
    simp only [Nat.cast_mul, Nat.cast_pow, hc1, hc2, hc3]
    have hn' : (2 : ℤ) ≤ n := by exact_mod_cast hn
    have e1 : ((n : ℤ) - 1) ^ 2 * (n + 1) = n ^ 3 - n ^ 2 - n + 1 := by ring
    have e2 : (n : ℤ) ^ 2 * (2 * n - 1) = 2 * n ^ 3 - n ^ 2 := by ring
    rw [e1, e2]
    nlinarith [show (1 : ℤ) ≤ n from by omega]
  exact Nat.cast_le.1 hz

/-- `n * C(2n, n) = (n+1) * C(2n, n-1)` for `n ≥ 1`. -/
lemma choose_two_mul_rel (n : ℕ) (hn : 1 ≤ n) :
    n * (2 * n).choose n = (n + 1) * (2 * n).choose (n - 1) := by
  have h := Nat.choose_succ_right_eq (2 * n) (n - 1)
  have hk : (n - 1) + 1 = n := by omega
  have hsub : 2 * n - (n - 1) = n + 1 := by omega
  rw [hk, hsub] at h
  linarith

/-- Core growth: `2 * F n ≤ F (n+1)` for `n ≥ 2`. -/
lemma two_mul_F_le_succ (n : ℕ) (hn : 2 ≤ n) : 2 * F n ≤ F (n + 1) := by
  have hn1 : 2 ≤ n + 1 := by omega
  rw [F_of_two_le hn, F_of_two_le hn1]
  have hsimp : (2 * (n + 1) - 2) = 2 * n ∧ (n + 1 - 1) = n ∧ (n + 1 - 2) = n - 1 := by
    omega
  obtain ⟨hs1, hs2, hs3⟩ := hsimp
  rw [hs1, hs2, hs3]
  have hA : 2 * (2 * n - 2).choose (n - 1) ≤ (2 * n).choose n := by
    have h := sq_mul_choose_two n (by omega : 1 ≤ n)
    have key : n ^ 2 * (2 * (2 * n - 2).choose (n - 1)) ≤ n ^ 2 * (2 * n).choose n := by
      rw [h]
      have hle : (n : ℕ) ^ 2 * 2 ≤ 2 * n * (2 * n - 1) := by
        have : (n : ℕ) ^ 2 * 2 = 2 * n * n := by ring
        rw [this]
        exact Nat.mul_le_mul_left (2 * n) (by omega : n ≤ 2 * n - 1)
      -- n^2 * (2 * C') ≤ 2n(2n-1) C'
      have hL : (n : ℕ) ^ 2 * (2 * (2 * n - 2).choose (n - 1))
          = (n ^ 2 * 2) * (2 * n - 2).choose (n - 1) := by ring
      rw [hL]
      exact Nat.mul_le_mul_right _ hle
    exact Nat.le_of_mul_le_mul_left key (by positivity : 0 < n ^ 2)
  have hB : 2 * (n - 1) * (2 * n - 2).choose (n - 2) ≤ n * (2 * n).choose (n - 1) := by
    have hcomp := n_mul_choose_complement n (by omega : 2 ≤ n)
    have hrel := choose_two_mul_rel n (by omega : 1 ≤ n)
    have hs := sq_mul_choose_two n (by omega : 1 ≤ n)
    have hgs := growth_sq n (by omega : 2 ≤ n)
    have hpos : 0 < n * (n + 1) := Nat.mul_pos (by omega) (by omega)
    have goal' : 2 * (n - 1) * (2 * n - 2).choose (n - 2) * (n * (n + 1))
        ≤ n * (2 * n).choose (n - 1) * (n * (n + 1)) := by
      have hL0 : 2 * (n - 1) * (2 * n - 2).choose (n - 2) * (n * (n + 1))
          = 2 * (n - 1) * (n + 1) * (n * (2 * n - 2).choose (n - 2)) := by
        ring
      have hR0 : n * (2 * n).choose (n - 1) * (n * (n + 1))
          = n * n * ((n + 1) * (2 * n).choose (n - 1)) := by
        ring
      rw [hL0, hR0, hcomp, ← hrel]
      -- LHS = 2(n-1)(n+1)(n-1) C' = 2(n-1)^2 (n+1) C'
      -- RHS = n * n * [n C(2n,n)] = n^3 C(2n,n)
      have hL : 2 * (n - 1) * (n + 1) * ((n - 1) * (2 * n - 2).choose (n - 1))
          = 2 * (n - 1) ^ 2 * (n + 1) * (2 * n - 2).choose (n - 1) := by
        ring
      have hR : n * n * (n * (2 * n).choose n) = n ^ 3 * (2 * n).choose n := by
        ring
      rw [hL, hR]
      have hR2 : n ^ 3 * (2 * n).choose n
          = 2 * n ^ 2 * (2 * n - 1) * (2 * n - 2).choose (n - 1) := by
        have hnn : (n : ℕ) ^ 3 = n * n ^ 2 := by ring
        rw [hnn]
        have : n * n ^ 2 * (2 * n).choose n = n * (n ^ 2 * (2 * n).choose n) := by ring
        rw [this, hs]
        ring
      rw [hR2]
      have hmul : 2 * (n - 1) ^ 2 * (n + 1) * (2 * n - 2).choose (n - 1)
          ≤ 2 * n ^ 2 * (2 * n - 1) * (2 * n - 2).choose (n - 1) := by
        apply Nat.mul_le_mul_right
        have h1 : (2 * (n - 1) ^ 2 * (n + 1) : ℕ) = 2 * ((n - 1) ^ 2 * (n + 1)) := by ring
        have h2 : (2 * n ^ 2 * (2 * n - 1) : ℕ) = 2 * (n ^ 2 * (2 * n - 1)) := by ring
        rw [h1, h2]
        exact Nat.mul_le_mul_left 2 hgs
      exact hmul
    exact Nat.le_of_mul_le_mul_right goal' hpos
  have hsplit : 2 * ((2 * n - 2).choose (n - 1) + (n - 1) * (2 * n - 2).choose (n - 2))
      = 2 * (2 * n - 2).choose (n - 1) + 2 * ((n - 1) * (2 * n - 2).choose (n - 2)) := by
    ring
  rw [hsplit]
  have hB' : 2 * ((n - 1) * (2 * n - 2).choose (n - 2)) ≤ n * (2 * n).choose (n - 1) := by
    have : 2 * ((n - 1) * (2 * n - 2).choose (n - 2))
        = 2 * (n - 1) * (2 * n - 2).choose (n - 2) := by ring
    rw [this]
    exact hB
  omega

/-- `F` is strictly increasing: `F (q-1) < F q` for `q ≥ 2`. -/
lemma F_lt_succ {q : ℕ} (hq : 2 ≤ q) : F (q - 1) < F q := by
  have h2 : 2 * F (q - 1) ≤ F ((q - 1) + 1) ∨ q - 1 = 1 := by
    by_cases h : 2 ≤ q - 1
    · exact Or.inl (two_mul_F_le_succ (q - 1) h)
    · exact Or.inr (by omega)
  rcases h2 with h2 | h1
  · have hrew : (q - 1) + 1 = q := by omega
    rw [hrew] at h2
    have hpos : 0 < F (q - 1) := by
      have h2' : 2 ≤ q - 1 ∨ q - 1 = 1 := by omega
      rcases h2' with h2' | h2'
      · have hF := F_of_two_le h2'
        have hC : 0 < (2 * (q - 1) - 2).choose ((q - 1) - 1) := by
          apply Nat.choose_pos; omega
        omega
      · have hq : (q - 1 : ℕ) = 1 := h2'
        rw [hq, F_one]
        omega
    omega
  · have hq2 : q = 2 := by omega
    subst hq2
    norm_num [F]

/-- `F` is monotone on positive integers. -/
lemma F_mono {x y : ℕ} (hx : 1 ≤ x) (hxy : x ≤ y) : F x ≤ F y := by
  rcases Nat.eq_or_lt_of_le hxy with heq | hlt
  · subst heq; omega
  · have : ∀ z : ℕ, 1 ≤ x → x ≤ z → F x ≤ F z := by
      intro z
      induction z with
      | zero => intro hx' hxz; omega
      | succ n ih =>
        intro hx' hxn
        by_cases hxe : x = n + 1
        · subst hxe; omega
        · have hlt' : x ≤ n := by omega
          have ih1 : F x ≤ F n := ih hx' hlt'
          by_cases hn2 : 2 ≤ n + 1
          · have hstep : F n ≤ F (n + 1) := by
              have hlt := F_lt_succ (by omega : 2 ≤ n + 1)
              have hrew : n = (n + 1) - 1 := by omega
              rw [← hrew] at hlt
              omega
            omega
          · omega
    exact this y hx hxy

/-- Lemma 3.1 (second half): `F a + F b ≤ F (a+b)` for `a, b ≥ 1`. -/
lemma F_add_le (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) : F a + F b ≤ F (a + b) := by
  by_cases hab2 : a + b = 2
  · have ha1 : a = 1 := by omega
    have hb1 : b = 1 := by omega
    subst ha1; subst hb1
    norm_num [F]
  · have hab3 : 3 ≤ a + b := by omega
    have ha' : a ≤ a + b - 1 := by omega
    have hb' : b ≤ a + b - 1 := by omega
    have hFa : F a ≤ F (a + b - 1) := F_mono ha ha'
    have hFb : F b ≤ F (a + b - 1) := F_mono hb hb'
    have hsum : F a + F b ≤ 2 * F (a + b - 1) := by omega
    have hm : a + b = (a + b - 1) + 1 := by omega
    have h2m : 2 ≤ a + b - 1 := by omega
    have h2 : 2 * F (a + b - 1) ≤ F ((a + b - 1) + 1) := two_mul_F_le_succ _ h2m
    rw [← hm] at h2
    omega

/-- Finite nonempty sums of local-factor bounds are bounded by the bound at
the sum of the dimensions. -/
theorem sum_F_le_F_sum {ι : Type*} (S : Finset ι) (d : ι → ℕ)
    (hS : S.Nonempty) (hd : ∀ i ∈ S, 1 ≤ d i) :
    (∑ i ∈ S, F (d i)) ≤ F (∑ i ∈ S, d i) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact False.elim (Finset.not_nonempty_empty hS)
  | @insert i S hi ih =>
    by_cases hn : S.Nonempty
    · rw [sum_insert hi, sum_insert hi]
      have hsum : 1 ≤ ∑ j ∈ S, d j := by
        obtain ⟨j, hj⟩ := hn
        exact (hd j (mem_insert_of_mem hj)).trans (single_le_sum (fun _ _ => Nat.zero_le _) hj)
      exact (Nat.add_le_add_left (ih hn (fun j hj => hd j (mem_insert_of_mem hj))) _).trans
        (F_add_le (d i) (∑ j ∈ S, d j) (hd i (mem_insert_self _ _)) hsum)
    · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      simp [he]

end UniformBorderRank
