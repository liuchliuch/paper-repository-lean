import Mathlib.Tactic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Elementary counting identities used by Proposition 2.1
-/

open Finset BigOperators Nat

namespace SemidegreeExt

/-- `∑_{i < d} (d - i) = d(d+1)/2`, doubled form. -/
theorem sum_range_sub_self (d : ℕ) :
    (∑ i ∈ range d, (d - i)) * 2 = d * (d + 1) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    have h1 : ∑ i ∈ range (d + 1), (d + 1 - i)
        = (d + 1) + ∑ i ∈ range d, (d - i) := by
      have hsum : ∑ i ∈ range (d + 1), (d + 1 - i)
          = ∑ i ∈ range d, (d + 1 - (i + 1)) + (d + 1 - 0) :=
        sum_range_succ' (fun i => (d + 1 - i) : ℕ → ℕ) d
      rw [hsum, Nat.sub_zero, add_comm]
      have hmap : ∑ i ∈ range d, (d + 1 - (i + 1)) = ∑ i ∈ range d, (d - i) :=
        sum_congr rfl fun i _ => by omega
      rw [hmap]
    rw [h1, add_mul, ih]
    ring

/-- `∑_{i=0}^{n-1} (d-i) = d(d+1)/2` when `d ≤ n`, doubled form. -/
theorem sum_sub_eq (n d : ℕ) (hd : d ≤ n) :
    (∑ i ∈ range n, (d - i)) * 2 = d * (d + 1) := by
  have hsplit : ∑ i ∈ range n, (d - i) = ∑ i ∈ range d, (d - i) := by
    have hdecomp : range n = range d ∪ (Ico d n) := by
      ext i
      simp only [mem_union, mem_range, mem_Ico]
      omega
    rw [hdecomp, sum_union]
    · have hzero : ∑ i ∈ Ico d n, (d - i) = 0 :=
        sum_eq_zero fun i hi => by
          simp only [mem_Ico] at hi
          exact Nat.sub_eq_zero_of_le (by omega)
      rw [hzero, add_zero]
    · rw [disjoint_left]
      intro i hi hj
      simp only [mem_range, mem_Ico] at hi hj
      omega
  rw [hsplit, sum_range_sub_self]

/-- `∑_{i < n} min(c,i) = c*n - c(c+1)/2`, doubled form. -/
theorem sum_min_eq (n c : ℕ) (hc : c ≤ n) :
    (∑ i ∈ range n, min c i) * 2 + c * (c + 1) = 2 * c * n := by
  have hsplit2 :
      ∑ i ∈ range n, min c i = ∑ i ∈ range c, i + c * (n - c) := by
    have hdecomp : range n = range c ∪ (Ico c n) := by
      ext i
      simp only [mem_union, mem_range, mem_Ico]
      omega
    rw [hdecomp, sum_union]
    · have h1 : ∑ i ∈ range c, min c i = ∑ i ∈ range c, i :=
        sum_congr rfl fun i hi => by
          simp only [mem_range] at hi
          exact min_eq_right (Nat.le_of_lt hi)
      have h2 : ∑ i ∈ Ico c n, min c i = ∑ i ∈ Ico c n, c :=
        sum_congr rfl fun i hi => by
          simp only [mem_Ico] at hi
          exact min_eq_left (by omega)
      rw [h1, h2, sum_const, nsmul_eq_mul, Nat.card_Ico]
      simp only [Nat.cast_id]
      ring
    · rw [disjoint_left]
      intro i hi hj
      simp only [mem_range, mem_Ico] at hi hj
      omega
  rw [hsplit2, add_mul]
  have hsum : ∑ i ∈ range c, i = c * (c - 1) / 2 := sum_range_id _
  rw [hsum]
  have h2 : c * (c - 1) / 2 * 2 = c * (c - 1) := by
    refine Nat.div_mul_cancel ?_
    have heven : Even (c * (c - 1)) := by
      rcases Nat.even_or_odd c with he | ho
      · obtain ⟨k, hk⟩ := he
        refine ⟨k * (c - 1), ?_⟩
        rw [hk]
        ring
      · obtain ⟨k, hk⟩ := ho
        refine ⟨c * k, ?_⟩
        have hce : c - 1 = 2 * k := by omega
        rw [hce]
        ring
    exact Even.two_dvd heven
  rw [h2]
  have h3 : (c * (n - c)) * 2 = 2 * c * (n - c) := by ring
  rw [h3]
  rcases c with _ | c
  · rw [show 0 * (0 + 1) = 0 by ring, show 0 * n = 0 by ring, zero_add]
    ring
  · have h4 : (c + 1) * ((c + 1) - 1) = (c + 1) * c := by rw [Nat.add_sub_cancel]
    rw [h4]
    have h6 : (c + 1) * ((c + 1) + 1) = (c + 1) * c + 2 * (c + 1) := by ring
    rw [h6]
    have h7 :
        (c + 1) * c + 2 * (c + 1) * (n - (c + 1)) + ((c + 1) * c + 2 * (c + 1))
          = 2 * ((c + 1) * (c + (n - (c + 1)) + 1)) := by
      ring
    rw [h7]
    have h8 : c + (n - (c + 1)) + 1 = n := by omega
    rw [h8, mul_assoc]

end SemidegreeExt
