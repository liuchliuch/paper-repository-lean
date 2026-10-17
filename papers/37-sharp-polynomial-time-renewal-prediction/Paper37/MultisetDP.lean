import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Rat.Cast.Order
import Lean.Elab.Tactic.Omega
import Init.Data.Vector.OfFn
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum.Core

/-!
Appendix C: exact multiset aggregates. The count-vector sums below use the
factorial-quotient multinomial coefficient, rather than defining the aggregates
by the algorithm whose correctness is being proved.
-/
namespace Paper37.DP

open scoped Nat
open Finset

/-- The numerator of the completed-gap likelihood for one count vector. -/
def weight (a : ℕ → ℕ) (s : Finset ℕ) (b : ℕ → ℕ) : ℕ :=
  ∏ j ∈ s, (a j + b j) ^ (a j + b j)

/-- Sum of the lengths of the future completed gaps. -/
def lengthSum (s : Finset ℕ) (b : ℕ → ℕ) : ℕ := ∑ j ∈ s, j * b j

/-- Number of future gap copies that may occur first after age `A`. -/
def marked (s : Finset ℕ) (A : ℕ) (b : ℕ → ℕ) : ℕ :=
  ∑ j ∈ s, if A < j then b j else 0

/-- C.4, with an arbitrary finite set of available gap lengths. -/
noncomputable def G (a : ℕ → ℕ) (s : Finset ℕ) (k u : ℕ) : ℕ :=
  ∑ b ∈ s.piAntidiag k,
    if lengthSum s b = u then Nat.multinomial s b * weight a s b else 0

/-- C.5, with an arbitrary finite set of available gap lengths. -/
noncomputable def S (a : ℕ → ℕ) (s : Finset ℕ) (A k u : ℕ) : ℕ :=
  ∑ b ∈ s.piAntidiag k,
    if lengthSum s b = u then Nat.multinomial s b * weight a s b * marked s A b else 0

@[simp] theorem G_empty (a : ℕ → ℕ) (k u : ℕ) :
    G a ∅ k u = if k = 0 ∧ u = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst k; simp [G, weight, lengthSum, eq_comm]
  · simp [G, hk]

@[simp] theorem S_empty (a : ℕ → ℕ) (A k u : ℕ) : S a ∅ A k u = 0 := by
  simp [S, marked]

/-- `piAntidiag` count vectors vanish at a newly inserted gap length. -/
private theorem at_new_zero {s : Finset ℕ} {d k : ℕ} {b : ℕ → ℕ}
    (hd : d ∉ s) (hb : b ∈ s.piAntidiag k) : b d = 0 := by
  by_contra h; exact hd ((mem_piAntidiag.mp hb).2 d h)

private theorem add_new_eq {s : Finset ℕ} {d k c : ℕ} {b : ℕ → ℕ}
    (hd : d ∉ s) (hb : b ∈ s.piAntidiag k) :
    (b + fun j => if j = d then c else 0) d = c := by
  simp [Pi.add_apply, at_new_zero hd hb]

private theorem add_old_eq {s : Finset ℕ} {d c : ℕ} {b : ℕ → ℕ}
    (hd : d ∉ s) {j : ℕ} (hj : j ∈ s) :
    (b + fun j => if j = d then c else 0) j = b j := by
  have h : j ≠ d := ne_of_mem_of_not_mem hj hd
  simp [Pi.add_apply, h]

private theorem weight_add_new {a : ℕ → ℕ} {s : Finset ℕ} {d k c : ℕ}
    {b : ℕ → ℕ} (hd : d ∉ s) (hb : b ∈ s.piAntidiag k) :
    weight a (s.cons d hd) (b + fun j => if j = d then c else 0) =
      (a d + c) ^ (a d + c) * weight a s b := by
  simp only [weight, prod_cons, add_new_eq hd hb]
  congr 1
  exact prod_congr rfl fun j hj => by rw [add_old_eq hd hj]

private theorem length_add_new {s : Finset ℕ} {d k c : ℕ} {b : ℕ → ℕ}
    (hd : d ∉ s) (hb : b ∈ s.piAntidiag k) :
    lengthSum (s.cons d hd) (b + fun j => if j = d then c else 0) =
      d * c + lengthSum s b := by
  simp only [lengthSum, sum_cons, add_new_eq hd hb]
  congr 1
  exact sum_congr rfl fun j hj => by rw [add_old_eq hd hj]

private theorem marked_add_new {s : Finset ℕ} {A d k c : ℕ} {b : ℕ → ℕ}
    (hd : d ∉ s) (hb : b ∈ s.piAntidiag k) :
    marked (s.cons d hd) A (b + fun j => if j = d then c else 0) =
      (if A < d then c else 0) + marked s A b := by
  simp only [marked, sum_cons, add_new_eq hd hb]
  congr 1
  exact sum_congr rfl fun j hj => by rw [add_old_eq hd hj]

private theorem multinomial_add_new {s : Finset ℕ} {d k c : ℕ} {b : ℕ → ℕ}
    (hd : d ∉ s) (hb : b ∈ s.piAntidiag k) :
    Nat.multinomial (s.cons d hd) (b + fun j => if j = d then c else 0) =
      (c + k).choose c * Nat.multinomial s b := by
  rw [Nat.multinomial_cons, add_new_eq hd hb]
  have hs : ∑ j ∈ s, (b + fun j => if j = d then c else 0) j = k := by
    rw [← (mem_piAntidiag.mp hb).1]
    exact sum_congr rfl fun j hj => add_old_eq hd hj
  rw [hs]
  congr 1
  exact Nat.multinomial_congr fun j hj => add_old_eq hd hj

/-- A fresh dimension can be separated without assuming the recurrence. This is
C.6 indexed by the antidiagonal `b + c = k`; infeasible length states are zero. -/
theorem G_cons (a : ℕ → ℕ) (s : Finset ℕ) (d k u : ℕ) (hd : d ∉ s) :
    G a (s.cons d hd) k u =
      ∑ p ∈ antidiagonal k,
        if d * p.1 ≤ u then
          k.choose p.1 * (a d + p.1) ^ (a d + p.1) *
            G a s p.2 (u - d * p.1)
        else 0 := by
  classical
  unfold G
  rw [piAntidiag_cons, sum_disjiUnion]
  refine sum_congr rfl fun p hp => ?_
  rw [sum_map]
  have hp' := mem_antidiagonal.mp hp
  simp only [addRightEmbedding_apply]
  by_cases hdu : d * p.1 ≤ u
  · rw [if_pos hdu, mul_sum]
    refine sum_congr rfl fun b hb => ?_
    rw [length_add_new hd hb, multinomial_add_new hd hb, weight_add_new hd hb]
    have he : d * p.1 + lengthSum s b = u ↔ lengthSum s b = u - d * p.1 := by omega
    simp only [he, hp']
    split_ifs <;> ring
  · rw [if_neg hdu]
    refine sum_eq_zero fun b hb => ?_
    rw [length_add_new hd hb]
    have he : ¬d * p.1 + lengthSum s b = u := by omega
    rw [if_neg he]

/-- The marked dimension has its old marks plus `b` new marks iff `d > A`.
This proves C.7 from its independent multiset-sum specification. -/
theorem S_cons (a : ℕ → ℕ) (s : Finset ℕ) (A d k u : ℕ) (hd : d ∉ s) :
    S a (s.cons d hd) A k u =
      ∑ p ∈ antidiagonal k,
        if d * p.1 ≤ u then
          k.choose p.1 * (a d + p.1) ^ (a d + p.1) *
            (S a s A p.2 (u - d * p.1) +
              (if A < d then p.1 else 0) * G a s p.2 (u - d * p.1))
        else 0 := by
  classical
  unfold S G
  rw [piAntidiag_cons, sum_disjiUnion]
  refine sum_congr rfl fun p hp => ?_
  rw [sum_map]
  have hp' := mem_antidiagonal.mp hp
  simp only [addRightEmbedding_apply]
  by_cases hdu : d * p.1 ≤ u
  · rw [if_pos hdu, mul_sum, ← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun b hb => ?_
    rw [length_add_new hd hb, multinomial_add_new hd hb, weight_add_new hd hb,
      marked_add_new hd hb]
    have he : d * p.1 + lengthSum s b = u ↔ lengthSum s b = u - d * p.1 := by omega
    simp only [he, hp']
    split_ifs <;> ring
  · rw [if_neg hdu]
    refine sum_eq_zero fun b hb => ?_
    rw [length_add_new hd hb]
    have he : ¬d * p.1 + lengthSum s b = u := by omega
    rw [if_neg he]

end Paper37.DP

namespace Paper37.DP

open scoped Nat
open Finset

/-- Number of distinct orderings of a multiset whose first letter is `e`.
The branch at count zero rules out choosing an absent gap type. -/
def firstOrders (s : Finset ℕ) (b : ℕ → ℕ) (e : ℕ) : ℕ :=
  if b e = 0 then 0 else
    (s.sum b - 1).choose (b e - 1) * Nat.multinomial (s.erase e) b

/-- The marked-copy identity for a single coordinate of a multinomial.
It is the integer, cross-multiplied form of the ordering ratio in C.9. -/
theorem multinomial_mul_count (s : Finset ℕ) (b : ℕ → ℕ) (e : ℕ) (he : e ∈ s) :
    Nat.multinomial s b * b e = s.sum b * firstOrders s b e := by
  classical
  by_cases hzero : b e = 0
  · simp [hzero, firstOrders]
  · have hpos : 0 < b e := Nat.pos_of_ne_zero hzero
    have hs : s.sum b = b e + (s.erase e).sum b := by
      rw [← sum_insert (notMem_erase e s), insert_erase he]
    have hm : Nat.multinomial s b =
        (b e + (s.erase e).sum b).choose (b e) * Nat.multinomial (s.erase e) b := by
      exact (congrArg (fun t => Nat.multinomial t b) (insert_erase he)).symm.trans
        (Nat.multinomial_insert (notMem_erase e s) b)
    rw [hm, firstOrders, if_neg hzero, hs]
    have h1 : b e + (s.erase e).sum b = (b e - 1 + (s.erase e).sum b) + 1 := by omega
    have h2 : b e = (b e - 1) + 1 := by omega
    have h3 : b e + (s.erase e).sum b - 1 = b e - 1 + (s.erase e).sum b := by omega
    rw [h3]
    have hchoose : (b e + (s.erase e).sum b).choose (b e) * b e =
        (b e + (s.erase e).sum b) *
          (b e - 1 + (s.erase e).sum b).choose (b e - 1) := by
      have ht := (Nat.succ_mul_choose_eq (b e - 1 + (s.erase e).sum b) (b e - 1)).symm
      simp only [Nat.succ_eq_add_one] at ht
      rwa [← h1, ← h2] at ht
    calc
      _ = ((b e + (s.erase e).sum b).choose (b e) * b e) *
          Nat.multinomial (s.erase e) b := by ring
      _ = _ := by rw [hchoose]; ring

/-- Sum of first-admissible orderings for one future count vector. -/
def admissibleOrders (s : Finset ℕ) (A : ℕ) (b : ℕ → ℕ) : ℕ :=
  ∑ e ∈ s, if A < e then firstOrders s b e else 0

/-- C.9 without rational division: marked copies equal length times
admissible first orderings. -/
theorem marked_ordering_identity (s : Finset ℕ) (A : ℕ) (b : ℕ → ℕ) :
    Nat.multinomial s b * marked s A b = s.sum b * admissibleOrders s A b := by
  classical
  unfold marked admissibleOrders
  rw [mul_sum, mul_sum]
  refine sum_congr rfl fun e he => ?_
  by_cases h : A < e
  · simp only [if_pos h]; exact multinomial_mul_count s b e he
  · simp [h]

/-- C.9 in its rational form. The left side is a sum of natural-number
ordering counts, so this also certifies integrality of the right side. -/
theorem admissibleOrders_eq_ratio (s : Finset ℕ) (A : ℕ) (b : ℕ → ℕ)
    (hk : s.sum b ≠ 0) :
    (admissibleOrders s A b : ℚ) =
      (marked s A b : ℚ) / ((s.sum b : ℕ) : ℚ) * (Nat.multinomial s b : ℚ) := by
  have h := marked_ordering_identity s A b
  have hk' : ((s.sum b : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hk
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hk').2
  calc
    (admissibleOrders s A b : ℚ) * ((s.sum b : ℕ) : ℚ) =
        ((s.sum b : ℕ) : ℚ) * (admissibleOrders s A b : ℚ) := by ring
    _ = (Nat.multinomial s b : ℚ) * (marked s A b : ℚ) := by exact_mod_cast h.symm
    _ = _ := by ring

/-- Independently enumerated weighted first-admissible orderings. -/
noncomputable def F (a : ℕ → ℕ) (s : Finset ℕ) (A k u : ℕ) : ℕ :=
  ∑ b ∈ s.piAntidiag k,
    if lengthSum s b = u then admissibleOrders s A b * weight a s b else 0

/-- Aggregate C.9: the marked numerator is an exact multiple of `k`. -/
theorem S_eq_mul_F (a : ℕ → ℕ) (s : Finset ℕ) (A k u : ℕ) :
    S a s A k u = k * F a s A k u := by
  classical
  unfold S F
  rw [mul_sum]
  refine sum_congr rfl fun b hb => ?_
  split_ifs with h
  · have ho := marked_ordering_identity s A b
    rw [(mem_piAntidiag.mp hb).1] at ho
    calc
      _ = (Nat.multinomial s b * marked s A b) * weight a s b := by ring
      _ = _ := by rw [ho]; ring
  · simp

/-- The exact division required by the integer implementation of C.8. -/
theorem S_divisible (a : ℕ → ℕ) (s : Finset ℕ) (A k u : ℕ) :
    k ∣ S a s A k u := by
  rw [S_eq_mul_F]
  exact dvd_mul_right k _

/-- Integer division of `S` computes the first-admissible aggregate exactly. -/
theorem S_div_eq_F (a : ℕ → ℕ) (s : Finset ℕ) (A k u : ℕ) (hk : 0 < k) :
    S a s A k u / k = F a s A k u := by
  rw [S_eq_mul_F, Nat.mul_div_right _ hk]

end Paper37.DP

namespace Paper37.DP

open scoped Nat
open Finset

/-- The exact paper index set `[1,d]`. -/
def gapSet (d : ℕ) : Finset ℕ := Icc 1 d

noncomputable def Gd (a : ℕ → ℕ) (d k u : ℕ) : ℕ := G a (gapSet d) k u
noncomputable def Sd (a : ℕ → ℕ) (A d k u : ℕ) : ℕ := S a (gapSet d) A k u

@[simp] theorem gapSet_zero : gapSet 0 = ∅ := by simp [gapSet]

private theorem gapSet_succ (d : ℕ) :
    gapSet (d + 1) = (gapSet d).cons (d + 1) (by simp [gapSet]) := by
  ext j
  simp only [gapSet, mem_Icc, mem_cons]
  omega

@[simp] theorem Gd_zero (a : ℕ → ℕ) (k u : ℕ) :
    Gd a 0 k u = if k = 0 ∧ u = 0 then 1 else 0 := by simp [Gd]

@[simp] theorem Sd_zero (a : ℕ → ℕ) (A k u : ℕ) : Sd a A 0 k u = 0 := by
  simp [Sd]

/-- Convert the antidiagonal indexing to the finite bounded loop of C.6/C.7. -/
private theorem antidiagonal_bounded_sum (d k u : ℕ) (hd : 0 < d) (H : ℕ → ℕ → ℕ) :
    (∑ p ∈ antidiagonal k, if d * p.1 ≤ u then H p.1 p.2 else 0) =
      ∑ b ∈ range (min k (u / d) + 1), H b (k - b) := by
  classical
  rw [Nat.antidiagonal_eq_map, sum_map]
  simp only [Function.Embedding.coeFn_mk]
  let m := min k (u / d)
  have hm : m ≤ k := min_le_left _ _
  have hsub : range (m + 1) ⊆ range (k + 1) := by
    intro b hb
    simp only [mem_range] at hb ⊢
    omega
  have hre : (∑ b ∈ range (k + 1), if d * b ≤ u then H b (k - b) else 0) =
      ∑ b ∈ range (m + 1), if d * b ≤ u then H b (k - b) else 0 := by
    symm
    exact sum_subset hsub fun b hb hbm => by
      have hbk : b ≤ k := by simpa [Nat.lt_succ_iff] using hb
      have hbm' : ¬b ≤ min k (u / d) := by simpa [m, Nat.lt_succ_iff] using hbm
      have hndiv : ¬b ≤ u / d := by omega
      have hn : ¬d * b ≤ u := by
        intro h
        apply hndiv
        exact (Nat.le_div_iff_mul_le hd).2 (by simpa [mul_comm] using h)
      simp [hn]
  rw [hre]
  refine sum_congr rfl fun b hb => ?_
  have hbdiv : b ≤ u / d := (le_min_iff.mp (show b ≤ min k (u / d) by
    simpa [m, Nat.lt_succ_iff] using hb)).2
  have h : d * b ≤ u := by
    simpa [mul_comm] using (Nat.le_div_iff_mul_le hd).1 hbdiv
  simp [h]

/-- C.6 with exactly the stated finite loop bound. -/
theorem Gd_recurrence (a : ℕ → ℕ) (d k u : ℕ) :
    Gd a (d + 1) k u =
      ∑ b ∈ range (min k (u / (d + 1)) + 1),
        k.choose b * (a (d + 1) + b) ^ (a (d + 1) + b) *
          Gd a d (k - b) (u - (d + 1) * b) := by
  unfold Gd
  rw [gapSet_succ, G_cons]
  exact antidiagonal_bounded_sum (d + 1) k u (Nat.zero_lt_succ d)
    (fun b c => k.choose b * (a (d + 1) + b) ^ (a (d + 1) + b) *
      G a (gapSet d) c (u - (d + 1) * b))

/-- C.7 with exactly the stated finite loop bound. -/
theorem Sd_recurrence (a : ℕ → ℕ) (A d k u : ℕ) :
    Sd a A (d + 1) k u =
      ∑ b ∈ range (min k (u / (d + 1)) + 1),
        k.choose b * (a (d + 1) + b) ^ (a (d + 1) + b) *
          (Sd a A d (k - b) (u - (d + 1) * b) +
            (if A < d + 1 then b else 0) * Gd a d (k - b) (u - (d + 1) * b)) := by
  unfold Sd Gd
  rw [gapSet_succ, S_cons]
  exact antidiagonal_bounded_sum (d + 1) k u (Nat.zero_lt_succ d)
    (fun b c => k.choose b * (a (d + 1) + b) ^ (a (d + 1) + b) *
      (S a (gapSet d) A c (u - (d + 1) * b) +
        (if A < d + 1 then b else 0) * G a (gapSet d) c (u - (d + 1) * b)))

/-- Exact divisibility for the paper's states, including unreachable states. -/
theorem Sd_divisible (a : ℕ → ℕ) (A d k u : ℕ) : k ∣ Sd a A d k u :=
  S_divisible a (gapSet d) A k u

end Paper37.DP

namespace Paper37.DP

open scoped Nat
open Finset

/-- A materialized rolling layer; both axes include the states `0,…,N`. -/
abbrev Layer (N : ℕ) := Vector (Vector (ℕ × ℕ) (N + 1)) (N + 1)

private def subIndex {N : ℕ} (k : Fin (N + 1)) (b : ℕ) : Fin (N + 1) :=
  ⟨k.val - b, lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩

/-- One materialized recurrence layer. Each lookup refers to the preceding
layer; the construction does not recursively enumerate gap orderings. -/
def step (N : ℕ) (a : ℕ → ℕ) (A d : ℕ) (old : Layer N) : Layer N :=
  Vector.ofFn fun k => Vector.ofFn fun u =>
    (∑ b ∈ range (min k.val (u.val / (d + 1)) + 1),
      k.val.choose b * (a (d + 1) + b) ^ (a (d + 1) + b) *
        (old[(subIndex k b).val][(subIndex u ((d + 1) * b)).val]).1,
     ∑ b ∈ range (min k.val (u.val / (d + 1)) + 1),
      k.val.choose b * (a (d + 1) + b) ^ (a (d + 1) + b) *
        ((old[(subIndex k b).val][(subIndex u ((d + 1) * b)).val]).2 +
          (if A < d + 1 then b else 0) *
            (old[(subIndex k b).val][(subIndex u ((d + 1) * b)).val]).1))

/-- Executable integer DP with materialized layers. -/
def run (N : ℕ) (a : ℕ → ℕ) (A : ℕ) : ℕ → Layer N
  | 0 => Vector.ofFn fun k => Vector.ofFn fun u =>
      (if k.val = 0 ∧ u.val = 0 then 1 else 0, 0)
  | d + 1 => step N a A d (run N a A d)

/-- Every computed table entry equals the independent count-vector sum. -/
theorem run_correct (N : ℕ) (a : ℕ → ℕ) (A d : ℕ) (k u : Fin (N + 1)) :
    (run N a A d)[k.val][u.val] = (Gd a d k.val u.val, Sd a A d k.val u.val) := by
  induction d generalizing k u with
  | zero => simp [run]
  | succ d ih =>
    simp only [run, step, Vector.getElem_ofFn]
    apply Prod.ext
    · dsimp only
      rw [Gd_recurrence]
      refine sum_congr rfl fun b hb => ?_
      rw [ih (subIndex k b) (subIndex u ((d + 1) * b))]
      rfl
    · dsimp only
      rw [Sd_recurrence]
      refine sum_congr rfl fun b hb => ?_
      rw [ih (subIndex k b) (subIndex u ((d + 1) * b))]
      rfl

/-- Number of recurrence summands in the explicit layer schedule through `L`.
Both table coordinates range over the materialized `0,…,N` states. -/
def updateCount (N L : ℕ) : ℕ :=
  ∑ d ∈ range L, ∑ k ∈ range (N + 1), ∑ u ∈ range (N + 1),
    (min k (u / (d + 1)) + 1)

/-- The recurrence has at most `L (N+1)^3` summand updates. This is an exact
combinatorial loop-count bound, separate from a bit-operation cost model. -/
theorem updateCount_le (N L : ℕ) : updateCount N L ≤ L * (N + 1) ^ 3 := by
  unfold updateCount
  calc
    _ ≤ ∑ _d ∈ range L, ∑ _k ∈ range (N + 1), ∑ _u ∈ range (N + 1), (N + 1) := by
      apply sum_le_sum
      intro d hd
      apply sum_le_sum
      intro k hk
      apply sum_le_sum
      intro u hu
      have hk' : k < N + 1 := mem_range.mp hk
      have hm := min_le_left k (u / (d + 1))
      omega
    _ = _ := by simp [pow_succ, mul_assoc]

/-- The full dimension schedule `d≤N` has a quartic update bound. -/
theorem updateCount_quartic (N L : ℕ) (hL : L ≤ N) :
    updateCount N L ≤ (N + 1) ^ 4 := by
  calc
    _ ≤ L * (N + 1) ^ 3 := updateCount_le N L
    _ ≤ (N + 1) * (N + 1) ^ 3 := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring

end Paper37.DP

namespace Paper37.DP

open scoped Nat
open Finset

/-- The first-letter count is the factorial quotient in the left-hand side
of C.9. In particular no field division is needed to count orderings. -/
theorem firstOrders_factorial (s : Finset ℕ) (b : ℕ → ℕ) (e : ℕ)
    (he : e ∈ s) (hbe : 0 < b e) :
    firstOrders s b e = (s.sum b - 1)! /
      ((b e - 1)! * ∏ j ∈ s.erase e, (b j)!) := by
  classical
  have hs : s.sum b = b e + (s.erase e).sum b := by
    rw [← sum_insert (notMem_erase e s), insert_erase he]
  have hle : b e - 1 ≤ s.sum b - 1 := by omega
  have hsub : s.sum b - 1 - (b e - 1) = (s.erase e).sum b := by omega
  have hc : (s.sum b - 1).choose (b e - 1) * (b e - 1)! *
      ((s.erase e).sum b)! = (s.sum b - 1)! := by
    simpa only [hsub] using Nat.choose_mul_factorial_mul_factorial hle
  have hp := Nat.multinomial_spec (s.erase e) b
  have hzero : b e ≠ 0 := Nat.ne_of_gt hbe
  have hm : ((b e - 1)! * ∏ j ∈ s.erase e, (b j)!) * firstOrders s b e =
      (s.sum b - 1)! := by
    unfold firstOrders
    rw [if_neg hzero]
    calc
      _ = (s.sum b - 1).choose (b e - 1) * (b e - 1)! *
          ((∏ j ∈ s.erase e, (b j)!) * Nat.multinomial (s.erase e) b) := by ring
      _ = _ := by rw [hp]; exact hc
  exact (Nat.div_eq_of_eq_mul_right
    (Nat.mul_pos (Nat.factorial_pos _) (Nat.prod_factorial_pos _ _)) hm.symm).symm

end Paper37.DP

namespace Paper37.DP

open Finset

/-- All empirical-likelihood numerator factors are bounded together by the
power of the total sample size, as used in the bit-length argument. -/
theorem weight_le_pow (a : ℕ → ℕ) (s : Finset ℕ) (b : ℕ → ℕ) (N : ℕ)
    (hN : 0 < N) (hsize : ∑ j ∈ s, (a j + b j) ≤ N) :
    weight a s b ≤ N ^ N := by
  unfold weight
  calc
    _ ≤ ∏ j ∈ s, N ^ (a j + b j) := by
      apply prod_le_prod'
      intro j hj
      apply Nat.pow_le_pow_left
      exact (single_le_sum (fun i hi => Nat.zero_le (a i + b i)) hj).trans hsize
    _ = N ^ (∑ j ∈ s, (a j + b j)) := prod_pow_eq_pow_sum _ _ _
    _ ≤ _ := Nat.pow_le_pow_right hN hsize

/-- The multinomial coefficients count all tuples over the available alphabet. -/
theorem sum_multinomial (s : Finset ℕ) (k : ℕ) :
    ∑ b ∈ s.piAntidiag k, Nat.multinomial s b = s.card ^ k := by
  simpa using (Finset.sum_pow_eq_sum_piAntidiag s (fun _ => (1 : ℕ)) k).symm

/-- A bound that ignores the gap-sum constraint, sufficient for the same
`O(N log N)` integer bit lengths. -/
theorem G_le_alphabet_pow (a : ℕ → ℕ) (s : Finset ℕ) (k u N : ℕ)
    (hN : 0 < N) (hsize : s.sum a + k ≤ N) :
    G a s k u ≤ s.card ^ k * N ^ N := by
  classical
  unfold G
  calc
    _ ≤ ∑ b ∈ s.piAntidiag k, Nat.multinomial s b * N ^ N := by
      apply sum_le_sum
      intro b hb
      split_ifs
      · apply Nat.mul_le_mul_left
        apply weight_le_pow _ _ _ _ hN
        rw [sum_add_distrib, (mem_piAntidiag.mp hb).1]
        exact hsize
      · exact Nat.zero_le _
    _ = _ := by rw [← sum_mul, sum_multinomial]

/-- The mark never exceeds the number of future gap copies. -/
theorem marked_le_count (s : Finset ℕ) (A : ℕ) (b : ℕ → ℕ) :
    marked s A b ≤ s.sum b := by
  unfold marked
  apply sum_le_sum
  intro j hj
  split_ifs <;> omega

/-- The marked table adds at most one mark for each future gap copy. -/
theorem S_le_mul_G (a : ℕ → ℕ) (s : Finset ℕ) (A k u : ℕ) :
    S a s A k u ≤ k * G a s k u := by
  classical
  unfold S G
  rw [mul_sum]
  apply sum_le_sum
  intro b hb
  split_ifs
  · have hm : marked s A b ≤ k := by
      simpa only [(mem_piAntidiag.mp hb).1] using marked_le_count s A b
    calc
      _ ≤ Nat.multinomial s b * weight a s b * k := Nat.mul_le_mul_left _ hm
      _ = _ := by ring
  · simp

/-- Explicit polynomial bit-length envelope for `G` (a deliberately crude
bound of the same exponential order as C.3). -/
theorem G_le_square_power (a : ℕ → ℕ) (s : Finset ℕ) (k u N : ℕ)
    (hN : 0 < N) (hcard : s.card ≤ N) (hsize : s.sum a + k ≤ N) :
    G a s k u ≤ N ^ N * N ^ N := by
  have hk : k ≤ N := by omega
  calc
    _ ≤ s.card ^ k * N ^ N := G_le_alphabet_pow _ _ _ _ _ hN hsize
    _ ≤ N ^ N * N ^ N := Nat.mul_le_mul_right _
      ((Nat.pow_le_pow_left hcard k).trans (Nat.pow_le_pow_right hN hk))

end Paper37.DP

namespace Paper37.DP
open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def countExponent {k : ℕ} (f : Fin k → α) : α →₀ ℕ :=
  ∑ i, Finsupp.single (f i) 1

private noncomputable def exponent (c : α → ℕ) : α →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm c

private theorem exponent_injective : Function.Injective (exponent (α := α)) :=
  Finsupp.equivFunOnFinite.symm.injective

private theorem product_X (c : α → ℕ) :
    (∏ a, (MvPolynomial.X a : MvPolynomial α ℕ) ^ c a) =
      MvPolynomial.monomial (exponent c) 1 := by
  change (∏ a, (MvPolynomial.X a : MvPolynomial α ℕ) ^ exponent c a) = _
  rw [← MvPolynomial.prod_X_pow_eq_monomial]
  symm
  apply prod_subset (subset_univ _)
  intro a ha hnot
  rw [Finsupp.notMem_support_iff.mp hnot, pow_zero]

private theorem tuple_product_X {k : ℕ} (f : Fin k → α) :
    (∏ i, (MvPolynomial.X (f i) : MvPolynomial α ℕ)) =
      MvPolynomial.monomial (countExponent f) 1 := by
  simpa only [MvPolynomial.X, countExponent] using
    (MvPolynomial.monomial_sum_one univ (fun i => Finsupp.single (f i) 1)
      (R := ℕ)).symm

/-- Count ordered tuples with a prescribed histogram by extracting one
coefficient of the multinomial theorem. -/
theorem card_exponent_tuples (c : α → ℕ) :
    Fintype.card {f : Fin (∑ a, c a) → α // countExponent f = exponent c} =
      Nat.multinomial univ c := by
  classical
  let k := ∑ a, c a
  let P : MvPolynomial α ℕ := (∑ a, MvPolynomial.X a) ^ k
  have hmulti := Finset.sum_pow_eq_sum_piAntidiag univ
    (fun a : α => (MvPolynomial.X a : MvPolynomial α ℕ)) k
  have hc := congrArg (MvPolynomial.coeff (exponent c)) hmulti
  have hnat (n : ℕ) : (n : MvPolynomial α ℕ) = MvPolynomial.C n := by simp
  simp_rw [MvPolynomial.coeff_sum, product_X, hnat, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_monomial] at hc
  have heq (b : α → ℕ) : exponent b = exponent c ↔ b = c :=
    exponent_injective.eq_iff
  simp only [heq] at hc
  have hmem : c ∈ piAntidiag univ k := by simp [mem_piAntidiag, k]
  have hcoef : MvPolynomial.coeff (exponent c) P = Nat.multinomial univ c := by
    simpa [P, hmem] using hc
  have ht := Fintype.sum_pow (fun a : α => (MvPolynomial.X a : MvPolynomial α ℕ)) k
  have hct := congrArg (MvPolynomial.coeff (exponent c)) ht
  simp_rw [MvPolynomial.coeff_sum, tuple_product_X, MvPolynomial.coeff_monomial] at hct
  have hcard : Fintype.card {f : Fin k → α // countExponent f = exponent c} =
      ∑ f : Fin k → α, if countExponent f = exponent c then 1 else 0 := by
    rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [hcard]
  exact hct.symm.trans hcoef

/-- Applying the exponent vector recovers the literal list histogram. -/
theorem countExponent_apply {k : ℕ} (f : Fin k → α) (a : α) :
    countExponent f a = (List.ofFn f).count a := by
  induction k with
  | zero => simp [countExponent]
  | succ k ih =>
    simp only [countExponent, Fin.sum_univ_succ, Finsupp.add_apply]
    rw [List.ofFn_succ, List.count_cons]
    have ht := ih (fun i => f i.succ)
    change _ + countExponent (fun i => f i.succ) a = _
    rw [ht]
    by_cases h : f 0 = a
    · simp only [Finsupp.single_apply, beq_iff_eq, h, if_true, Nat.add_comm]
    · simp only [Finsupp.single_apply, beq_iff_eq, h, if_false, Nat.zero_add, Nat.add_zero]

/-- Exact multinomial cardinality for actual ordered tuples, stated with
literal `List.count` histograms. -/
theorem card_count_tuples (c : α → ℕ) :
    Fintype.card {f : Fin (∑ a, c a) → α // ∀ a, (List.ofFn f).count a = c a} =
      Nat.multinomial univ c := by
  classical
  have hp (f : Fin (∑ a, c a) → α) :
      countExponent f = exponent c ↔ ∀ a, (List.ofFn f).count a = c a := by
    constructor
    · intro h a
      have hh := congrArg (fun v => v a) h
      simpa only [countExponent_apply] using hh
    · intro h
      ext a
      simpa only [countExponent_apply] using h a
  have h := card_exponent_tuples c
  simpa only [hp] using h

abbrev TupleOrdering (c : α → ℕ) :=
  {f : Fin (∑ a, c a) → α // ∀ a, (List.ofFn f).count a = c a}

theorem count_comp_perm {k : ℕ} (f : Fin k → α) (σ : Equiv.Perm (Fin k)) (a : α) :
    (List.ofFn (fun i => f (σ i))).count a = (List.ofFn f).count a := by
  rw [← countExponent_apply, ← countExponent_apply]
  apply congrArg (fun v : α →₀ ℕ => v a)
  exact Fintype.sum_equiv σ _ _ (fun i => rfl)

/-- Position permutations preserve the literal histogram. -/
def permuteTuples (c : α → ℕ) (σ : Equiv.Perm (Fin (∑ a, c a))) :
    TupleOrdering c ≃ TupleOrdering c where
  toFun f := ⟨fun i => f.val (σ i), fun a => (count_comp_perm f.val σ a).trans (f.prop a)⟩
  invFun f := ⟨fun i => f.val (σ.symm i),
    fun a => (count_comp_perm f.val σ.symm a).trans (f.prop a)⟩
  left_inv f := by apply Subtype.ext; funext i; simp
  right_inv f := by apply Subtype.ext; funext i; simp

/-- All positions have the same number of histograms with an admissible
symbol. This is a finite bijection, including repeated gap symbols. -/
theorem gate_position_invariant (c : α → ℕ) (hk : 0 < ∑ a, c a)
    (p : α → Prop) [DecidablePred p] (i : Fin (∑ a, c a)) :
    (∑ f : TupleOrdering c, if p (f.val i) then 1 else 0) =
      ∑ f : TupleOrdering c, if p (f.val ⟨0, hk⟩) then 1 else 0 := by
  classical
  exact Fintype.sum_equiv (permuteTuples c (Equiv.swap ⟨0, hk⟩ i)) _ _
    (fun f => by simp [permuteTuples])

/-- Each tuple has precisely the prescribed total number of admissible copies. -/
theorem tuple_gate_count (c : α → ℕ) (f : TupleOrdering c)
    (p : α → Prop) [DecidablePred p] :
    (∑ i, if p (f.val i) then 1 else 0) = ∑ a, if p a then c a else 0 := by
  classical
  have hist (a : α) : (∑ i, if f.val i = a then 1 else 0) = c a := by
    have h := f.prop a
    rw [← countExponent_apply] at h
    simpa only [countExponent, Finsupp.finset_sum_apply, Finsupp.single_apply] using h
  calc
    _ = ∑ i, ∑ a, if f.val i = a then (if p a then 1 else 0) else 0 := by
      apply sum_congr rfl
      intro i hi
      simp
    _ = ∑ a, ∑ i, if f.val i = a then (if p a then 1 else 0) else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro a ha
      by_cases hp : p a
      · simp only [if_pos hp]; exact hist a
      · simp [hp]

/-- C.9 for actual ordered tuples: total marked copies are the number of
positions times the number of first-admissible orderings. -/
theorem actual_ordering_mark_identity (c : α → ℕ) (hk : 0 < ∑ a, c a)
    (p : α → Prop) [DecidablePred p] :
    Nat.multinomial univ c * (∑ a, if p a then c a else 0) =
      (∑ a, c a) * ∑ f : TupleOrdering c, if p (f.val ⟨0, hk⟩) then 1 else 0 := by
  classical
  calc
    _ = Fintype.card (TupleOrdering c) * (∑ a, if p a then c a else 0) := by
      rw [card_count_tuples]
    _ = ∑ _f : TupleOrdering c, (∑ a, if p a then c a else 0) := by simp
    _ = ∑ f : TupleOrdering c, ∑ i, if p (f.val i) then 1 else 0 := by
      apply sum_congr rfl
      intro f hf
      exact (tuple_gate_count c f p).symm
    _ = ∑ i, ∑ f : TupleOrdering c, if p (f.val i) then 1 else 0 := sum_comm
    _ = ∑ _i : Fin (∑ a, c a),
        ∑ f : TupleOrdering c, if p (f.val ⟨0, hk⟩) then 1 else 0 := by
      apply sum_congr rfl
      intro i hi
      exact gate_position_invariant c hk p i
    _ = _ := by simp

end Paper37.DP
