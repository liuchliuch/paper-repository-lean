import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Abstract counting lemmas used in the paper

These are the purely combinatorial engines of Sections 2–4:

* double counting of incidences (Remark 5);
* the Gaussian binomial `q`-analogue of `binom(4,2)` (Lemma 7).
-/

open Finset

namespace K44K35Free

variable {ι X : Type*}

/-- **Double counting of incidences.**
If every point of `X` lies in exactly `r` members of the family `E`, and every
member of `E` meets `X` in at most `k` points, then `|X| * r ≤ k * |E|`. -/
theorem incidence_double_count [Fintype X] [DecidableEq X] [Fintype ι]
    (Xs : Finset X) (E : ι → Finset X) (r k : ℕ)
    (hr : ∀ x ∈ Xs, (univ.filter fun i => x ∈ E i).card = r)
    (hk : ∀ i, (E i ∩ Xs).card ≤ k) :
    Xs.card * r ≤ k * (univ : Finset ι).card := by
  classical
  have h1 : (∑ x ∈ Xs, (univ.filter fun i : ι => x ∈ E i).card)
      = Xs.card * r :=
    sum_const_nat (fun x hx => hr x hx)
  have hI : (∑ x ∈ Xs, (univ.filter fun i : ι => x ∈ E i).card)
      = ∑ i : ι, (E i ∩ Xs).card := by
    calc ∑ x ∈ Xs, (univ.filter fun i : ι => x ∈ E i).card
        = ∑ x ∈ Xs, ∑ i : ι, if x ∈ E i then (1 : ℕ) else 0 := by
          refine sum_congr rfl fun x _ => ?_
          rw [card_eq_sum_ones, sum_filter]
      _ = ∑ i : ι, ∑ x ∈ Xs, if x ∈ E i then (1 : ℕ) else 0 := by
          rw [Finset.sum_comm]
      _ = ∑ i : ι, (E i ∩ Xs).card := by
          refine sum_congr rfl fun i _ => ?_
          have hb : (∑ x ∈ Xs, if x ∈ E i then (1 : ℕ) else 0)
              = (Xs.filter (fun x => x ∈ E i)).card := sum_boole _ _
          have hfi : Xs.filter (fun x => x ∈ E i) = E i ∩ Xs := by
            ext x
            simp only [mem_filter, mem_inter]
            tauto
          rw [hb, hfi]
  have h3 : ∑ i : ι, (E i ∩ Xs).card ≤ ∑ _i : ι, (k : ℕ) :=
    sum_le_sum fun i _ => hk i
  have h4 : (∑ _i : ι, (k : ℕ)) = k * (univ : Finset ι).card := by
    rw [sum_const]
    simp [nsmul_eq_mul, Nat.mul_comm]
  omega

/-- Gaussian binomial coefficient `q`-analogue `[4 choose 2]_q`, the number of
`2`-dimensional subspaces of `F_q^4` (Lemma 7).  Closed form
`(q²+1)(q²+q+1) = q⁴+q³+2q²+q+1`. -/
def gaussianBinom2 (q : ℕ) : ℕ :=
  (q ^ 2 + 1) * (q ^ 2 + q + 1)

/-- Closed form of `M_q = [4 choose 2]_q`. -/
theorem gaussianBinom2_eq (q : ℕ) :
    gaussianBinom2 q = q ^ 4 + q ^ 3 + 2 * q ^ 2 + q + 1 := by
  unfold gaussianBinom2
  ring_nf

/-- Lemma 7: `M_q = O(q⁴)`.  For `q ≥ 2`, `M_q ≤ 6 q⁴`. -/
lemma gaussianBinom2_le (q : ℕ) (hq : 2 ≤ q) : gaussianBinom2 q ≤ 6 * q ^ 4 := by
  rw [gaussianBinom2_eq]
  have h1 : 1 ≤ q := by omega
  have p4 : q ^ 4 ≤ q ^ 4 := le_refl _
  have p3 : q ^ 3 ≤ q ^ 4 := by
    have h : (3:ℕ) ≤ 4 := by norm_num
    exact Nat.pow_le_pow_right h1 h
  have p2 : 2 * q ^ 2 ≤ 2 * q ^ 4 := by
    have h : (2:ℕ) ≤ 4 := by norm_num
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right h1 h)
  have p1 : q ≤ q ^ 4 := by
    have h : (1:ℕ) ≤ 4 := by norm_num
    simpa [pow_one] using Nat.pow_le_pow_right h1 h
  have p0 : 1 ≤ q ^ 4 := by
    have h : (0:ℕ) ≤ 4 := by norm_num
    simpa [pow_zero] using Nat.pow_le_pow_right h1 h
  omega

/-- **Remark 5 (abstract form).**
If `X` meets every member of a family of `m` sets in at most `k` points, and
every point of `X` lies in exactly `r` of those sets, then `|X| * r ≤ k * m`. -/
theorem remark5_obstruction [Fintype X] [DecidableEq X] [Fintype ι]
    (Xs : Finset X) (E : ι → Finset X) (r k m : ℕ)
    (hr : ∀ x ∈ Xs, (univ.filter fun i => x ∈ E i).card = r)
    (hk : ∀ i, (E i ∩ Xs).card ≤ k)
    (hm : (univ : Finset ι).card = m) :
    Xs.card * r ≤ k * m := by
  have h := incidence_double_count Xs E r k hr hk
  rw [hm] at h
  exact h

end K44K35Free
