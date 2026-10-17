import MEJF.OrderStatistics
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases

/-!
# Tournament component of the randomized-rank extension

This file proves the finite tournament optimization in Proposition 6.4.
It does not identify the statistical minimax value with this optimization.
-/
namespace MEJF.Extensions

open Finset

/-- A tournament has exactly one directed edge between distinct vertices. -/
structure Tournament (N : ℕ) where
  wins : Fin N → Fin N → Bool
  noLoop : ∀ i, wins i i = false
  complete : ∀ i j, i ≠ j → (wins i j = true ↔ wins j i = false)

namespace Tournament

def edge (T : Tournament N) (i j : Fin N) : ℕ := if T.wins i j then 1 else 0

def degree (T : Tournament N) (i : Fin N) : ℕ := ∑ j, T.edge i j

lemma edge_le_one (T : Tournament N) (i j : Fin N) : T.edge i j ≤ 1 := by
  simp only [edge]
  split <;> omega

lemma edge_pair (T : Tournament N) (i j : Fin N) :
    T.edge i j + T.edge j i + (if i = j then 1 else 0) = 1 := by
  by_cases h : i = j
  · subst j
    simp [edge, T.noLoop]
  · have h' := T.complete i j h
    cases hi : T.wins i j <;> cases hj : T.wins j i <;> simp_all [edge]

/-- Internal tournament edges count each unordered pair exactly once. -/
lemma internal_sum (T : Tournament N) (S : Finset (Fin N)) :
    2 * (∑ i ∈ S, ∑ j ∈ S, T.edge i j) + S.card = S.card * S.card := by
  have hc : (∑ i ∈ S, ∑ j ∈ S,
      (T.edge i j + T.edge j i + if i = j then 1 else 0)) = S.card * S.card := by
    simp_rw [T.edge_pair]
    simp
  have hswap : (∑ i ∈ S, ∑ j ∈ S, T.edge j i) =
      ∑ i ∈ S, ∑ j ∈ S, T.edge i j := by
    rw [Finset.sum_comm]
  simp_rw [Finset.sum_add_distrib] at hc
  simp only [hswap] at hc
  have hdiag : (∑ i ∈ S, ∑ j ∈ S, if i = j then 1 else 0) = S.card := by
    simp
  rw [hdiag] at hc
  omega

/-- The sum of outdegrees on a selected vertex set includes at most all
edges from that set to its complement. This is the subset score inequality. -/
lemma subset_degree_bound (T : Tournament N) (S : Finset (Fin N)) :
    2 * (∑ i ∈ S, T.degree i) + S.card * S.card + S.card ≤ 2 * N * S.card := by
  let C := Finset.univ \ S
  have hc : C.card + S.card = N := by
    dsimp [C]
    simpa using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
  have hsplit : (∑ i ∈ S, T.degree i) =
      (∑ i ∈ S, ∑ j ∈ S, T.edge i j) + (∑ i ∈ S, ∑ j ∈ C, T.edge i j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [degree, C]
    have hh := Finset.sum_sdiff (f := fun j => T.edge i j) (Finset.subset_univ S)
    simpa only [add_comm] using hh.symm
  have hcross : (∑ i ∈ S, ∑ j ∈ C, T.edge i j) ≤ S.card * C.card := by
    calc
      _ ≤ ∑ _i ∈ S, ∑ _j ∈ C, 1 := by
        apply Finset.sum_le_sum
        intro i hi
        exact Finset.sum_le_sum (fun j hj => T.edge_le_one i j)
      _ = _ := by simp
  have hint := T.internal_sum S
  nlinarith

/-- The seven-vertex tournament objective for the uniform mixture of ranks
2 and 3 is bounded by six before division by two. -/
theorem seven_rank_count (T : Tournament 7) :
    (Finset.univ.filter fun i => 5 ≤ T.degree i).card +
      (Finset.univ.filter fun i => 4 ≤ T.degree i).card ≤ 6 := by
  let A := Finset.univ.filter fun i => 5 ≤ T.degree i
  let B := Finset.univ.filter fun i => 4 ≤ T.degree i
  have hAB : A ⊆ B := by
    intro i hi
    simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at *
    omega
  have hab := Finset.card_le_card hAB
  have hb : B.card ≤ 7 := by
    simpa using Finset.card_le_card (Finset.subset_univ B)
  have hlow : 4 * B.card + A.card ≤ ∑ i ∈ B, T.degree i := by
    have hpoint : ∀ i ∈ B, 4 + (if i ∈ A then 1 else 0) ≤ T.degree i := by
      intro i hi
      have hi' : 4 ≤ T.degree i := (Finset.mem_filter.mp hi).2
      by_cases ha : i ∈ A
      · have ha' : 5 ≤ T.degree i := (Finset.mem_filter.mp ha).2
        simp [ha, ha']
      · simp [ha, hi']
    have hs := Finset.sum_le_sum hpoint
    have hind : (∑ i ∈ B, if i ∈ A then 1 else 0) = A.card := by
      rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hAB]
      simp
    rw [Finset.sum_add_distrib, hind] at hs
    simpa [Nat.mul_comm] using hs
  have hu := T.subset_degree_bound B
  have hpoly : B.card * B.card + 2 * A.card ≤ 5 * B.card := by omega
  change A.card + B.card ≤ 6
  interval_cases h : B.card <;> omega

/-- A concrete tournament with score sequence (0,1,2,3,5,5,5).
The upper three vertices beat all lower four and form a directed 3-cycle. -/
def sevenWitness : Tournament 7 where
  wins i j := decide ((i.val < 4 ∧ j.val < i.val) ∨
    (4 ≤ i.val ∧ j.val < 4) ∨
    (i.val = 4 ∧ j.val = 5) ∨ (i.val = 5 ∧ j.val = 6) ∨
    (i.val = 6 ∧ j.val = 4))
  noLoop := by decide
  complete := by decide

theorem sevenWitness_degrees :
    (List.ofFn sevenWitness.degree) = [0, 1, 2, 3, 5, 5, 5] := by decide

theorem sevenWitness_attains :
    (Finset.univ.filter fun i => 5 ≤ sevenWitness.degree i).card +
      (Finset.univ.filter fun i => 4 ≤ sevenWitness.degree i).card = 6 := by decide

/-- Twice the weighted number of failures is the sum of these threshold
counts. The normalization by seven yields the source's value 3/7. -/
def rank23Payoff (T : Tournament 7) : ℚ :=
  ((Finset.univ.filter fun i => 5 ≤ T.degree i).card +
    (Finset.univ.filter fun i => 4 ≤ T.degree i).card : ℕ) / (14 : ℚ)

theorem rank23Payoff_le (T : Tournament 7) : T.rank23Payoff ≤ 3 / 7 := by
  have h := T.seven_rank_count
  dsimp [rank23Payoff]
  exact_mod_cast (show ((Finset.univ.filter fun i => 5 ≤ T.degree i).card +
      (Finset.univ.filter fun i => 4 ≤ T.degree i).card : ℚ) / 14 ≤ 3 / 7 by
    have h' : ((Finset.univ.filter fun i => 5 ≤ T.degree i).card +
      (Finset.univ.filter fun i => 4 ≤ T.degree i).card : ℚ) ≤ 6 := by exact_mod_cast h
    linarith)

theorem sevenWitness_payoff : sevenWitness.rank23Payoff = 3 / 7 := by
  unfold rank23Payoff
  rw [sevenWitness_attains]
  norm_num

/-- The tournament maximum is attained; no characterization of possible
score sequences is needed for this exact optimization. -/
theorem rank23Payoff_isGreatest :
    IsGreatest (Set.range rank23Payoff) (3 / 7 : ℚ) := by
  constructor
  · exact ⟨sevenWitness, sevenWitness_payoff⟩
  · rintro x ⟨T, rfl⟩
    exact rank23Payoff_le T

/-- The separate rank-two tournament objective has maximum 3/7. -/
theorem seven_ge5_count_le (T : Tournament 7) :
    (Finset.univ.filter fun i => 5 ≤ T.degree i).card ≤ 3 := by
  let S := Finset.univ.filter fun i => 5 ≤ T.degree i
  have hl : 5 * S.card ≤ ∑ i ∈ S, T.degree i := by
    calc
      _ = ∑ _i ∈ S, 5 := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun i hi => (Finset.mem_filter.mp hi).2)
  have hu := T.subset_degree_bound S
  change S.card ≤ 3
  nlinarith

/-- The separate rank-three tournament objective has maximum 5/7. -/
theorem seven_ge4_count_le (T : Tournament 7) :
    (Finset.univ.filter fun i => 4 ≤ T.degree i).card ≤ 5 := by
  let S := Finset.univ.filter fun i => 4 ≤ T.degree i
  have hl : 4 * S.card ≤ ∑ i ∈ S, T.degree i := by
    calc
      _ = ∑ _i ∈ S, 4 := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun i hi => (Finset.mem_filter.mp hi).2)
  have hu := T.subset_degree_bound S
  change S.card ≤ 5
  nlinarith

/-- Two transitive bottom vertices and a regular five-vertex tournament
above them give degree sequence (0,1,4,4,4,4,4). -/
def fiveWitness : Tournament 7 where
  wins i j := decide ((i.val < 2 ∧ j.val < i.val) ∨
    (2 ≤ i.val ∧ j.val < 2) ∨
    (2 ≤ i.val ∧ 2 ≤ j.val ∧
      ((j.val + 5 - i.val) % 5 = 1 ∨ (j.val + 5 - i.val) % 5 = 2)))
  noLoop := by decide
  complete := by decide

theorem fiveWitness_degrees :
    List.ofFn fiveWitness.degree = [0,1,4,4,4,4,4] := by decide

theorem deterministic_threshold_counts_attained :
    (Finset.univ.filter fun i => 5 ≤ sevenWitness.degree i).card = 3 ∧
    (Finset.univ.filter fun i => 4 ≤ fiveWitness.degree i).card = 5 := by decide

theorem randomized_strict_gain : (3 : ℚ) / 7 < (1 / 2) * (3 / 7 + 5 / 7) ∧
    (1 / 2 : ℚ) * (3 / 7 + 5 / 7) = 4 / 7 := by norm_num

end Tournament
namespace Stability

/-- Among `N` scalar reference radii, at most `N-d` labels can have at
least `d` strictly smaller reference radii. Equal values remain distinct
indexed occurrences, and strict comparisons handle ties conservatively. -/
theorem scalar_rank_count {I α : Type*} [Fintype I] [DecidableEq I]
    [LinearOrder α] (q : I → α) (d : ℕ) (hd : d ≤ Fintype.card I) :
    (Finset.univ.filter fun i => d ≤
      (Finset.univ.filter fun j => q j < q i).card).card + d ≤ Fintype.card I := by
  classical
  let S := Finset.univ.filter fun i => d ≤
    (Finset.univ.filter fun j => q j < q i).card
  change S.card + d ≤ Fintype.card I
  by_cases hs : S.Nonempty
  · obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image S q hs
    have hi' : d ≤ (Finset.univ.filter fun j => q j < q i).card :=
      (Finset.mem_filter.mp hi).2
    have hsub : (Finset.univ.filter fun j => q j < q i) ⊆ Finset.univ \ S := by
      intro j hj
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hjS
      exact not_lt_of_ge (hmin j hjS) (Finset.mem_filter.mp hj).2
    have hc := Finset.card_le_card hsub
    have hcompl : (Finset.univ \ S).card + S.card = Fintype.card I := by
      simpa using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
    omega
  · have hz : S.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hs)
    omega

/-- The exact scalar event in (6.35), using the paper's leave-one
ascending order statistic. The index `m-ell` is zero based, so its paper
rank is `N-ell`. No distinctness assumption on the radii is used. -/
theorem reference_rank_count (m : ℕ) (q : Fin (m+1) → ℝ)
    (ell : ℕ) (hell : 1 ≤ ell) (helm : ell ≤ m) :
    (Finset.univ.filter fun i =>
      OrderStatistics.stat (fun j => q (i.succAbove j))
        ⟨m-ell, by omega⟩ < q i).card ≤ ell := by
  classical
  let S := Finset.univ.filter fun i =>
    OrderStatistics.stat (fun j => q (i.succAbove j))
      ⟨m-ell, by omega⟩ < q i
  let B := Finset.univ.filter fun i => m+1-ell ≤
    (Finset.univ.filter fun j => q j < q i).card
  have hsub : S ⊆ B := by
    intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    have hlocal := OrderStatistics.count_lt_of_stat_lt
      (fun j => q (i.succAbove j)) ⟨m-ell, by omega⟩ (q i) hi'
    have hinj : OrderStatistics.count (fun j => q (i.succAbove j)) (· < q i) ≤
        (Finset.univ.filter fun j => q j < q i).card := by
      dsimp [OrderStatistics.count]
      apply Finset.card_le_card_of_injOn i.succAbove
      · intro j hj
        change j ∈ Finset.univ.filter (fun j => q (i.succAbove j) < q i) at hj
        change i.succAbove j ∈ Finset.univ.filter (fun j => q j < q i)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
      · intro j hj k hk heq
        exact Fin.succAbove_right_injective heq
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    dsimp at hlocal
    omega
  have hc := scalar_rank_count q (m+1-ell) (by simpa using Nat.sub_le (m+1) ell)
  have hmono := Finset.card_le_card hsub
  change S.card ≤ ell
  change B.card + (m+1-ell) ≤ Fintype.card (Fin (m+1)) at hc
  simp only [Fintype.card_fin] at hc
  omega

/-- The numerical endpoint estimate behind the `2ε` expansion: one ε
comes from the center and one from the residual radius. -/
theorem candidate_endpoint_bounds (p g r q ε : ℝ)
    (hp : |p-g| ≤ ε) (hr : |r-q| ≤ ε) :
    p-r-2*ε ≤ g-q ∧ g+q ≤ p+r+2*ε := by
  have hp' := abs_le.mp hp
  have hr' := abs_le.mp hr
  constructor <;> linarith

/-- The affine interpolation in (6.29), once the two exact pointwise
label counts and the probability of the stability event are available. -/
theorem bad_event_interpolation (N ell s p γ : ℝ)
    (hN : 0 < N) (hls : ell ≤ s) (hp : p ≤ γ) :
    (ell*(1-p)+s*p)/N ≤ ell/N + (s-ell)/N*γ := by
  have hm := mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr hls)
  calc
    (ell*(1-p)+s*p)/N = (ell+(s-ell)*p)/N := by congr 1; nlinarith
    _ ≤ (ell+(s-ell)*γ)/N := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hN)
      linarith
    _ = ell/N + (s-ell)/N*γ := by rw [add_div, mul_div_right_comm]

end Stability
end MEJF.Extensions
