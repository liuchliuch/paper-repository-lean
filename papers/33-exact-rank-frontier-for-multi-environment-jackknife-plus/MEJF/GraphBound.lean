import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! Sharp high-outdegree upper bound for arbitrary finite oriented graphs. -/
namespace MEJF.GraphBound

open scoped BigOperators
open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (R : α → α → Prop) [DecidableRel R]

/-- Actual outdegree, counting edges to all vertices. -/
def outDegree (i : α) : ℕ := (univ.filter (R i)).card

/-- The actual vertices meeting a fixed degree demand. -/
def highVertices (w : ℕ) : Finset α := univ.filter (fun i => w ≤ outDegree R i)

/-- The integer-valued adjacency matrix. -/
def edge (i j : α) : ℤ := if R i j then 1 else 0

omit [DecidableEq α] in
lemma outDegree_eq_sum (i : α) : (outDegree R i : ℤ) = ∑ j, edge R i j := by
  simp [outDegree, edge]

omit [Fintype α] [DecidableEq α] in
lemma edge_le_one (i j : α) : edge R i j ≤ 1 := by
  unfold edge
  split <;> omega

omit [Fintype α] [DecidableEq α] in
lemma edge_nonneg (i j : α) : 0 ≤ edge R i j := by
  unfold edge
  split <;> omega

omit [Fintype α] in
lemma pair_bound (hR : ∀ i j, R i j → ¬ R j i) (i j : α) :
    edge R i j + edge R j i + (if i = j then 1 else 0 : ℤ) ≤ 1 := by
  by_cases hij : i = j
  · subst j
    have hii : ¬ R i i := fun h => hR i i h h
    simp [edge, hii]
  · by_cases hr : R i j
    · have hn := hR i j hr
      simp [edge, hr, hn, hij]
    · by_cases hs : R j i <;> simp [edge, hr, hs, hij]

/-- Twice the number of internal arcs is at most `g(g-1)`.
The diagonal term is kept on the left to avoid truncated subtraction. -/
theorem internal_edge_bound (hR : ∀ i j, R i j → ¬ R j i) (S : Finset α) :
    2 * (∑ i ∈ S, ∑ j ∈ S, edge R i j) + S.card ≤ (S.card : ℤ) ^ 2 := by
  have hb := Finset.sum_le_sum (fun i (_hi : i ∈ S) =>
    Finset.sum_le_sum (fun j (_hj : j ∈ S) => pair_bound R hR i j))
  have hswap : (∑ i ∈ S, ∑ j ∈ S, edge R j i) =
      ∑ i ∈ S, ∑ j ∈ S, edge R i j := Finset.sum_comm
  have hdiag : (∑ i ∈ S, ∑ j ∈ S, (if i = j then 1 else 0 : ℤ)) = S.card := by
    simp
  simp only [Finset.sum_add_distrib] at hb
  rw [hswap, hdiag] at hb
  simpa [pow_two, two_mul] using hb

/-- Outgoing arcs from `S` to its complement are bounded by the number of pairs. -/
theorem external_edge_bound (S : Finset α) :
    (∑ i ∈ S, ∑ j ∈ Sᶜ, edge R i j) ≤ (S.card : ℤ) * Sᶜ.card := by
  calc
    _ ≤ ∑ _i ∈ S, ∑ _j ∈ Sᶜ, (1 : ℤ) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => edge_le_one R i j))
    _ = _ := by simp

/-- The complete sum of actual outgoing degrees splits into internal and external arcs. -/
lemma sum_outDegree_split (S : Finset α) :
    (∑ i ∈ S, (outDegree R i : ℤ)) =
      (∑ i ∈ S, ∑ j ∈ S, edge R i j) +
        (∑ i ∈ S, ∑ j ∈ Sᶜ, edge R i j) := by
  simp only [outDegree_eq_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact (Finset.sum_add_sum_compl S (fun j => edge R i j)).symm

/-- Universal double count for every subset in a finite oriented graph. -/
theorem subset_degree_sum_bound (hR : ∀ i j, R i j → ¬ R j i) (S : Finset α) :
    2 * (∑ i ∈ S, (outDegree R i : ℤ)) + (S.card : ℤ)^2 + S.card ≤
      2 * S.card * Fintype.card α := by
  have hi := internal_edge_bound R hR S
  have he := external_edge_bound R S
  have hc : (S.card : ℤ) + Sᶜ.card = Fintype.card α := by
    exact_mod_cast Finset.card_add_card_compl S
  rw [sum_outDegree_split]
  nlinarith

/-- Any nonempty set of vertices all meeting demand `w` obeys the sharp bound. -/
theorem subset_card_bound (hR : ∀ i j, R i j → ¬ R j i) (S : Finset α)
    (hS : S.Nonempty) (w : ℕ) (hw : ∀ i ∈ S, w ≤ outDegree R i) :
    (S.card : ℤ) ≤ 2 * (Fintype.card α - (w : ℤ)) - 1 := by
  have hs : (0 : ℤ) < S.card := by exact_mod_cast S.card_pos.mpr hS
  have hl : (S.card : ℤ) * w ≤ ∑ i ∈ S, (outDegree R i : ℤ) := by
    calc
      _ = ∑ _i ∈ S, (w : ℤ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i hi => by exact_mod_cast hw i hi)
  have hb := subset_degree_sum_bound R hR S
  nlinarith

/-- Every subset of vertices satisfying possibly different demands obeys the
necessary oriented-edge cut inequality, in doubled form. -/
theorem demand_cut_bound (hR : ∀ i j, R i j → ¬ R j i) (S : Finset α)
    (demand : α → ℕ) (hd : ∀ i ∈ S, demand i ≤ outDegree R i) :
    2 * (∑ i ∈ S, (demand i : ℤ)) + (S.card : ℤ)^2 + S.card ≤
      2 * S.card * Fintype.card α := by
  have hl : (∑ i ∈ S, (demand i : ℤ)) ≤ ∑ i ∈ S, (outDegree R i : ℤ) :=
    Finset.sum_le_sum (fun i hi => by exact_mod_cast hd i hi)
  have hb := subset_degree_sum_bound R hR S
  linarith

/-- The sharp upper count applies directly to any designated set of vertices
whose actual outdegrees meet the demand. -/
theorem qualifying_subset_card_le (hR : ∀ i j, R i j → ¬ R j i) (S : Finset α)
    (w : ℕ) (hw : w < Fintype.card α) (hS : ∀ i ∈ S, w ≤ outDegree R i) :
    S.card ≤ min (Fintype.card α) (2 * (Fintype.card α - w) - 1) := by
  apply Nat.le_min.mpr
  constructor
  · exact Finset.card_le_univ _
  · by_cases hs : S.Nonempty
    · have h := subset_card_bound R hR S hs w hS
      omega
    · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      simp [he]

/-- Lemma 4.3: the number of vertices meeting a demand `w < N` is at most
`min N (2*(N-w)-1)`, for the actual outdegrees of any asymmetric finite relation. -/
theorem highVertices_card_le (hR : ∀ i j, R i j → ¬ R j i) (w : ℕ)
    (hw : w < Fintype.card α) :
    (highVertices R w).card ≤
      min (Fintype.card α) (2 * (Fintype.card α - w) - 1) := by
  apply qualifying_subset_card_le R hR (highVertices R w) w hw
  intro i hi
  exact (Finset.mem_filter.mp hi).2

end MEJF.GraphBound
