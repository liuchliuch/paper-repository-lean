import MEJF.GraphBound
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! Exact oriented-graph demand feasibility by Hall matching to incident pairs. -/
namespace MEJF.HeterogeneousGraph
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- All available unordered edges, each a genuine two-element vertex set. -/
def allEdges : Finset (Finset α) := (univ : Finset α).powersetCard 2

/-- Edges touching at least one vertex of `A`. -/
def incident (A : Finset α) : Finset (Finset α) :=
  allEdges \ Aᶜ.powersetCard 2

lemma mem_incident {A e : Finset α} :
    e ∈ incident A ↔ e.card = 2 ∧ ∃ i ∈ A, i ∈ e := by
  classical
  constructor
  · intro he
    have hc : e.card = 2 := (mem_powersetCard.mp (mem_sdiff.mp he).1).2
    refine ⟨hc, ?_⟩
    by_contra hn
    apply (mem_sdiff.mp he).2
    apply mem_powersetCard.mpr
    refine ⟨?_, hc⟩
    intro i hie
    apply mem_compl.mpr
    intro hiA
    exact hn ⟨i, hiA, hie⟩
  · rintro ⟨hc, i, hiA, hie⟩
    apply mem_sdiff.mpr
    refine ⟨mem_powersetCard.mpr ⟨subset_univ _, hc⟩, ?_⟩
    intro hcomp
    exact (mem_compl.mp ((mem_powersetCard.mp hcomp).1 hie)) hiA

lemma mem_incident_singleton {i : α} {e : Finset α} :
    e ∈ incident ({i} : Finset α) ↔ e.card = 2 ∧ i ∈ e := by
  simp only [mem_incident, mem_singleton, exists_eq_left]

lemma incident_mono {A B : Finset α} (h : A ⊆ B) : incident A ⊆ incident B := by
  intro e he
  obtain ⟨hc, i, hiA, hie⟩ := mem_incident.mp he
  exact mem_incident.mpr ⟨hc, i, h hiA, hie⟩

lemma two_choose_two (n : ℕ) : 2 * n.choose 2 + n = n*n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.choose_succ_succ]
    simp only [Nat.choose_one_right]
    nlinarith

/-- Exactly `choose |A| 2 + |A|*(N-|A|)` available edges touch `A`. -/
theorem card_incident (A : Finset α) :
    (incident A).card = A.card.choose 2 + A.card * (Fintype.card α-A.card) := by
  have hsub : Aᶜ.powersetCard 2 ⊆ (allEdges : Finset (Finset α)) :=
    powersetCard_mono (subset_univ _)
  have hc := card_sdiff_add_card_eq_card hsub
  simp only [incident, allEdges, card_powersetCard, card_univ, card_compl] at hc ⊢
  have hN : A.card + (Fintype.card α-A.card) = Fintype.card α :=
    Nat.add_sub_of_le (card_le_univ A)
  have ha := two_choose_two A.card
  have hb := two_choose_two (Fintype.card α-A.card)
  have ht := two_choose_two (Fintype.card α)
  nlinarith

/-- Hall's condition on arbitrary demand slots reduces to the source's vertex
subset inequalities, because every slot of a vertex has the same neighbors. -/
theorem exists_incident_matching (w : α → ℕ)
    (hcut : ∀ A : Finset α, ∑ i ∈ A, w i ≤
      A.card.choose 2 + A.card*(Fintype.card α-A.card)) :
    ∃ f : (Σ i : α, Fin (w i)) → Finset α,
      Function.Injective f ∧ ∀ x, f x ∈ incident ({x.1} : Finset α) := by
  classical
  let neighbors : (Σ i : α, Fin (w i)) → Finset (Finset α) :=
    fun x => incident {x.1}
  apply (Finset.all_card_le_biUnion_card_iff_existsInjective' neighbors).mp
  intro T
  let A : Finset α := T.image Sigma.fst
  have hslots : T.card ≤ ∑ i ∈ A, w i := by
    let f : T → (Σ i : A, Fin (w i.val)) := fun x =>
      ⟨⟨x.val.1, mem_image.mpr ⟨x.val, x.property, rfl⟩⟩, x.val.2⟩
    let forget : (Σ i : A, Fin (w i.val)) → (Σ i : α, Fin (w i)) :=
      fun x => ⟨x.1.val, x.2⟩
    have hf : Function.Injective f := by
      intro x y hxy
      exact Subtype.ext (congrArg forget hxy)
    have hh := Fintype.card_le_of_injective f hf
    simpa [Fintype.card_sigma, Finset.sum_attach] using hh
  have hunion : T.biUnion neighbors = incident A := by
    ext e
    simp only [mem_biUnion, neighbors]
    constructor
    · rintro ⟨x, hx, he⟩
      obtain ⟨hc, hxe⟩ := mem_incident_singleton.mp he
      exact mem_incident.mpr ⟨hc, x.1, mem_image.mpr ⟨x, hx, rfl⟩, hxe⟩
    · intro he
      obtain ⟨hc, i, hi, hie⟩ := mem_incident.mp he
      obtain ⟨x, hx, hxi⟩ := mem_image.mp hi
      exact ⟨x, hx, mem_incident_singleton.mpr ⟨hc, by simpa [hxi] using hie⟩⟩
  rw [hunion, card_incident]
  exact hslots.trans (hcut A)

/-- Every matched incident pair has exactly one other endpoint. -/
lemma matched_pair_other {i : α} {e : Finset α}
    (he : e ∈ incident ({i} : Finset α)) :
    ∃ j, i ≠ j ∧ e = {i,j} := by
  obtain ⟨hc, hi⟩ := mem_incident_singleton.mp he
  have herase : (e.erase i).card = 1 := by
    rw [card_erase_of_mem hi]
    omega
  obtain ⟨j, hj⟩ := card_eq_one.mp herase
  have hji : j ≠ i := by
    have hm : j ∈ e.erase i := by rw [hj]; simp
    exact (mem_erase.mp hm).1
  exact ⟨j, hji.symm, by rw [← insert_erase hi, hj]⟩

/-- A genuine finite asymmetric relation realizes exactly all prescribed
outdegrees whenever the complete family of incident-edge cut inequalities holds. -/
theorem exists_oriented_of_cuts (w : α → ℕ)
    (hcut : ∀ A : Finset α, ∑ i ∈ A, w i ≤
      A.card.choose 2 + A.card*(Fintype.card α-A.card)) :
    ∃ R : α → α → Prop, (∀ i j, R i j → ¬ R j i) ∧
      ∀ i, GraphBound.outDegree R i = w i := by
  classical
  obtain ⟨f, hfinj, hf⟩ := exists_incident_matching w hcut
  have hother : ∀ x : (Σ i : α, Fin (w i)), ∃ j, x.1 ≠ j ∧ f x = {x.1,j} :=
    fun x => matched_pair_other (hf x)
  choose target hne hedge using hother
  let R : α → α → Prop := fun i j => ∃ k : Fin (w i), target ⟨i,k⟩ = j
  letI : DecidableRel R := fun i j => Classical.propDecidable (R i j)
  have hR : ∀ i j, R i j → ¬ R j i := by
    rintro i j ⟨ki, hki⟩ ⟨kj, hkj⟩
    have heq : f ⟨i,ki⟩ = f ⟨j,kj⟩ := by
      rw [hedge, hedge, hki, hkj, pair_comm]
    have hij : i = j := congrArg Sigma.fst (hfinj heq)
    exact hne ⟨i,ki⟩ (hki.trans hij.symm).symm
  refine ⟨R, hR, ?_⟩
  intro i
  letI : DecidablePred (R i) := fun j => Classical.propDecidable (R i j)
  have htinj : Function.Injective (fun k : Fin (w i) => target ⟨i,k⟩) := by
    intro a b hab
    have hfab : f ⟨i,a⟩ = f ⟨i,b⟩ := by
      rw [hedge, hedge]
      change ({i, target ⟨i,a⟩} : Finset α) = {i, target ⟨i,b⟩}
      exact congrArg (fun j => ({i,j} : Finset α)) hab
    have hs := hfinj hfab
    cases hs
    rfl
  unfold GraphBound.outDegree
  calc
    _ = (univ : Finset (Fin (w i))).card := by
      symm
      apply Finset.card_bij (fun k _ => target ⟨i,k⟩)
      · intro k hk
        exact mem_filter.mpr ⟨mem_univ _, ⟨k,rfl⟩⟩
      · intro k hk l hl hkl
        exact htinj hkl
      · intro j hj
        obtain ⟨k, hk⟩ := (mem_filter.mp hj).2
        exact ⟨k, mem_univ _, hk⟩
    _ = w i := by simp

/-- The source cut inequalities are necessary for every actual finite oriented
relation, with no tournament completeness assumption. -/
theorem cuts_of_oriented (R : α → α → Prop) (hR : ∀ i j, R i j → ¬ R j i)
    (w : α → ℕ) (hdeg : ∀ i, GraphBound.outDegree R i = w i) (A : Finset α) :
    (∑ i ∈ A, w i) ≤ A.card.choose 2 + A.card*(Fintype.card α-A.card) := by
  classical
  have hb := GraphBound.demand_cut_bound R hR A w (fun i _ => (hdeg i).ge)
  have hb' : 2*(∑ i ∈ A, w i) + A.card^2 + A.card ≤
      2*A.card*Fintype.card α := by exact_mod_cast hb
  have hc : A.card + (Fintype.card α-A.card) = Fintype.card α :=
    Nat.add_sub_of_le (card_le_univ A)
  have hchoose := two_choose_two A.card
  nlinarith

/-- Exact finite oriented-graph demand feasibility, the Hall component of
Theorem 6.1. All cardinal and degree counts refer to actual finite sets/relations. -/
theorem oriented_degree_iff_cuts (w : α → ℕ) :
    (∃ R : α → α → Prop, (∀ i j, R i j → ¬ R j i) ∧
      ∀ i, GraphBound.outDegree R i = w i) ↔
    ∀ A : Finset α, ∑ i ∈ A, w i ≤
      A.card.choose 2 + A.card*(Fintype.card α-A.card) := by
  constructor
  · rintro ⟨R, hR, hdeg⟩ A
    exact cuts_of_oriented R hR w hdeg A
  · exact exists_oriented_of_cuts w

/-- Demands on a designated set, and no outgoing arcs required elsewhere. -/
def supportedDemand (S : Finset α) (w : α → ℕ) (i : α) : ℕ :=
  if i ∈ S then w i else 0

/-- Subset cut inequalities are also necessary when demands are merely lower
bounds on the actual degrees, as in the failure set in Theorem 6.1. -/
theorem demand_cut_of_oriented (R : α → α → Prop) (hR : ∀ i j, R i j → ¬ R j i)
    (w : α → ℕ) (A : Finset α)
    (hdeg : ∀ i ∈ A, w i ≤ GraphBound.outDegree R i) :
    (∑ i ∈ A, w i) ≤ A.card.choose 2 + A.card*(Fintype.card α-A.card) := by
  classical
  have hb := GraphBound.demand_cut_bound R hR A w hdeg
  have hb' : 2*(∑ i ∈ A, w i) + A.card^2 + A.card ≤
      2*A.card*Fintype.card α := by exact_mod_cast hb
  have hc : A.card + (Fintype.card α-A.card) = Fintype.card α :=
    Nat.add_sub_of_le (card_le_univ A)
  have hchoose := two_choose_two A.card
  nlinarith

/-- Source-set form of the exact Hall realization: only subsets of `S` need be
checked, and the constructed relation has zero outdegree outside `S`. -/
theorem exists_oriented_on_of_cuts (S : Finset α) (w : α → ℕ)
    (hcut : ∀ A ⊆ S, ∑ i ∈ A, w i ≤
      A.card.choose 2 + A.card*(Fintype.card α-A.card)) :
    ∃ R : α → α → Prop, (∀ i j, R i j → ¬ R j i) ∧
      (∀ i ∈ S, GraphBound.outDegree R i = w i) ∧
      (∀ i ∉ S, GraphBound.outDegree R i = 0) := by
  classical
  have hc : ∀ A : Finset α, ∑ i ∈ A, supportedDemand S w i ≤
      A.card.choose 2 + A.card*(Fintype.card α-A.card) := by
    intro A
    let B : Finset α := A.filter (fun i => i ∈ S)
    have hBS : B ⊆ S := by
      intro i hi
      exact (mem_filter.mp hi).2
    have hBA : B ⊆ A := filter_subset _ _
    calc
      _ = ∑ i ∈ B, w i := by
        dsimp [B, supportedDemand]
        rw [sum_filter]
      _ ≤ B.card.choose 2 + B.card*(Fintype.card α-B.card) := hcut B hBS
      _ = (incident B).card := (card_incident B).symm
      _ ≤ (incident A).card := card_le_card (incident_mono hBA)
      _ = _ := card_incident A
  obtain ⟨R, hR, hdeg⟩ := exists_oriented_of_cuts (supportedDemand S w) hc
  refine ⟨R, hR, ?_, ?_⟩
  · intro i hi
    simpa only [supportedDemand, if_pos hi] using hdeg i
  · intro i hi
    simpa only [supportedDemand, if_neg hi] using hdeg i

/-- The exact source Hall-type demand criterion, with equality of the requested
outdegrees on `S` and no outgoing arcs at all outside `S`. -/
theorem oriented_degree_on_iff_cuts (S : Finset α) (w : α → ℕ) :
    (∃ R : α → α → Prop, (∀ i j, R i j → ¬ R j i) ∧
      (∀ i ∈ S, GraphBound.outDegree R i = w i) ∧
      (∀ i ∉ S, GraphBound.outDegree R i = 0)) ↔
    ∀ A ⊆ S, ∑ i ∈ A, w i ≤
      A.card.choose 2 + A.card*(Fintype.card α-A.card) := by
  constructor
  · rintro ⟨R,hR,hdeg,hzero⟩ A hAS
    exact demand_cut_of_oriented R hR w A (fun i hi => (hdeg i (hAS hi)).ge)
  · exact exists_oriented_on_of_cuts S w

end
end MEJF.HeterogeneousGraph
