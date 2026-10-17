import MEJF.Setup
import MEJF.Incidence
import MEJF.HeterogeneousGraph
import MEJF.HeterogeneousFrontier
import Mathlib.MeasureTheory.Constructions.Pi

/-! Genuine variable-positive-length block objects and finite-rank endpoint rule
from §6.1. Sizes remain part of each exchangeable block. -/
namespace MEJF.HeterogeneousSetup
open Finset MeasureTheory OrderStatistics
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The variable-size block space (6.1), with the countable disjoint-union
measurable structure supplied by its Sigma type. -/
abbrev Block (X : Type*) := Σ n : ℕ+, Fin n.val → X × ℝ

def size {X : Type*} (z : Block X) : ℕ := z.1.val

/-- One measurable symmetric learner acting on multisets of complete variable
blocks. Indexed arities witness exactly the paper's joint measurability. -/
structure Learner (X : Type*) [MeasurableSpace X] where
  predict : Multiset (Block X) → X → ℝ
  measurable_predict : ∀ r : ℕ,
    Measurable (fun q : (Fin r → Block X) × X =>
      predict ((List.ofFn q.1 : List (Block X)) : Multiset (Block X)) q.2)

def pairPrediction {X : Type*} [MeasurableSpace X] {N : ℕ}
    (A : Learner X) (Z : Fin N → Block X) (i k : Fin N) (x : X) : ℝ :=
  A.predict (((univ.erase i).erase k).val.map Z) x

lemma pairPrediction_symm {X : Type*} [MeasurableSpace X] {N : ℕ}
    (A : Learner X) (Z : Fin N → Block X) (i k : Fin N) (x : X) :
    pairPrediction A Z i k x = pairPrediction A Z k i x := by
  unfold pairPrediction
  rw [Finset.erase_right_comm]

/-- The unordered realized size multiset (6.2), retaining every occurrence. -/
def sizeMultiset {X : Type*} {N : ℕ} (Z : Fin N → Block X) : Multiset ℕ :=
  (univ.val.map fun i => size (Z i))

/-- Label-dependent inner ranks are exact floors, as in (6.3). -/
def innerRank {X : Type*} {N : ℕ} (a : ℝ) (Z : Fin N → Block X) (i : Fin N) : ℕ :=
  ⌊a*(size (Z i)+1)⌋₊

def failureRank {X : Type*} {N : ℕ} (alpha : ℝ) (Z : Fin N → Block X) (i : Fin N) : ℕ :=
  ⌊alpha*size (Z i)⌋₊+1

variable {m : ℕ}

/-- Actual arrays, with one different coordinate type at every label. -/
abbrev Responses (n : Fin (m+1) → ℕ) := (i : Fin (m+1)) → Fin (n i) → ℝ
abbrev Predictions (n : Fin (m+1) → ℕ) :=
  (i k : Fin (m+1)) → Fin (n i) → ℝ

def score (n : Fin (m+1) → ℕ) (y : Responses n) (p : Predictions n)
    (t : Fin (m+1) → ℕ) (ht : ∀ i, 1 ≤ t i ∧ t i ≤ n i) (i k : Fin (m+1)) : ℝ :=
  stat (fun j => |y i j-p i k j|) (Setup.innerIndex (n i) (t i) (ht i))

def lower (n : Fin (m+1) → ℕ) (y : Responses n) (p : Predictions n)
    (t : Fin (m+1) → ℕ) (ht : ∀ i, 1 ≤ t i ∧ t i ≤ n i)
    (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) (i : Fin (m+1)) (j : Fin (n i)) : ℝ :=
  stat (fun k : Fin m => p i (i.succAbove k) j-score n y p t ht (i.succAbove k) i)
    (Setup.lowerIndex m ell he)

def upper (n : Fin (m+1) → ℕ) (y : Responses n) (p : Predictions n)
    (t : Fin (m+1) → ℕ) (ht : ∀ i, 1 ≤ t i ∧ t i ≤ n i)
    (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) (i : Fin (m+1)) (j : Fin (n i)) : ℝ :=
  stat (fun k : Fin m => p i (i.succAbove k) j+score n y p t ht (i.succAbove k) i)
    (Setup.upperIndex m ell he)

def covered (n : Fin (m+1) → ℕ) (y : Responses n) (p : Predictions n)
    (t : Fin (m+1) → ℕ) (ht : ∀ i, 1 ≤ t i ∧ t i ≤ n i)
    (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) (i : Fin (m+1)) (j : Fin (n i)) : Prop :=
  lower n y p t ht ell he i j ≤ y i j ∧ y i j ≤ upper n y p t ht ell he i j

def failure (n : Fin (m+1) → ℕ) (y : Responses n) (p : Predictions n)
    (F t : Fin (m+1) → ℕ) (ht : ∀ i, 1 ≤ t i ∧ t i ≤ n i)
    (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) (i : Fin (m+1)) : Prop :=
  F i ≤ (univ.filter fun j => ¬ covered n y p t ht ell he i j).card

/-- The label-specific demand (6.8), in its exactly equivalent floor form. -/
def demand (F t : Fin (m+1) → ℕ) (ell : ℕ) (i : Fin (m+1)) : ℕ :=
  if F i < t i then 0 else Incidence.threshold (F i) m (m+1-ell) (t i)

def comparison (n : Fin (m+1) → ℕ) (y : Responses n) (p : Predictions n)
    (t : Fin (m+1) → ℕ) (ht : ∀ i, 1 ≤ t i ∧ t i ≤ n i)
    (i k : Fin (m+1)) : Prop := score n y p t ht k i < score n y p t ht i k

lemma comparison_asymm (n : Fin (m+1) → ℕ) (y : Responses n) (p : Predictions n)
    (t : Fin (m+1) → ℕ) (ht : ∀ i, 1 ≤ t i ∧ t i ≤ n i) :
    ∀ i k, comparison n y p t ht i k → ¬ comparison n y p t ht k i := by
  intro i k hik hki
  exact (not_lt_of_gt hik) hki


lemma enumerated_degree (n : Fin (m+1) → ℕ) (y : Responses n) (p : Predictions n)
    (t : Fin (m+1) → ℕ) (ht : ∀ i, 1 ≤ t i ∧ t i ≤ n i) (i : Fin (m+1)) :
    (univ.filter fun k : Fin m => comparison n y p t ht i (i.succAbove k)).card =
      GraphBound.outDegree (comparison n y p t ht) i := by
  classical
  unfold GraphBound.outDegree
  apply Finset.card_bij (fun k _ => i.succAbove k)
  · intro k hk
    simpa only [mem_filter,mem_univ,true_and] using hk
  · intro k hk l hl hkl
    exact Fin.succAbove_right_injective hkl
  · intro k hk
    have hki : k ≠ i := by
      intro h; subst k
      exact lt_irrefl _ ((mem_filter.mp hk).2)
    obtain ⟨j,rfl⟩ := Fin.exists_succAbove_eq hki
    exact ⟨j,by simpa only [mem_filter,mem_univ,true_and] using hk,rfl⟩

/-- The outer endpoint argument does not depend on equal coordinate lengths. -/
lemma coordinate_miss_count (n : Fin (m+1) → ℕ) (y : Responses n) (p : Predictions n)
    (t : Fin (m+1) → ℕ) (ht : ∀ i, 1 ≤ t i ∧ t i ≤ n i)
    (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) (i : Fin (m+1)) (j : Fin (n i))
    (hmiss : ¬ covered n y p t ht ell he i j) :
    m+1-ell ≤ (univ.filter fun k : Fin m =>
      score n y p t ht (i.succAbove k) i < |y i j-p i (i.succAbove k) j|).card := by
  have h := aggregate_miss_count
    (fun k : Fin m => p i (i.succAbove k) j-score n y p t ht (i.succAbove k) i)
    (fun k : Fin m => p i (i.succAbove k) j+score n y p t ht (i.succAbove k) i)
    (Setup.lowerIndex m ell he) (Setup.upperIndex m ell he) (by
      simp only [Setup.lowerIndex,Setup.upperIndex]
      omega) (y i j) hmiss
  simp only [Setup.upperIndex,count] at h
  simpa only [candidate_miss_iff,show m-ell+1=m+1-ell by omega] using h

/-- Every heterogeneous block failure forces its own actual degree demand.
This is proved from actual sorted residuals, without a failure-to-degree premise. -/
theorem failure_forces_demand (n : Fin (m+1) → ℕ) (y : Responses n) (p : Predictions n)
    (F t : Fin (m+1) → ℕ) (ht : ∀ i, 1 ≤ t i ∧ t i ≤ n i)
    (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) (i : Fin (m+1))
    (hfail : failure n y p F t ht ell he i) :
    demand F t ell i ≤ GraphBound.outDegree (comparison n y p t ht) i := by
  classical
  by_cases hFt : F i < t i
  · simp only [demand,if_pos hFt]
    exact Nat.zero_le _
  · rw [demand,if_neg hFt]
    have htF : t i ≤ F i := by omega
    obtain ⟨J,hJ,hJF⟩ := Finset.exists_subset_card_eq hfail
    let B : J → Fin m → Prop := fun j k =>
      score n y p t ht (i.succAbove k) i < |y i j.val-p i (i.succAbove k) j.val|
    let out : Finset (Fin m) := univ.filter fun k => comparison n y p t ht i (i.succAbove k)
    have hrow : ∀ j : J, m+1-ell ≤ Incidence.rowSum B j := by
      intro j
      have hj := (mem_filter.mp (hJ j.property)).2
      simpa only [Incidence.rowSum,B,sum_boole] using
        coordinate_miss_count n y p t ht ell he i j.val hj
    have hforce : ∀ k, t i ≤ Incidence.colSum B k → k ∈ out := by
      intro k hk
      have hcount : Incidence.colSum B k ≤
          count (fun j : Fin (n i) => |y i j-p i (i.succAbove k) j|)
            (score n y p t ht (i.succAbove k) i < ·) := by
        have hinj : Function.Injective (fun j : {j : J // B j k} =>
            (⟨j.val.val,j.property⟩ : {j : Fin (n i) //
              score n y p t ht (i.succAbove k) i < |y i j-p i (i.succAbove k) j|})) := by
          intro a b hab
          have hab' : a.val.val = b.val.val := congrArg
            (fun x : {j : Fin (n i) // score n y p t ht (i.succAbove k) i <
              |y i j-p i (i.succAbove k) j|} => x.val) hab
          exact Subtype.ext (Subtype.ext hab')
        have hh := Fintype.card_le_of_injective _ hinj
        simpa only [Fintype.card_subtype,Incidence.colSum,sum_boole,count] using hh
      have hlt := residual_rank_gt
        (fun j : Fin (n i) => |y i j-p i (i.succAbove k) j|)
        (t i) (ht i).1 (ht i).2 (score n y p t ht (i.succAbove k) i) (hk.trans hcount)
      exact mem_filter.mpr ⟨mem_univ _,hlt⟩
    have hcap := Incidence.incidence_capacity B out (m+1-ell) (t i) hrow hforce
    have hcardJ : Fintype.card J = F i := by simpa using hJF
    have hout : out.card = GraphBound.outDegree (comparison n y p t ht) i :=
      enumerated_degree n y p t ht i
    simp only [hcardJ,Fintype.card_fin,hout] at hcap
    exact Incidence.degree_threshold_of_capacity (F i) m (m+1-ell) (t i) _
      (ht i).1 htF (by omega) (by
        rw [← hout]
        simpa only [Fintype.card_fin] using Finset.card_le_univ out) hcap

/-- Evaluate the original learner and the original complete blocks at all
observed coordinates. No change of sample space or artificial failure event. -/
def learnerResponses {X : Type*} (Z : Fin (m+1) → Block X) :
    Responses (fun i => size (Z i)) := fun i j => (Z i).2 j |>.2

def learnerPredictions {X : Type*} [MeasurableSpace X]
    (A : Learner X) (Z : Fin (m+1) → Block X) :
    Predictions (fun i => size (Z i)) :=
  fun i k j => pairPrediction A Z i k ((Z i).2 j).1

def learnerFailure {X : Type*} [MeasurableSpace X]
    (A : Learner X) (Z : Fin (m+1) → Block X) (F t : Fin (m+1) → ℕ)
    (ht : ∀ i, 1 ≤ t i ∧ t i ≤ size (Z i)) (ell : ℕ)
    (he : 1 ≤ ell ∧ ell ≤ m) (i : Fin (m+1)) : Prop :=
  failure (fun i => size (Z i)) (learnerResponses Z) (learnerPredictions A Z)
    F t ht ell he i

/-- The actual finite-size rule's pairwise radius (6.6). -/
def radius {X : Type*} [MeasurableSpace X]
    (A : Learner X) (Z : Fin (m+1) → Block X) (t : Fin (m+1) → ℕ)
    (ht : ∀ i, 1 ≤ t i ∧ t i ≤ size (Z i)) (i k : Fin (m+1)) : ℝ :=
  score (fun i => size (Z i)) (learnerResponses Z) (learnerPredictions A Z) t ht i k

def lowerEndpoint {X : Type*} [MeasurableSpace X]
    (A : Learner X) (Z : Fin (m+1) → Block X) (t : Fin (m+1) → ℕ)
    (ht : ∀ i, 1 ≤ t i ∧ t i ≤ size (Z i)) (ell : ℕ)
    (he : 1 ≤ ell ∧ ell ≤ m) (i : Fin (m+1)) (j : Fin (size (Z i))) : ℝ :=
  lower (fun i => size (Z i)) (learnerResponses Z) (learnerPredictions A Z) t ht ell he i j

def upperEndpoint {X : Type*} [MeasurableSpace X]
    (A : Learner X) (Z : Fin (m+1) → Block X) (t : Fin (m+1) → ℕ)
    (ht : ∀ i, 1 ≤ t i ∧ t i ≤ size (Z i)) (ell : ℕ)
    (he : 1 ≤ ell ∧ ell ≤ m) (i : Fin (m+1)) (j : Fin (size (Z i))) : ℝ :=
  upper (fun i => size (Z i)) (learnerResponses Z) (learnerPredictions A Z) t ht ell he i j

/-- Actual variable-size failures are bounded by the exact sorted graph frontier. -/
theorem failure_count_le_sStar (n : Fin (m+1) → ℕ) (y : Responses n) (p : Predictions n)
    (F t : Fin (m+1) → ℕ) (ht : ∀ i, 1 ≤ t i ∧ t i ≤ n i)
    (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) :
    (univ.filter fun i => failure n y p F t ht ell he i).card ≤
      HeterogeneousFrontier.sStar (demand F t ell) := by
  apply HeterogeneousFrontier.qualifying_card_le_sStar (demand F t ell)
    (comparison n y p t ht) (comparison_asymm n y p t ht)
  intro i hi
  exact failure_forces_demand n y p F t ht ell he i (mem_filter.mp hi).2

/-- The full pointwise upper bridge for the paper's original variable-length
measurable multiset learner and every realized array of complete blocks. -/
theorem learner_failure_count_le_sStar {X : Type*} [MeasurableSpace X]
    (A : Learner X) (Z : Fin (m+1) → Block X) (F t : Fin (m+1) → ℕ)
    (ht : ∀ i, 1 ≤ t i ∧ t i ≤ size (Z i)) (ell : ℕ)
    (he : 1 ≤ ell ∧ ell ≤ m) :
    (univ.filter fun i => learnerFailure A Z F t ht ell he i).card ≤
      HeterogeneousFrontier.sStar (demand F t ell) :=
  failure_count_le_sStar (fun i => size (Z i)) (learnerResponses Z)
    (learnerPredictions A Z) F t ht ell he

/-- The source block-failure fraction is precisely the source floor threshold,
using each block's own positive coordinate length. -/
theorem learnerFailure_iff_covered_fraction {X : Type*} [MeasurableSpace X]
    (A : Learner X) (Z : Fin (m+1) → Block X) (alpha : ℝ) (ha : 0 ≤ alpha)
    (t : Fin (m+1) → ℕ) (ht : ∀ i, 1 ≤ t i ∧ t i ≤ size (Z i))
    (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) (i : Fin (m+1)) :
    learnerFailure A Z (failureRank alpha Z) t ht ell he i ↔
      ((univ.filter fun j => ((Z i).2 j).2 ∈ Set.Icc
        (lowerEndpoint A Z t ht ell he i j) (upperEndpoint A Z t ht ell he i j)).card : ℝ) /
        size (Z i) < 1-alpha := by
  classical
  have hc := filter_card_add_filter_neg_card_eq_card
    (s := (univ : Finset (Fin (size (Z i)))))
    (p := fun j => covered (fun k => size (Z k)) (learnerResponses Z)
      (learnerPredictions A Z) t ht ell he i j)
  simp only [card_univ,Fintype.card_fin] at hc
  have hn : 0 < size (Z i) := (Z i).1.property
  have hn' : (0:ℝ) < size (Z i) := by exact_mod_cast hn
  have han : 0 ≤ alpha*size (Z i) := mul_nonneg ha hn'.le
  unfold learnerFailure failure failureRank
  rw [← Nat.lt_iff_add_one_le,Nat.floor_lt han,div_lt_iff₀ hn']
  have hcr : ((univ.filter fun j => covered (fun k => size (Z k)) (learnerResponses Z)
      (learnerPredictions A Z) t ht ell he i j).card : ℝ) +
    ((univ.filter fun j => ¬ covered (fun k => size (Z k)) (learnerResponses Z)
      (learnerPredictions A Z) t ht ell he i j).card : ℝ) = size (Z i) := by exact_mod_cast hc
  change (alpha*size (Z i) < _) ↔ _
  have hcov : (univ.filter fun j => ((Z i).2 j).2 ∈ Set.Icc
      (lowerEndpoint A Z t ht ell he i j) (upperEndpoint A Z t ht ell he i j)) =
      (univ.filter fun j => covered (fun k => size (Z k)) (learnerResponses Z)
        (learnerPredictions A Z) t ht ell he i j) := by
    ext j
    simp only [mem_filter,mem_univ,true_and,Set.mem_Icc]
    rfl
  rw [hcov]
  constructor <;> intro h <;> nlinarith

/-- The degree demand induced by a size, depending only on that size. -/
def sizeDemand (m : ℕ) (alpha a : ℝ) (ell r : ℕ) : ℕ :=
  if ⌊alpha*r⌋₊+1 < ⌊a*(r+1)⌋₊ then 0 else
    Incidence.threshold (⌊alpha*r⌋₊+1) m (m+1-ell) ⌊a*(r+1)⌋₊

/-- The source frontier for a realized size multiset. -/
def realizedFrontier {X : Type*} (alpha a : ℝ) (ell : ℕ)
    (Z : Fin (m+1) → Block X) : ℕ :=
  HeterogeneousFrontier.sStar (fun i => sizeDemand m alpha a ell (size (Z i)))

/-- The frontier is determined by the unordered size multiset, even when sizes
are randomly assigned to labels. -/
theorem realizedFrontier_eq_of_sizeMultiset_eq {X Y : Type*}
    (alpha a : ℝ) (ell : ℕ) (Z : Fin (m+1) → Block X) (W : Fin (m+1) → Block Y)
    (hsize : sizeMultiset Z = sizeMultiset W) :
    realizedFrontier alpha a ell Z = realizedFrontier alpha a ell W := by
  apply HeterogeneousFrontier.sStar_eq_of_multiset_eq
  have h := congrArg (Multiset.map (sizeDemand m alpha a ell)) hsize
  simpa only [sizeMultiset,Multiset.map_map,Function.comp_def] using h

/-- Source floor ranks plugged into the actual statistical pointwise bound. -/
theorem source_failure_count_le_frontier {X : Type*} [MeasurableSpace X]
    (A : Learner X) (Z : Fin (m+1) → Block X) (alpha a : ℝ) (ell : ℕ)
    (ht : ∀ i, 1 ≤ innerRank a Z i ∧ innerRank a Z i ≤ size (Z i))
    (he : 1 ≤ ell ∧ ell ≤ m) :
    (univ.filter fun i => learnerFailure A Z (failureRank alpha Z) (innerRank a Z) ht ell he i).card ≤
      realizedFrontier alpha a ell Z := by
  exact learner_failure_count_le_sStar A Z (failureRank alpha Z) (innerRank a Z) ht ell he

end
end MEJF.HeterogeneousSetup
