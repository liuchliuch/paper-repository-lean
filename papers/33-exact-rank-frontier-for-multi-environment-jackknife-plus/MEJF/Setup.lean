import MEJF.Exchangeability
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Fin.SuccPred
import MEJF.OrderStatistics

/-! Actual finite-rank statistical objects from §2 and §4.
These are definitions on the paper's sample space, rather than definitions of
`Gamma` by the proposed closed formula. The minimax identity is not postulated. -/
namespace MEJF.Setup
open MeasureTheory Finset
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev UniversalCovariate := Set.Icc (0 : ℝ) 1
abbrev Block (X : Type*) (n : ℕ) := Fin n → X × ℝ

/-- A learner on multisets of complete blocks; the indexed evaluation map is
jointly measurable at every arity. A multiset retains multiplicity. -/
structure Learner (X : Type*) [MeasurableSpace X] (n : ℕ) where
  predict : Multiset (Block X n) → X → ℝ
  measurable_predict : ∀ r : ℕ,
    Measurable (fun q : (Fin r → Block X n) × X =>
      predict ((List.ofFn q.1 : List (Block X n)) : Multiset (Block X n)) q.2)

/-- Delete the two indexed occurrences before evaluating the one shared fit. -/
def pairPrediction {X : Type*} [MeasurableSpace X] {N n : ℕ}
    (A : Learner X n) (Z : Fin N → Block X n) (i k : Fin N) (x : X) : ℝ :=
  A.predict (((univ.erase i).erase k).val.map Z) x

lemma pairPrediction_symm {X : Type*} [MeasurableSpace X] {N n : ℕ}
    (A : Learner X n) (Z : Fin N → Block X n) (i k : Fin N) (x : X) :
    pairPrediction A Z i k x = pairPrediction A Z k i x := by
  unfold pairPrediction
  rw [Finset.erase_right_comm]

/-- Inner residual rank as a zero-based index. -/
def innerIndex (n t : ℕ) (ht : 1 ≤ t ∧ t ≤ n) : Fin n :=
  ⟨n-t, by omega⟩

def lowerIndex (m ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) : Fin m :=
  ⟨ell-1, by omega⟩

def upperIndex (m ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) : Fin m :=
  ⟨m-ell, by omega⟩

/-- Pairwise score (4.1), retaining ties with multiplicity. -/
def radius {X : Type*} [MeasurableSpace X] {N n : ℕ}
    (A : Learner X n) (Z : Fin N → Block X n) (i k : Fin N)
    (t : ℕ) (ht : 1 ≤ t ∧ t ≤ n) : ℝ :=
  OrderStatistics.stat (fun j => |(Z i j).2 - pairPrediction A Z i k (Z i j).1|)
    (innerIndex n t ht)

/-- Hypothetical interval endpoints (4.2)–(4.3). `succAbove` enumerates exactly
all other labels, without selecting the test block itself. -/
def lowerEndpoint {X : Type*} [MeasurableSpace X] {m n : ℕ}
    (A : Learner X n) (Z : Fin (m+1) → Block X n) (i : Fin (m+1)) (j : Fin n)
    (t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) : ℝ :=
  OrderStatistics.stat (fun k : Fin m =>
    pairPrediction A Z i (i.succAbove k) (Z i j).1 - radius A Z (i.succAbove k) i t ht)
    (lowerIndex m ell he)

def upperEndpoint {X : Type*} [MeasurableSpace X] {m n : ℕ}
    (A : Learner X n) (Z : Fin (m+1) → Block X n) (i : Fin (m+1)) (j : Fin n)
    (t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) : ℝ :=
  OrderStatistics.stat (fun k : Fin m =>
    pairPrediction A Z i (i.succAbove k) (Z i j).1 + radius A Z (i.succAbove k) i t ht)
    (upperIndex m ell he)

/-- Equality at an endpoint counts as coverage, including crossed intervals. -/
def covered {X : Type*} [MeasurableSpace X] {m n : ℕ}
    (A : Learner X n) (Z : Fin (m+1) → Block X n) (i : Fin (m+1)) (j : Fin n)
    (t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) : Prop :=
  (Z i j).2 ∈ Set.Icc (lowerEndpoint A Z i j t ell ht he)
    (upperEndpoint A Z i j t ell ht he)

def failure {X : Type*} [MeasurableSpace X] {m n : ℕ}
    (A : Learner X n) (Z : Fin (m+1) → Block X n) (i : Fin (m+1))
    (F t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) : Prop :=
  F ≤ (univ.filter fun j => ¬ covered A Z i j t ell ht he).card

/-- The integer parameters are the exact floors from (2.7). -/
def failureRank (alpha : ℝ) (n : ℕ) : ℕ := ⌊alpha * n⌋₊ + 1
def innerRank (a : ℝ) (n : ℕ) : ℕ := ⌊a * (n+1)⌋₊
def outerRank (b : ℝ) (m : ℕ) : ℕ := ⌊b * (m+1)⌋₊

/-- The minimax problem (2.5) in the positive finite-rank regime, on the fixed
universal covariate space. It is a supremum over actual exchangeable measures
and measurable multiset learners, and is not defined by (3.2). -/
def finiteRankGamma (m n : ℕ) (alpha : ℝ) (t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) : ℝ :=
  sSup {r : ℝ | ∃ (A : Learner UniversalCovariate n)
    (μ : Measure (Fin (m+1) → Block UniversalCovariate n)),
    IsProbabilityMeasure μ ∧ Exchangeability.Exchangeable μ ∧
    r = μ.real {Z | failure A Z (Fin.last m) (failureRank alpha n) t ell ht he}}

lemma radius_nonneg {X : Type*} [MeasurableSpace X] {N n : ℕ}
    (A : Learner X n) (Z : Fin N → Block X n) (i k : Fin N)
    (t : ℕ) (ht : 1 ≤ t ∧ t ≤ n) : 0 ≤ radius A Z i k t ht := by
  unfold radius OrderStatistics.stat
  exact abs_nonneg _

/-- The strict fraction failure event (2.4) is exactly the floor threshold from
(2.7); endpoint equalities remain covered. -/
theorem failure_iff_covered_fraction {X : Type*} [MeasurableSpace X] {m n : ℕ}
    (A : Learner X n) (Z : Fin (m+1) → Block X n) (i : Fin (m+1))
    (alpha : ℝ) (ha : 0 ≤ alpha) (hn : 0 < n)
    (t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    failure A Z i (failureRank alpha n) t ell ht he ↔
    ((univ.filter fun j => covered A Z i j t ell ht he).card : ℝ) / n < 1-alpha := by
  classical
  have hc := Finset.filter_card_add_filter_neg_card_eq_card (s := (univ : Finset (Fin n)))
    (p := fun j => covered A Z i j t ell ht he)
  simp only [card_univ, Fintype.card_fin] at hc
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have han : 0 ≤ alpha * n := mul_nonneg ha hn'.le
  unfold failure failureRank
  rw [← Nat.lt_iff_add_one_le, Nat.floor_lt han, div_lt_iff₀ hn']
  have hcr : ((univ.filter fun j => covered A Z i j t ell ht he).card : ℝ) +
    ((univ.filter fun j => ¬ covered A Z i j t ell ht he).card : ℝ) = n := by
    exact_mod_cast hc
  constructor <;> intro h <;> nlinarith

end
end MEJF.Setup
