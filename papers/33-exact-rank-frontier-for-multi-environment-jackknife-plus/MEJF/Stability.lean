import MEJF.Extensions
import MEJF.Setup
import MEJF.DeterministicUpper
import Mathlib.Data.Fin.Rev

/-! Deterministic on-sample deletion-stability bound for actual rank endpoints.
The proof passes through the scalar leave-one reference radii, with ties kept. -/
namespace MEJF.Stability
open Finset OrderStatistics
noncomputable section
attribute [local instance] Classical.propDecidable

variable {m n : ℕ}

/-- Zero-based indices corresponding to paper ranks `n+1-t`, `ell`, and `N-ell`. -/
def innerIndex (n t : ℕ) (ht : 1 ≤ t ∧ t ≤ n) : Fin n := ⟨n-t, by omega⟩
def lowerIndex (m ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) : Fin m := ⟨ell-1, by omega⟩
def upperIndex (m ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) : Fin m := ⟨m-ell, by omega⟩

abbrev Responses (m n : ℕ) := Fin (m+1) → Fin n → ℝ
abbrev Predictions (m n : ℕ) := Fin (m+1) → Fin (m+1) → Fin n → ℝ

def score (y : Responses m n) (p : Predictions m n)
    (i k : Fin (m+1)) (t : ℕ) (ht : 1 ≤ t ∧ t ≤ n) : ℝ :=
  stat (fun j => |y i j-p i k j|) (innerIndex n t ht)

def referenceRadius (y g : Responses m n) (i : Fin (m+1))
    (t : ℕ) (ht : 1 ≤ t ∧ t ≤ n) : ℝ :=
  stat (fun j => |y i j-g i j|) (innerIndex n t ht)

def lower (y : Responses m n) (p : Predictions m n) (i : Fin (m+1)) (j : Fin n)
    (t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) : ℝ :=
  stat (fun k : Fin m => p i (i.succAbove k) j-score y p (i.succAbove k) i t ht)
    (lowerIndex m ell he)

def upper (y : Responses m n) (p : Predictions m n) (i : Fin (m+1)) (j : Fin n)
    (t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) : ℝ :=
  stat (fun k : Fin m => p i (i.succAbove k) j+score y p (i.succAbove k) i t ht)
    (upperIndex m ell he)

def expandedCovered (y : Responses m n) (p : Predictions m n) (ε : ℝ)
    (i : Fin (m+1)) (j : Fin n) (t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) : Prop :=
  lower y p i j t ell ht he-2*ε ≤ y i j ∧
    y i j ≤ upper y p i j t ell ht he+2*ε

def expandedFailure (y : Responses m n) (p : Predictions m n) (ε : ℝ)
    (i : Fin (m+1)) (F t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) : Prop :=
  F ≤ (univ.filter fun j => ¬ expandedCovered y p ε i j t ell ht he).card

/-- Increasing and decreasing tuples have opposite rank indices under negation. -/
lemma stat_neg (u : Fin m → ℝ) (k : Fin m) :
    stat (fun j => -u j) k = -stat u k.rev := by
  have hmono : Monotone ((fun j => -u j) ∘ (Fin.revPerm.trans (Tuple.sort u))) := by
    intro a b hab
    change -stat u a.rev ≤ -stat u b.rev
    exact neg_le_neg (stat_monotone_rank u (Fin.rev_anti hab))
  have h := Tuple.unique_monotone (Tuple.monotone_sort (fun j => -u j)) hmono
  exact congrFun h k

lemma stat_const_sub (u : Fin m → ℝ) (k : Fin m) (g : ℝ) :
    stat (fun j => g-u j) k = g-stat u k.rev := by
  calc
    _ = stat (fun j => -u j+g) k := by congr 1; funext j; linarith
    _ = stat (fun j => -u j) k+g := stat_add_const _ _ _
    _ = _ := by rw [stat_neg]; linarith

lemma reverse_lower_index (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) :
    (lowerIndex m ell he).rev = upperIndex m ell he := by
  apply Fin.ext
  simp only [Fin.val_rev, lowerIndex, upperIndex]
  omega

lemma residual_close (y p g ε : ℝ) (hp : |p-g| ≤ ε) :
    abs (abs (y-p) - abs (y-g)) ≤ ε := by
  have h := abs_abs_sub_abs_le_abs_sub (y-p) (y-g)
  have heq : (y-p)-(y-g) = g-p := by linarith
  rw [heq, abs_sub_comm g p] at h
  exact h.trans hp

/-- Order statistics of residuals inherit the same ε bound as predictions. -/
lemma score_close (y g : Responses m n) (p : Predictions m n) (ε : ℝ)
    (hstable : ∀ i k, i ≠ k → ∀ j, |p i k j-g i j| ≤ ε)
    (i k : Fin (m+1)) (hik : i ≠ k)
    (t : ℕ) (ht : 1 ≤ t ∧ t ≤ n) :
    |score y p i k t ht-referenceRadius y g i t ht| ≤ ε := by
  apply stat_lipschitz
  intro j
  exact residual_close _ _ _ _ (hstable i k hik j)

/-- The expanded interval contains the common scalar reference interval
in source (6.34), for every coordinate of every hypothetical test label. -/
theorem reference_interval_contained (y g : Responses m n) (p : Predictions m n) (ε : ℝ)
    (hstable : ∀ i k, i ≠ k → ∀ j, |p i k j-g i j| ≤ ε)
    (i : Fin (m+1)) (j : Fin n) (t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    lower y p i j t ell ht he-2*ε ≤
      g i j-stat (fun k => referenceRadius y g (i.succAbove k) t ht)
        (upperIndex m ell he) ∧
    g i j+stat (fun k => referenceRadius y g (i.succAbove k) t ht)
        (upperIndex m ell he) ≤ upper y p i j t ell ht he+2*ε := by
  let q : Fin m → ℝ := fun k => referenceRadius y g (i.succAbove k) t ht
  have hl : lower y p i j t ell ht he ≤
      stat (fun k => g i j-q k+2*ε) (lowerIndex m ell he) := by
    apply stat_mono
    intro k
    have hpair := hstable i (i.succAbove k) (Fin.succAbove_ne _ _).symm j
    have hr := score_close y g p ε hstable (i.succAbove k) i
      (Fin.succAbove_ne _ _) t ht
    have hb := (Extensions.Stability.candidate_endpoint_bounds _ _ _ _ _ hpair hr).1
    dsimp [q]
    linarith
  have hu : stat (fun k => g i j+q k-2*ε) (upperIndex m ell he) ≤
      upper y p i j t ell ht he := by
    apply stat_mono
    intro k
    have hpair := hstable i (i.succAbove k) (Fin.succAbove_ne _ _).symm j
    have hr := score_close y g p ε hstable (i.succAbove k) i
      (Fin.succAbove_ne _ _) t ht
    have hb := (Extensions.Stability.candidate_endpoint_bounds _ _ _ _ _ hpair hr).2
    dsimp [q]
    linarith
  rw [stat_add_const, stat_const_sub, reverse_lower_index] at hl
  rw [stat_sub_const] at hu
  have heq : stat (fun k => g i j+q k) (upperIndex m ell he) =
      g i j+stat q (upperIndex m ell he) := by
    simpa [add_comm] using stat_add_const q (upperIndex m ell he) (g i j)
  rw [heq] at hu
  constructor <;> dsimp [q] at * <;> linarith

/-- Nonnegative expansion removes coordinate misses, hence also block
failures. This supplies the unrestricted count on the complement of the
stability event. -/
theorem expanded_failure_mono (y : Responses m n) (p : Predictions m n) (ε : ℝ)
    (hε : 0 ≤ ε) (i : Fin (m+1)) (F t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    expandedFailure y p ε i F t ell ht he →
      expandedFailure y p 0 i F t ell ht he := by
  intro hfail
  apply hfail.trans
  apply Finset.card_le_card
  intro j hj
  simp only [mem_filter, mem_univ, true_and] at *
  intro hc
  apply hj
  dsimp [expandedCovered] at *
  constructor <;> nlinarith [hc.1, hc.2]

/-- Missing the expanded rule on F coordinates forces the strict scalar
comparison (6.35); t≤F is the only inner-rank requirement here. -/
theorem failure_forces_reference_rank (y g : Responses m n) (p : Predictions m n) (ε : ℝ)
    (hstable : ∀ i k, i ≠ k → ∀ j, |p i k j-g i j| ≤ ε)
    (i : Fin (m+1)) (F t ell : ℕ) (htF : t ≤ F)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m)
    (hfail : expandedFailure y p ε i F t ell ht he) :
    stat (fun k => referenceRadius y g (i.succAbove k) t ht)
      (upperIndex m ell he) < referenceRadius y g i t ht := by
  let Q := stat (fun k => referenceRadius y g (i.succAbove k) t ht)
      (upperIndex m ell he)
  have hm : ∀ j, ¬ expandedCovered y p ε i j t ell ht he → Q < |y i j-g i j| := by
    intro j hj
    have hb := reference_interval_contained y g p ε hstable i j t ell ht he
    by_contra! hbad
    have habs := abs_le.mp hbad
    apply hj
    constructor <;> dsimp [expandedCovered] <;> dsimp [Q] at * <;> linarith
  have hcard : F ≤ count (fun j => |y i j-g i j|) (Q < ·) := by
    apply hfail.trans
    apply Finset.card_le_card
    intro j hj
    simp only [mem_filter, mem_univ, true_and] at *
    exact hm j hj
  exact residual_rank_gt _ t ht.1 ht.2 Q (htF.trans hcard)

/-- The full pointwise stability count in the positive finite-rank regime.
It is a theorem about actual residual ranks and expanded endpoint ranks. -/
theorem expanded_failure_count (y g : Responses m n) (p : Predictions m n) (ε : ℝ)
    (hstable : ∀ i k, i ≠ k → ∀ j, |p i k j-g i j| ≤ ε)
    (F t ell : ℕ) (htF : t ≤ F)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    (univ.filter fun i => expandedFailure y p ε i F t ell ht he).card ≤ ell := by
  apply (Finset.card_le_card ?_).trans
    (Extensions.Stability.reference_rank_count m (fun i => referenceRadius y g i t ht)
      ell he.1 he.2)
  intro i hi
  simp only [mem_filter, mem_univ, true_and] at *
  exact failure_forces_reference_rank y g p ε hstable i F t ell htF ht he hi

/-- Leave-one reference fit on the actual multiset of blocks. -/
def referencePrediction {X : Type*} [MeasurableSpace X]
    (A : Setup.Learner X n) (Z : Fin (m+1) → Setup.Block X n)
    (i : Fin (m+1)) (x : X) : ℝ :=
  A.predict ((univ.erase i).val.map Z) x

/-- The simultaneous on-sample deletion-stability event (6.27). -/
def onSampleDeletionStable {X : Type*} [MeasurableSpace X]
    (A : Setup.Learner X n) (Z : Fin (m+1) → Setup.Block X n) (ε : ℝ) : Prop :=
  ∀ i k, i ≠ k → ∀ j,
    |Setup.pairPrediction A Z i k (Z i j).1-
      referencePrediction A Z i (Z i j).1| ≤ ε

/-- Actual new-block failure of the explicit expanded rule (6.28). -/
def learnerExpandedFailure {X : Type*} [MeasurableSpace X]
    (A : Setup.Learner X n) (Z : Fin (m+1) → Setup.Block X n) (ε : ℝ)
    (i : Fin (m+1)) (F t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) : Prop :=
  F ≤ (univ.filter fun j => ¬
    (Setup.lowerEndpoint A Z i j t ell ht he-2*ε ≤ (Z i j).2 ∧
      (Z i j).2 ≤ Setup.upperEndpoint A Z i j t ell ht he+2*ε)).card

/-- Apply the full deterministic stability theorem to actual learner fits,
blocks, inner radii, and endpoint order statistics from the source model. -/
theorem learner_expanded_failure_count {X : Type*} [MeasurableSpace X]
    (A : Setup.Learner X n) (Z : Fin (m+1) → Setup.Block X n) (ε : ℝ)
    (hstable : onSampleDeletionStable A Z ε) (F t ell : ℕ) (htF : t ≤ F)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    (univ.filter fun i => learnerExpandedFailure A Z ε i F t ell ht he).card ≤ ell := by
  have harray := expanded_failure_count
    (fun i j => (Z i j).2)
    (fun i j => referencePrediction A Z i (Z i j).1)
    (fun i k j => Setup.pairPrediction A Z i k (Z i j).1)
    ε hstable F t ell htF ht he
  apply (Finset.card_le_card ?_).trans harray
  intro i hi
  simp only [mem_filter, mem_univ, true_and] at *
  unfold learnerExpandedFailure at hi
  apply hi.trans
  apply Finset.card_le_card
  intro j hj
  simp only [mem_filter, mem_univ, true_and] at *
  exact hj

/-- Expansion only removes failures of the actual statistical rule. -/
theorem learner_expanded_failure_implies_original {X : Type*} [MeasurableSpace X]
    (A : Setup.Learner X n) (Z : Fin (m+1) → Setup.Block X n) (ε : ℝ)
    (hε : 0 ≤ ε) (i : Fin (m+1)) (F t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m)
    (hfail : learnerExpandedFailure A Z ε i F t ell ht he) :
    Setup.failure A Z i F t ell ht he := by
  apply hfail.trans
  apply Finset.card_le_card
  intro j hj
  simp only [mem_filter, mem_univ, true_and] at *
  intro hc
  apply hj
  change Setup.lowerEndpoint A Z i j t ell ht he ≤ (Z i j).2 ∧
    (Z i j).2 ≤ Setup.upperEndpoint A Z i j t ell ht he at hc
  constructor <;> nlinarith [hc.1, hc.2]

/-- The general pointwise count remains available away from stability. -/
theorem learner_expanded_failure_count_unrestricted {X : Type*} [MeasurableSpace X]
    (A : Setup.Learner X n) (Z : Fin (m+1) → Setup.Block X n) (ε : ℝ)
    (hε : 0 ≤ ε) (F t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n)
    (he : 1 ≤ ell ∧ ell ≤ m) :
    (univ.filter fun i => learnerExpandedFailure A Z ε i F t ell ht he).card ≤
      if F < t then m+1 else min (m+1) (2 * min m (F*(ell-1)/(F-t+1)) + 1) := by
  apply (Finset.card_le_card ?_).trans
    (DeterministicUpper.learner_failure_label_count_le A Z F t ell ht he)
  intro i hi
  simp only [mem_filter, mem_univ, true_and] at *
  exact learner_expanded_failure_implies_original A Z ε hε i F t ell ht he hi

end
end MEJF.Stability
