import MEJF.GraphBound
import MEJF.Incidence
import MEJF.Setup

/-! The actual residual and endpoint events imply the sharp pointwise label count.
No implication from failure to degree demand is assumed: it is proved from the
sorted endpoint counts and the finite coordinate-incidence matrix. -/
namespace MEJF.DeterministicUpper

open Finset OrderStatistics
noncomputable section
attribute [local instance] Classical.propDecidable

variable {m n : ℕ}

/-- Responses and shared pair-fit predictions on the observed coordinates. -/
abbrev Responses (m n : ℕ) := Fin (m+1) → Fin n → ℝ
abbrev Predictions (m n : ℕ) := Fin (m+1) → Fin (m+1) → Fin n → ℝ

/-- The actual inner order statistic, with paper rank `n+1-t`. -/
def score (y : Responses m n) (p : Predictions m n)
    (i k : Fin (m+1)) (t : ℕ) (ht : 1 ≤ t ∧ t ≤ n) : ℝ :=
  stat (fun j => |y i j-p i k j|) (Setup.innerIndex n t ht)

def lower (y : Responses m n) (p : Predictions m n) (i : Fin (m+1)) (j : Fin n)
    (t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) : ℝ :=
  stat (fun k : Fin m => p i (i.succAbove k) j-score y p (i.succAbove k) i t ht)
    (Setup.lowerIndex m ell he)

def upper (y : Responses m n) (p : Predictions m n) (i : Fin (m+1)) (j : Fin n)
    (t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) : ℝ :=
  stat (fun k : Fin m => p i (i.succAbove k) j+score y p (i.succAbove k) i t ht)
    (Setup.upperIndex m ell he)

def coordinateCovered (y : Responses m n) (p : Predictions m n)
    (i : Fin (m+1)) (j : Fin n) (t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) : Prop :=
  lower y p i j t ell ht he ≤ y i j ∧ y i j ≤ upper y p i j t ell ht he

def blockFailure (y : Responses m n) (p : Predictions m n) (i : Fin (m+1))
    (F t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) : Prop :=
  F ≤ (univ.filter fun j => ¬ coordinateCovered y p i j t ell ht he).card

/-- Strict pairwise residual comparison (4.6). -/
def comparison (y : Responses m n) (p : Predictions m n)
    (t : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (i k : Fin (m+1)) : Prop :=
  score y p k i t ht < score y p i k t ht

lemma comparison_asymm (y : Responses m n) (p : Predictions m n)
    (t : ℕ) (ht : 1 ≤ t ∧ t ≤ n) :
    ∀ i k, comparison y p t ht i k → ¬ comparison y p t ht k i := by
  intro i k hik hki
  exact (not_lt_of_gt hik) hki

/-- Enumerating the other labels does not change the actual graph degree. -/
lemma enumerated_degree (y : Responses m n) (p : Predictions m n)
    (t : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (i : Fin (m+1)) :
    (univ.filter fun k : Fin m => comparison y p t ht i (i.succAbove k)).card =
      GraphBound.outDegree (comparison y p t ht) i := by
  classical
  unfold GraphBound.outDegree
  apply Finset.card_bij (fun k _ => i.succAbove k)
  · intro k hk
    simpa only [mem_filter, mem_univ, true_and] using hk
  · intro k hk l hl hkl
    exact Fin.succAbove_right_injective hkl
  · intro k hk
    have hki : k ≠ i := by
      intro h
      subst k
      have hself : comparison y p t ht i i := (mem_filter.mp hk).2
      exact lt_irrefl _ hself
    obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hki
    exact ⟨j, by simpa only [mem_filter, mem_univ, true_and] using hk, rfl⟩

/-- One missed aggregate coordinate has at least `m+1-ell` actual candidate misses. -/
lemma coordinate_miss_candidate_count (y : Responses m n) (p : Predictions m n)
    (i : Fin (m+1)) (j : Fin n) (t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m)
    (hmiss : ¬ coordinateCovered y p i j t ell ht he) :
    m+1-ell ≤ (univ.filter fun k : Fin m =>
      score y p (i.succAbove k) i t ht < |y i j-p i (i.succAbove k) j|).card := by
  have h := aggregate_miss_count
    (fun k : Fin m => p i (i.succAbove k) j-score y p (i.succAbove k) i t ht)
    (fun k : Fin m => p i (i.succAbove k) j+score y p (i.succAbove k) i t ht)
    (Setup.lowerIndex m ell he) (Setup.upperIndex m ell he) (by
      simp only [Setup.lowerIndex, Setup.upperIndex]
      omega) (y i j) hmiss
  simp only [Setup.upperIndex, count] at h
  simpa only [candidate_miss_iff, show m-ell+1 = m+1-ell by omega] using h

/-- Inner radii are nonnegative because each statistic is an actual residual. -/
lemma score_nonneg (y : Responses m n) (p : Predictions m n)
    (i k : Fin (m+1)) (t : ℕ) (ht : 1 ≤ t ∧ t ≤ n) :
    0 ≤ score y p i k t ht := abs_nonneg _

/-- Ordered outer ranks and actual nonnegative residual radii give a nonempty
aggregate interval. -/
theorem aggregate_nonempty_of_rank_balance (y : Responses m n) (p : Predictions m n)
    (i : Fin (m+1)) (j : Fin n) (t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m)
    (hbalance : ell ≤ m+1-ell) :
    lower y p i j t ell ht he ≤ upper y p i j t ell ht he := by
  apply OrderStatistics.aggregate_nonempty
  · intro k
    have := score_nonneg y p (i.succAbove k) i t ht
    linarith
  · change ell-1 ≤ m-ell
    omega

/-- Lemma 4.1 with its original nontrivial-demand hypothesis: the actual sorted
aggregate interval is nonempty at every coordinate. -/
theorem aggregate_nonempty_of_large_demand (y : Responses m n) (p : Predictions m n)
    (i : Fin (m+1)) (j : Fin n) (F t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) (htF : t ≤ F)
    (hlarge : m/2 < Incidence.threshold F m (m+1-ell) t) :
    lower y p i j t ell ht he ≤ upper y p i j t ell ht he := by
  have hw := Incidence.threshold_le_row F m (m+1-ell) t ht.1 htF (by omega)
  apply aggregate_nonempty_of_rank_balance y p i j t ell ht he
  omega

/-- Lemma 4.2, including the full bridge from actual endpoint misses to actual
pairwise residual degrees. The incidence demand is the equivalent floor form. -/
theorem failure_forces_high_outdegree (y : Responses m n) (p : Predictions m n)
    (i : Fin (m+1)) (F t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n)
    (he : 1 ≤ ell ∧ ell ≤ m) (htF : t ≤ F)
    (hfail : blockFailure y p i F t ell ht he) :
    Incidence.threshold F m (m+1-ell) t ≤
      GraphBound.outDegree (comparison y p t ht) i := by
  classical
  obtain ⟨J, hJ, hJF⟩ := Finset.exists_subset_card_eq hfail
  let B : J → Fin m → Prop := fun j k =>
    score y p (i.succAbove k) i t ht < |y i j.val-p i (i.succAbove k) j.val|
  let out : Finset (Fin m) :=
    univ.filter fun k => comparison y p t ht i (i.succAbove k)
  have hrow : ∀ j : J, m+1-ell ≤ Incidence.rowSum B j := by
    intro j
    have hj := hJ j.property
    have hmiss := (mem_filter.mp hj).2
    simpa only [Incidence.rowSum, B, sum_boole] using
      coordinate_miss_candidate_count y p i j.val t ell ht he hmiss
  have hforce : ∀ k, t ≤ Incidence.colSum B k → k ∈ out := by
    intro k hk
    have hcount : Incidence.colSum B k ≤
        count (fun j : Fin n => |y i j-p i (i.succAbove k) j|)
          (score y p (i.succAbove k) i t ht < ·) := by
      have hinj : Function.Injective (fun j : {j : J // B j k} =>
          (⟨j.val.val, j.property⟩ :
            {j : Fin n // score y p (i.succAbove k) i t ht <
              |y i j-p i (i.succAbove k) j|})) := by
        intro a b hab
        have hab' : a.val.val = b.val.val :=
          congrArg (fun x : {j : Fin n // score y p (i.succAbove k) i t ht <
            |y i j-p i (i.succAbove k) j|} => x.val) hab
        exact Subtype.ext (Subtype.ext hab')
      have hh := Fintype.card_le_of_injective _ hinj
      simpa only [Fintype.card_subtype, Incidence.colSum, sum_boole, count] using hh
    have hlt := residual_rank_gt
      (fun j : Fin n => |y i j-p i (i.succAbove k) j|)
      t ht.1 ht.2 (score y p (i.succAbove k) i t ht) (hk.trans hcount)
    exact mem_filter.mpr ⟨mem_univ _, hlt⟩
  have hcap := Incidence.incidence_capacity B out (m+1-ell) t hrow hforce
  have hcardJ : Fintype.card J = F := by simpa using hJF
  have hout : out.card = GraphBound.outDegree (comparison y p t ht) i :=
    enumerated_degree y p t ht i
  simp only [hcardJ, Fintype.card_fin, hout] at hcap
  exact Incidence.degree_threshold_of_capacity F m (m+1-ell) t _ ht.1 htF
    (by omega) (by
      rw [← hout]
      simpa only [Fintype.card_fin] using Finset.card_le_univ out) hcap

/-- The sharp pointwise upper bound (4.8), using the actual sorted rule. -/
theorem failure_label_count_le (y : Responses m n) (p : Predictions m n)
    (F t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n)
    (he : 1 ≤ ell ∧ ell ≤ m) (htF : t ≤ F) :
    (univ.filter fun i => blockFailure y p i F t ell ht he).card ≤
      min (m+1) (2 * min m (F*(ell-1)/(F-t+1)) + 1) := by
  let w := Incidence.threshold F m (m+1-ell) t
  have hw : w < m+1 := by
    have := Incidence.threshold_le_row F m (m+1-ell) t ht.1 htF (by omega)
    omega
  have hb := GraphBound.qualifying_subset_card_le (comparison y p t ht)
    (comparison_asymm y p t ht) (univ.filter fun i => blockFailure y p i F t ell ht he)
    w (by simpa using hw) (by
      intro i hi
      exact failure_forces_high_outdegree y p i F t ell ht he htF (mem_filter.mp hi).2)
  have hid : 2 * ((m+1)-w) - 1 = 2 * min m (F*(ell-1)/(F-t+1)) + 1 := by
    have hd : m-(m+1-ell) = ell-1 := by omega
    dsimp [w, Incidence.threshold]
    rw [hd]
    have := min_le_left m (F*(ell-1)/(F-t+1))
    omega
  simpa only [Fintype.card_fin, hid] using hb

/-- The finite-rank pointwise bound in both branches of (3.2). -/
theorem failure_label_count_le_all (y : Responses m n) (p : Predictions m n)
    (F t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    (univ.filter fun i => blockFailure y p i F t ell ht he).card ≤
      if F < t then m+1 else min (m+1) (2 * min m (F*(ell-1)/(F-t+1)) + 1) := by
  split_ifs with hFt
  · simpa only [Fintype.card_fin] using
      Finset.card_le_univ (univ.filter fun i => blockFailure y p i F t ell ht he)
  · exact failure_label_count_le y p F t ell ht he (by omega)

/-- Lemma 4.1 on the original learner and block objects. -/
theorem learner_aggregate_nonempty {X : Type*} [MeasurableSpace X]
    (A : Setup.Learner X n) (Z : Fin (m+1) → Setup.Block X n)
    (i : Fin (m+1)) (j : Fin n) (F t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) (htF : t ≤ F)
    (hlarge : m/2 < Incidence.threshold F m (m+1-ell) t) :
    Setup.lowerEndpoint A Z i j t ell ht he ≤ Setup.upperEndpoint A Z i j t ell ht he :=
  aggregate_nonempty_of_large_demand
    (fun i j => (Z i j).2)
    (fun i k j => Setup.pairPrediction A Z i k (Z i j).1)
    i j F t ell ht he htF hlarge

/-- Lemma 4.2 on the original learner, responses, residual scores, and failure event. -/
theorem learner_failure_forces_high_outdegree {X : Type*} [MeasurableSpace X]
    (A : Setup.Learner X n) (Z : Fin (m+1) → Setup.Block X n)
    (i : Fin (m+1)) (F t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n)
    (he : 1 ≤ ell ∧ ell ≤ m) (htF : t ≤ F)
    (hfail : Setup.failure A Z i F t ell ht he) :
    Incidence.threshold F m (m+1-ell) t ≤
      GraphBound.outDegree
        (fun i k => Setup.radius A Z k i t ht < Setup.radius A Z i k t ht) i :=
  failure_forces_high_outdegree
    (fun i j => (Z i j).2)
    (fun i k j => Setup.pairPrediction A Z i k (Z i j).1)
    i F t ell ht he htF hfail

/-- Apply the deterministic array theorem to every actual symmetric multiset
learner and every realized block tuple from the paper's sample space. -/
theorem learner_failure_label_count_le {X : Type*} [MeasurableSpace X]
    (A : Setup.Learner X n) (Z : Fin (m+1) → Setup.Block X n)
    (F t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    (univ.filter fun i => Setup.failure A Z i F t ell ht he).card ≤
      if F < t then m+1 else min (m+1) (2 * min m (F*(ell-1)/(F-t+1)) + 1) := by
  exact failure_label_count_le_all
    (fun i j => (Z i j).2)
    (fun i k j => Setup.pairPrediction A Z i k (Z i j).1) F t ell ht he

end
end MEJF.DeterministicUpper
