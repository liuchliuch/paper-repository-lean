import MEJF.Setup
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! Measurability of the actual multiset fits, finite-rank radii, endpoint
quantiles, coverage events and block-failure events in §§2 and 4. -/
namespace MEJF.Setup
open MeasureTheory Finset
noncomputable section
attribute [local instance] Classical.propDecidable

variable {X : Type*} [MeasurableSpace X] {N m n : ℕ}

/-- A finite set enumeration reproduces the same training multiset, so its
ordering cannot change the learner input. -/
lemma ofFn_finset_map {B : Type*} (s : Finset (Fin N)) (Z : Fin N → B) :
    ((List.ofFn (fun l : Fin s.card => Z (s.orderEmbOfFin rfl l)) : List B) : Multiset B) =
      s.val.map Z := by
  rw [List.ofFn_comp', List.ofFn_eq_map, s.listMap_orderEmbOfFin_finRange rfl]
  simp only [← Multiset.map_coe, Finset.sort_eq]

/-- Joint measurability applies to the fixed finite training set at its actual
arity; the complete array remains the measurable input. -/
lemma measurable_predict_finset (A : Learner X n) (s : Finset (Fin N)) :
    Measurable (fun q : (Fin N → Block X n) × X => A.predict (s.val.map q.1) q.2) := by
  have henum : Measurable (fun q : (Fin N → Block X n) × X =>
      ((fun l : Fin s.card => q.1 (s.orderEmbOfFin rfl l)), q.2)) := by
    apply Measurable.prodMk
    · apply measurable_pi_lambda
      intro l
      exact (measurable_pi_apply (s.orderEmbOfFin rfl l)).comp measurable_fst
    · exact measurable_snd
  have h := (A.measurable_predict s.card).comp henum
  simpa only [Function.comp_def, ofFn_finset_map] using h

lemma measurable_pairPrediction (A : Learner X n) (i k : Fin N) :
    Measurable (fun q : (Fin N → Block X n) × X => pairPrediction A q.1 i k q.2) :=
  measurable_predict_finset A ((univ.erase i).erase k)

lemma measurable_response (i : Fin N) (j : Fin n) :
    Measurable (fun Z : Fin N → Block X n => (Z i j).2) :=
  ((measurable_pi_apply j).comp (measurable_pi_apply i)).snd

lemma measurable_covariate (i : Fin N) (j : Fin n) :
    Measurable (fun Z : Fin N → Block X n => (Z i j).1) :=
  ((measurable_pi_apply j).comp (measurable_pi_apply i)).fst

lemma measurable_radius (A : Learner X n) (i k : Fin N)
    (t : ℕ) (ht : 1 ≤ t ∧ t ≤ n) :
    Measurable (fun Z : Fin N → Block X n => radius A Z i k t ht) := by
  apply OrderStatistics.measurable_stat_comp
  intro j
  exact continuous_abs.measurable.comp ((measurable_response i j).sub
    ((measurable_pairPrediction A i k).comp
      (measurable_id.prodMk (measurable_covariate i j))))

lemma measurable_lowerEndpoint (A : Learner X n) (i : Fin (m+1)) (j : Fin n)
    (t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    Measurable (fun Z : Fin (m+1) → Block X n => lowerEndpoint A Z i j t ell ht he) := by
  apply OrderStatistics.measurable_stat_comp
  intro k
  exact ((measurable_pairPrediction A i (i.succAbove k)).comp
    (measurable_id.prodMk (measurable_covariate i j))).sub
      (measurable_radius A (i.succAbove k) i t ht)

lemma measurable_upperEndpoint (A : Learner X n) (i : Fin (m+1)) (j : Fin n)
    (t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    Measurable (fun Z : Fin (m+1) → Block X n => upperEndpoint A Z i j t ell ht he) := by
  apply OrderStatistics.measurable_stat_comp
  intro k
  exact ((measurable_pairPrediction A i (i.succAbove k)).comp
    (measurable_id.prodMk (measurable_covariate i j))).add
      (measurable_radius A (i.succAbove k) i t ht)

lemma measurableSet_covered (A : Learner X n) (i : Fin (m+1)) (j : Fin n)
    (t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    MeasurableSet {Z : Fin (m+1) → Block X n | covered A Z i j t ell ht he} := by
  exact (measurableSet_le (measurable_lowerEndpoint A i j t ell ht he)
    (measurable_response i j)).inter
      (measurableSet_le (measurable_response i j)
        (measurable_upperEndpoint A i j t ell ht he))

lemma measurable_missCount (A : Learner X n) (i : Fin (m+1))
    (t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    Measurable (fun Z : Fin (m+1) → Block X n =>
      (univ.filter fun j => ¬ covered A Z i j t ell ht he).card) := by
  have h : Measurable (fun Z : Fin (m+1) → Block X n =>
      ∑ j : Fin n, if ¬ covered A Z i j t ell ht he then (1 : ℕ) else 0) := by
    apply Finset.measurable_sum
    intro j _
    exact Measurable.ite (measurableSet_covered A i j t ell ht he).compl
      measurable_const measurable_const
  simpa only [Finset.sum_boole] using h

/-- The event supplied to the exchangeability averaging theorem is measurable
on the full statistical sample space, for every measurable multiset learner. -/
lemma measurableSet_failure (A : Learner X n) (i : Fin (m+1))
    (F t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    MeasurableSet {Z : Fin (m+1) → Block X n | failure A Z i F t ell ht he} :=
  measurableSet_le measurable_const (measurable_missCount A i t ell ht he)

end
end MEJF.Setup
