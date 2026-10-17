import MEJF.Stability
import MEJF.SetupMeasurable
import MEJF.SetupEquivariance
import MEJF.RankFrontier

/-! The actual statistical upper bound (6.29), including measurability and
relabeling properties derived from the source's measurable multiset learner. -/
namespace MEJF.StabilityProbability
open MeasureTheory MEJF.Setup MEJF.Stability MEJF.Exchangeability Finset
noncomputable section
attribute [local instance] Classical.propDecidable

variable {X : Type*} [MeasurableSpace X] {m n : ℕ}

lemma measurable_referencePrediction (A : Learner X n) (i : Fin (m+1)) :
    Measurable (fun q : (Fin (m+1) → Block X n) × X =>
      referencePrediction A q.1 i q.2) :=
  Setup.measurable_predict_finset A (univ.erase i)

lemma measurableSet_onSampleDeletionStable (A : Learner X n) (ε : ℝ) :
    MeasurableSet {Z : Fin (m+1) → Block X n | onSampleDeletionStable A Z ε} := by
  simp only [onSampleDeletionStable, Set.setOf_forall]
  refine MeasurableSet.iInter fun i => ?_
  refine MeasurableSet.iInter fun k => ?_
  refine MeasurableSet.iInter fun _hik => ?_
  refine MeasurableSet.iInter fun j => ?_
  exact measurableSet_le
    (continuous_abs.measurable.comp
      (((Setup.measurable_pairPrediction A i k).comp
        (measurable_id.prodMk (Setup.measurable_covariate i j))).sub
      ((measurable_referencePrediction A i).comp
        (measurable_id.prodMk (Setup.measurable_covariate i j))))) measurable_const

lemma measurableSet_expandedCovered (A : Learner X n) (ε : ℝ)
    (i : Fin (m+1)) (j : Fin n) (t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    MeasurableSet {Z : Fin (m+1) → Block X n |
      lowerEndpoint A Z i j t ell ht he-2*ε ≤ (Z i j).2 ∧
        (Z i j).2 ≤ upperEndpoint A Z i j t ell ht he+2*ε} := by
  exact (measurableSet_le
    ((Setup.measurable_lowerEndpoint A i j t ell ht he).sub measurable_const)
    (Setup.measurable_response i j)).inter
    (measurableSet_le (Setup.measurable_response i j)
      ((Setup.measurable_upperEndpoint A i j t ell ht he).add measurable_const))

lemma measurableSet_learnerExpandedFailure (A : Learner X n) (ε : ℝ)
    (i : Fin (m+1)) (F t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    MeasurableSet {Z : Fin (m+1) → Block X n |
      learnerExpandedFailure A Z ε i F t ell ht he} := by
  have hm : Measurable (fun Z : Fin (m+1) → Block X n =>
      ∑ j : Fin n, if ¬ (lowerEndpoint A Z i j t ell ht he-2*ε ≤ (Z i j).2 ∧
        (Z i j).2 ≤ upperEndpoint A Z i j t ell ht he+2*ε) then (1 : ℕ) else 0) := by
    apply Finset.measurable_sum
    intro j _
    exact Measurable.ite (measurableSet_expandedCovered A ε i j t ell ht he).compl
      measurable_const measurable_const
  have hc : Measurable (fun Z : Fin (m+1) → Block X n =>
      (univ.filter fun j => ¬ (lowerEndpoint A Z i j t ell ht he-2*ε ≤ (Z i j).2 ∧
        (Z i j).2 ≤ upperEndpoint A Z i j t ell ht he+2*ε)).card) := by
    simpa only [Finset.sum_boole] using hm
  exact measurableSet_le measurable_const hc

lemma referencePrediction_relabel (A : Learner X n) (Z : Fin (m+1) → Block X n)
    (e : Equiv.Perm (Fin (m+1))) (i : Fin (m+1)) (x : X) :
    referencePrediction A (relabel e Z) (e i) x = referencePrediction A Z i x := by
  have h := SetupEquivariance.training_relabel Z e i i
  simp only [Finset.erase_idem] at h
  unfold referencePrediction
  rw [h]

/-- The stability event (6.27) is invariant under all block permutations. -/
theorem onSampleDeletionStable_relabel (A : Learner X n) (Z : Fin (m+1) → Block X n)
    (e : Equiv.Perm (Fin (m+1))) (ε : ℝ) :
    onSampleDeletionStable A (relabel e Z) ε ↔ onSampleDeletionStable A Z ε := by
  constructor
  · intro h i k hik j
    have h' := h (e i) (e k) (fun hh => hik (e.injective hh)) j
    have hZi : relabel e Z (e i) = Z i := by simp [relabel]
    simpa only [hZi, SetupEquivariance.pairPrediction_relabel,
      referencePrediction_relabel] using h'
  · intro h i k hik j
    obtain ⟨a, rfl⟩ := e.surjective i
    obtain ⟨b, rfl⟩ := e.surjective k
    have hZi : relabel e Z (e a) = Z a := by simp [relabel]
    simpa only [hZi, SetupEquivariance.pairPrediction_relabel,
      referencePrediction_relabel] using h a b (fun hh => hik (congrArg e hh)) j

/-- Equivariance of expanded-rule failures follows from the actual endpoints. -/
theorem learnerExpandedFailure_equivariant (A : Learner X n) (ε : ℝ) (F t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    Equivariant (fun Z : Fin (m+1) → Block X n => fun i =>
      learnerExpandedFailure A Z ε i F t ell ht he) := by
  intro e Z i
  unfold learnerExpandedFailure
  simp only [SetupEquivariance.lowerEndpoint_relabel, SetupEquivariance.upperEndpoint_relabel]
  simp only [relabel, Function.comp_apply, Equiv.symm_apply_apply]

/-- Source Theorem 6.5, equation (6.29), for the actual statistical experiment.
All event measurability, equivariance, and both pointwise counts are derived. -/
theorem expanded_failure_probability_le (A : Learner X n)
    (μ : Measure (Fin (m+1) → Block X n)) [IsProbabilityMeasure μ]
    (hμ : Exchangeable μ) (ε : ℝ) (hε : 0 ≤ ε) (F t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) (htF : t ≤ F)
    (γ : ℝ) (hprob : 1-γ ≤ μ.real {Z | onSampleDeletionStable A Z ε})
    (i : Fin (m+1)) :
    μ.real {Z | learnerExpandedFailure A Z ε i F t ell ht he} ≤
      (ell : ℝ)/(m+1 : ℕ) +
        ((RankFrontier.failureCount m F t ell : ℕ) - (ell : ℝ))/(m+1 : ℕ)*γ := by
  have hcap := RankFrontier.outer_le_capacity ht.1 htF (by omega : ell ≤ m+1)
  have hes : ell ≤ RankFrontier.failureCount m F t ell := by
    unfold RankFrontier.failureCount
    rw [if_neg (not_lt.mpr htF)]
    omega
  have hp := Exchangeability.probability_le_two_counts μ
    (fun Z i => learnerExpandedFailure A Z ε i F t ell ht he)
    (fun i => measurableSet_learnerExpandedFailure A ε i F t ell ht he) i
    (fun j => Exchangeability.event_probability_eq μ hμ _
      (fun i => measurableSet_learnerExpandedFailure A ε i F t ell ht he)
      (learnerExpandedFailure_equivariant A ε F t ell ht he) j i)
    {Z | onSampleDeletionStable A Z ε}
    (measurableSet_onSampleDeletionStable A ε)
    ell (RankFrontier.failureCount m F t ell) hes
    (fun Z hZ => learner_expanded_failure_count A Z ε hZ F t ell htF ht he)
    (fun Z _ => by
      simpa only [RankFrontier.failureCount, RankFrontier.capacity] using
        learner_expanded_failure_count_unrestricted A Z ε hε F t ell ht he)
    γ hprob
  simpa only [Fintype.card_fin] using hp

/-- Almost-sure on-sample stability gives the ell/N upper bound. -/
theorem expanded_failure_probability_le_stable (A : Learner X n)
    (μ : Measure (Fin (m+1) → Block X n)) [IsProbabilityMeasure μ]
    (hμ : Exchangeable μ) (ε : ℝ) (hε : 0 ≤ ε) (F t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) (htF : t ≤ F)
    (hprob : μ.real {Z | onSampleDeletionStable A Z ε} = 1) (i : Fin (m+1)) :
    μ.real {Z | learnerExpandedFailure A Z ε i F t ell ht he} ≤
      (ell : ℝ)/(m+1 : ℕ) := by
  have h := expanded_failure_probability_le A μ hμ ε hε F t ell ht he htF 0
    (by rw [hprob]; norm_num) i
  simpa only [mul_zero, add_zero] using h

end
end MEJF.StabilityProbability
