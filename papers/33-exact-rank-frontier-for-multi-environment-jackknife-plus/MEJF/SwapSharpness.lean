import MEJF.SwapRobustness
import MEJF.MainExact

/-! Corollary 6.7 on the actual statistical learner/block objects, including
sharp tilted laws and the exact variational swap-TV defect. -/
namespace MEJF.SwapRobustness
open MeasureTheory Setup Exchangeability Finset
noncomputable section
attribute [local instance] Classical.propDecidable
local instance permMeasurableSpace (N : ℕ) : MeasurableSpace (Equiv.Perm (Fin N)) := ⊤
local instance permMeasurableSingletonClass (N : ℕ) :
    MeasurableSingletonClass (Equiv.Perm (Fin N)) := ⟨fun _ => trivial⟩

/-- Exact counts propagate to the entire uniformly permuted finite orbit. -/
lemma blockPermutationLaw_count_eq_ae {N : ℕ} {B : Type*} [MeasurableSpace B]
    (data : Fin N → B) (H : (Fin N → B) → Fin N → Prop)
    (hH : ∀ i, MeasurableSet {z | H z i}) (heq : Equivariant H)
    (s : ℕ) (hbase : (univ.filter (H data)).card = s) :
    ∀ᵐ z ∂FiniteExchangeable.blockPermutationLaw data, (univ.filter (H z)).card = s := by
  have hm : Measurable (fun z : Fin N → B => (univ.filter (H z)).card) := by
    have hs : Measurable (fun z : Fin N → B => ∑ i : Fin N, if H z i then (1 : ℕ) else 0) := by
      apply Finset.measurable_sum
      intro i _
      exact Measurable.ite (hH i) measurable_const measurable_const
    simpa only [Finset.sum_boole] using hs
  change ∀ᵐ z ∂(((FiniteExchangeable.permutationMeasure (Fin N)).map
    FiniteExchangeable.typeArray).map (FiniteExchangeable.dataArray data)),
      (univ.filter (H z)).card = s
  rw [Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
  apply (ae_map_iff (measurable_of_finite _).aemeasurable
    (hm (measurableSet_singleton s))).2
  apply ae_of_all
  intro p
  change (univ.filter (H (data ∘ p))).card = s
  let S := univ.filter (H data)
  have hrel (i : Fin N) : H (data ∘ p) i ↔ p i ∈ S := by
    have hh := heq p.symm data (p i)
    simpa [Exchangeability.relabel, S] using hh
  calc
    _ = (univ.filter fun i => p i ∈ S).card := by
      congr 1
      ext i
      simp only [mem_filter, mem_univ, true_and, hrel]
    _ = S.card := FiniteExchangeable.permutation_selected_count S p
    _ = s := hbase

/-- Actual learner/block upper guarantee in (6.37). -/
theorem source_failure_probability_le {X : Type*} [MeasurableSpace X] {m n : ℕ}
    (A : Learner X n) (P : Measure (Fin (m+1) → Block X n)) [IsProbabilityMeasure P]
    (F t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) (i : Fin (m+1)) :
    P.real {Z | Setup.failure A Z i F t ell ht he} ≤
      min 1 ((RankFrontier.failureCount m F t ell : ℝ)/(m+1 : ℕ)+swapDefect P i) := by
  have hp := probability_le_count_add_swapDefect P
    (fun Z i => Setup.failure A Z i F t ell ht he)
    (fun i => Setup.measurableSet_failure A i F t ell ht he)
    (SetupEquivariance.failure_equivariant A F t ell ht he)
    (RankFrontier.failureCount m F t ell)
    (fun Z => by
      simpa only [RankFrontier.failureCount, RankFrontier.capacity] using
        DeterministicUpper.learner_failure_label_count_le A Z F t ell ht he) i
  simpa only [Fintype.card_fin] using hp

/-- Corollary 6.7 sharpness (6.38): a genuine measurable learner and probability
law attain every permitted additive swap defect. The TV is the actual
supremum over measurable events, rather than an eventwise supplied bound. -/
theorem source_swap_sharpness (m n F t ell : ℕ) (hF : 1 ≤ F) (hFn : F ≤ n)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m)
    (hsmall : RankFrontier.failureCount m F t ell < m+1)
    (η : ℝ) (hη : 0 ≤ η)
    (hηmax : η ≤ 1-(RankFrontier.failureCount m F t ell : ℝ)/(m+1 : ℕ)) :
    ∃ (A : Learner UniversalCovariate n)
      (P : Measure (Fin (m+1) → Block UniversalCovariate n)),
      IsProbabilityMeasure P ∧ swapDefect P (Fin.last m) = η ∧
      P.real {Z | Setup.failure A Z (Fin.last m) F t ell ht he} =
        (RankFrontier.failureCount m F t ell : ℝ)/(m+1 : ℕ)+η := by
  obtain ⟨A, data, hbase⟩ := Sharpness.exists_exact_failure_count_model
    m n F t ell (by omega) hF hFn ht he (PredictionTable.unitEmbedding (m+1) n)
    (PredictionTable.unitEmbedding (m+1) n).injective
  have hbase' : (univ.filter fun i => Setup.failure A data i F t ell ht he).card =
      RankFrontier.failureCount m F t ell := by
    simpa only [RankFrontier.failureCount, RankFrontier.capacity] using hbase
  let Q := FiniteExchangeable.blockPermutationLaw data
  have hcount := blockPermutationLaw_count_eq_ae data
    (fun Z i => Setup.failure A Z i F t ell ht he)
    (fun i => Setup.measurableSet_failure A i F t ell ht he)
    (SetupEquivariance.failure_equivariant A F t ell ht he)
    (RankFrontier.failureCount m F t ell) hbase'
  obtain ⟨P, hP, hdef, hfail⟩ := exists_sharp_tilt Q
    (FiniteExchangeable.blockPermutationLaw_exchangeable data)
    (fun Z i => Setup.failure A Z i F t ell ht he)
    (fun i => Setup.measurableSet_failure A i F t ell ht he)
    (SetupEquivariance.failure_equivariant A F t ell ht he)
    (RankFrontier.failureCount m F t ell) hcount
    (RankFrontier.failureCount_pos m F t ell)
    (by simpa only [Fintype.card_fin] using hsmall) (Fin.last m) η hη
    (by simpa only [Fintype.card_fin] using hηmax)
  refine ⟨A, P, hP, hdef, ?_⟩
  simpa only [Fintype.card_fin] using hfail

end
end MEJF.SwapRobustness
