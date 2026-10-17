import MEJF.DeterministicUpper
import MEJF.SetupMeasurable
import MEJF.SetupEquivariance
import MEJF.RankFrontier

/-! The statistical upper bound for actual measurable learners and arbitrary
exchangeable block laws, on the paper's original sample space. -/
namespace MEJF.MainUpper
open MeasureTheory MEJF.Setup MEJF.Exchangeability Finset
noncomputable section
attribute [local instance] Classical.propDecidable

variable {X : Type*} [MeasurableSpace X] {m n : ℕ}

/-- Uniform upper bound (3.2), for the actual finite-rank endpoint rule. -/
theorem failure_probability_le (A : Learner X n)
    (μ : Measure (Fin (m+1) → Block X n)) [IsProbabilityMeasure μ]
    (hμ : Exchangeable μ) (F t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) (i : Fin (m+1)) :
    μ.real {Z | Setup.failure A Z i F t ell ht he} ≤
      RankFrontier.failureRate m F t ell := by
  have hp := exchangeable_probability_le μ hμ
    (fun Z i => Setup.failure A Z i F t ell ht he)
    (fun i => Setup.measurableSet_failure A i F t ell ht he)
    (SetupEquivariance.failure_equivariant A F t ell ht he)
    (RankFrontier.failureCount m F t ell)
    (fun Z => by
      simpa only [RankFrontier.failureCount, RankFrontier.capacity] using
        DeterministicUpper.learner_failure_label_count_le A Z F t ell ht he) i
  simpa only [Fintype.card_fin, RankFrontier.failureRate] using hp

/-- The actual minimax set is inhabited by a constant learner and one fixed
constant block array. This avoids relying on a convention for the empty supremum. -/
lemma minimax_values_nonempty (m n : ℕ) (alpha : ℝ) (t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    {r : ℝ | ∃ (A : Learner UniversalCovariate n)
      (μ : Measure (Fin (m+1) → Block UniversalCovariate n)),
      IsProbabilityMeasure μ ∧ Exchangeable μ ∧
      r = μ.real {Z | Setup.failure A Z (Fin.last m) (failureRank alpha n) t ell ht he}}.Nonempty := by
  let A : Learner UniversalCovariate n := ⟨fun _ _ => 0, fun _ => measurable_const⟩
  let x : UniversalCovariate := ⟨0, by norm_num⟩
  let Z : Fin (m+1) → Block UniversalCovariate n := fun _ _ => (x,0)
  let μ : Measure (Fin (m+1) → Block UniversalCovariate n) := Measure.dirac Z
  have hμ : Exchangeable μ := by
    intro e
    have hm : Measurable (relabel e : (Fin (m+1) → Block UniversalCovariate n) → _) :=
      measurable_pi_iff.mpr (fun i => measurable_pi_apply (e.symm i))
    refine ⟨hm, ?_⟩
    change Measure.map (relabel e) (Measure.dirac Z) = Measure.dirac Z
    rw [Measure.map_dirac hm]
    rfl
  exact ⟨_, A, μ, by dsimp [μ]; infer_instance, hμ, rfl⟩

/-- Upper bound on the independently defined statistical supremum, not on a
formula that has been named Γ by definition. -/
theorem finiteRankGamma_le (m n : ℕ) (alpha : ℝ) (t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    finiteRankGamma m n alpha t ell ht he ≤
      RankFrontier.failureRate m (failureRank alpha n) t ell := by
  unfold finiteRankGamma
  apply csSup_le (minimax_values_nonempty m n alpha t ell ht he)
  intro r hr
  obtain ⟨A, μ, hprob, hex, rfl⟩ := hr
  letI : IsProbabilityMeasure μ := hprob
  exact failure_probability_le A μ hex _ t ell ht he (Fin.last m)

end
end MEJF.MainUpper
