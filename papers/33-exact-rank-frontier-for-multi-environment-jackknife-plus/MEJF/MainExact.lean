import MEJF.MainUpper
import MEJF.Sharpness
import MEJF.FiniteExchangeable

/-! The balanced minimax identity (3.2) for the actual statistical supremum.
The attaining law is explicitly the uniform permutation law of finitely many
complete blocks; the learner is jointly measurable on the universal space. -/
namespace MEJF.MainExact
open MeasureTheory MEJF.Setup MEJF.Exchangeability Finset
noncomputable section
attribute [local instance] Classical.propDecidable

/-- A single measurable learner and a finite exchangeable law attain the upper
bound, for every admissible finite integer parameter tuple. -/
theorem exists_attaining_model (m n F t ell : ℕ) (hm : 1 ≤ m)
    (hF : 1 ≤ F) (hFn : F ≤ n) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    ∃ (A : Learner UniversalCovariate n)
      (Z : Fin (m+1) → Block UniversalCovariate n),
      (FiniteExchangeable.blockPermutationLaw Z).real
        {W | Setup.failure A W (Fin.last m) F t ell ht he} =
      RankFrontier.failureRate m F t ell := by
  obtain ⟨A, Z, hcount⟩ := Sharpness.exists_exact_failure_count_model
    m n F t ell hm hF hFn ht he (PredictionTable.unitEmbedding (m+1) n)
    (PredictionTable.unitEmbedding (m+1) n).injective
  refine ⟨A, Z, ?_⟩
  have hp := FiniteExchangeable.blockPermutationLaw_equivariant_probability Z
    (fun W i => Setup.failure A W i F t ell ht he)
    (fun i => Setup.measurableSet_failure A i F t ell ht he)
    (SetupEquivariance.failure_equivariant A F t ell ht he) (Fin.last m)
  simpa only [hcount, Fintype.card_fin, RankFrontier.failureRate,
    RankFrontier.failureCount, RankFrontier.capacity] using hp

/-- Theorem 3.1's exact minimax identity, retaining the original supremum over
exchangeable laws and all jointly measurable multiset learners on [0,1]. -/
theorem finiteRankGamma_eq (m n : ℕ) (alpha : ℝ) (ha : 0 ≤ alpha) (ha1 : alpha < 1)
    (t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    finiteRankGamma m n alpha t ell ht he =
      RankFrontier.failureRate m (failureRank alpha n) t ell := by
  apply le_antisymm (MainUpper.finiteRankGamma_le m n alpha t ell ht he)
  have hn : 0 < n := by omega
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hFn : failureRank alpha n ≤ n := by
    unfold failureRank
    have hx : alpha * (n:ℝ) < n := by nlinarith
    have hh := (Nat.floor_lt (mul_nonneg ha hnR.le)).mpr hx
    omega
  obtain ⟨A, Z, hp⟩ := exists_attaining_model m n (failureRank alpha n) t ell
    (by omega) (by unfold failureRank; omega) hFn ht he
  let μ := FiniteExchangeable.blockPermutationLaw Z
  have hb : BddAbove {r : ℝ | ∃ (A : Learner UniversalCovariate n)
      (μ : Measure (Fin (m+1) → Block UniversalCovariate n)),
      IsProbabilityMeasure μ ∧ Exchangeable μ ∧
      r = μ.real {W | Setup.failure A W (Fin.last m) (failureRank alpha n) t ell ht he}} := by
    refine ⟨RankFrontier.failureRate m (failureRank alpha n) t ell, ?_⟩
    intro r hr
    obtain ⟨A, ν, hprob, hex, rfl⟩ := hr
    letI : IsProbabilityMeasure ν := hprob
    exact MainUpper.failure_probability_le A ν hex _ t ell ht he (Fin.last m)
  unfold finiteRankGamma
  apply le_csSup hb
  exact ⟨A, μ, by dsimp [μ]; infer_instance,
    FiniteExchangeable.blockPermutationLaw_exchangeable Z, hp.symm⟩

end
end MEJF.MainExact
