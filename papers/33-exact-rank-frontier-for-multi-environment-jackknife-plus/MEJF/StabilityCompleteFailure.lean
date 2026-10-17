import MEJF.StabilitySharpness
import MEJF.Sharpness

namespace MEJF.StabilitySharpness
open MeasureTheory Setup Stability StabilityProbability Exchangeability Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {m n : ℕ}

/-- Each block has exactly F responses beyond the expanded zero interval. -/
def completeData (ε : ℝ) (F : ℕ) : Fin (m+1) → Block UniversalCovariate n :=
  fun _i j => (⟨0, by norm_num⟩, if j.val < F then 2*ε+1 else 0)

lemma complete_radius (ε : ℝ) (hε : 0 ≤ ε) (F t : ℕ) (hFt : F < t)
    (ht : 1 ≤ t ∧ t ≤ n) (i k : Fin (m+1)) :
    Setup.radius (zeroLearner n) (completeData ε F) i k t ht = 0 := by
  let u : Fin n → ℝ := fun j => if j.val < F then 2*ε+1 else 0
  have hFn : F ≤ n := by omega
  have hu : ∀ j, 0 ≤ u j := by intro j; dsimp [u]; split_ifs <;> linarith
  have hrad : Setup.radius (zeroLearner n) (completeData ε F) i k t ht =
      OrderStatistics.stat u (Setup.innerIndex n t ht) := by
    unfold Setup.radius
    apply congrArg (fun v : Fin n → ℝ => OrderStatistics.stat v (Setup.innerIndex n t ht))
    funext j
    simpa only [Setup.pairPrediction, zeroLearner, completeData, sub_zero] using abs_of_nonneg (hu j)
  rw [hrad]
  have hzero : OrderStatistics.count u (· ≤ 0) = n-F := by
    have hs : (univ.filter fun j => u j ≤ 0) =
        univ.filter (fun j : Fin n => ¬ j.val < F) := by
      ext j
      simp only [mem_filter, mem_univ, true_and]
      by_cases hj : j.val < F
      · simp only [u, if_pos hj, hj, not_true_eq_false, iff_false, not_le]
        linarith
      · simp [u, hj]
    unfold OrderStatistics.count
    rw [hs]
    have hc := Finset.filter_card_add_filter_neg_card_eq_card (s := (univ : Finset (Fin n)))
      (p := fun j => j.val < F)
    have hfirst : (univ.filter fun j : Fin n => j.val < F).card = F :=
      Sharpness.firstRows_card hFn
    rw [hfirst] at hc
    simp only [card_univ, Fintype.card_fin] at hc
    omega
  apply le_antisymm
  · apply (OrderStatistics.stat_le_iff_count _ _ _).mpr
    rw [hzero]
    change n-t < n-F
    omega
  · exact OrderStatistics.min_le_stat u _ 0 hu

lemma complete_endpoints (ε : ℝ) (hε : 0 ≤ ε) (F t ell : ℕ) (hFt : F < t)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) (i : Fin (m+1)) (j : Fin n) :
    Setup.lowerEndpoint (zeroLearner n) (completeData ε F) i j t ell ht he = 0 ∧
      Setup.upperEndpoint (zeroLearner n) (completeData ε F) i j t ell ht he = 0 := by
  constructor
  · unfold Setup.lowerEndpoint
    simp_rw [complete_radius ε hε F t hFt ht]
    simp [Setup.pairPrediction, zeroLearner, OrderStatistics.stat_const]
  · unfold Setup.upperEndpoint
    simp_rw [complete_radius ε hε F t hFt ht]
    simp [Setup.pairPrediction, zeroLearner, OrderStatistics.stat_const]

lemma complete_failure (ε : ℝ) (hε : 0 ≤ ε) (F t ell : ℕ) (hFt : F < t)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) (i : Fin (m+1)) :
    learnerExpandedFailure (zeroLearner n) (completeData ε F) ε i F t ell ht he := by
  unfold learnerExpandedFailure
  have hs : (univ.filter fun j => ¬
      (Setup.lowerEndpoint (zeroLearner n) (completeData ε F) i j t ell ht he-2*ε ≤
        (completeData ε F i j).2 ∧ (completeData ε F i j).2 ≤
      Setup.upperEndpoint (zeroLearner n) (completeData ε F) i j t ell ht he+2*ε)) =
      Sharpness.firstRows F n := by
    ext j
    simp only [mem_filter, mem_univ, true_and, Sharpness.firstRows]
    rw [(complete_endpoints ε hε F t ell hFt ht he i j).1,
      (complete_endpoints ε hε F t ell hFt ht he i j).2]
    change ¬ (0-2*ε ≤ (if j.val < F then 2*ε+1 else 0) ∧
      (if j.val < F then 2*ε+1 else 0) ≤ 0+2*ε) ↔ j.val < F
    by_cases hj : j.val < F
    · simp only [hj, ite_true, iff_true]
      intro hc
      linarith [hc.2]
    · simp only [hj, ite_false, iff_false, not_not]
      constructor <;> linarith
  rw [hs, Sharpness.firstRows_card (by omega : F ≤ n)]

/-- Positive outer ranks with t>F fail with probability one under a learner
that is simultaneously zero-stable on every possible sample. -/
theorem stable_complete_attaining_model (m n : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (F t ell : ℕ)
    (hFt : F < t) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    ∃ (A : Learner UniversalCovariate n)
      (Z : Fin (m+1) → Block UniversalCovariate n),
      (∀ W : Fin (m+1) → Block UniversalCovariate n, onSampleDeletionStable A W ε) ∧
      (FiniteExchangeable.blockPermutationLaw Z).real
        {W | learnerExpandedFailure A W ε (Fin.last m) F t ell ht he} = 1 := by
  refine ⟨zeroLearner n, completeData ε F, zero_stable ε hε, ?_⟩
  have hp := FiniteExchangeable.blockPermutationLaw_equivariant_probability (completeData ε F)
    (fun W i => learnerExpandedFailure (zeroLearner n) W ε i F t ell ht he)
    (fun i => measurableSet_learnerExpandedFailure (zeroLearner n) ε i F t ell ht he)
    (learnerExpandedFailure_equivariant (zeroLearner n) ε F t ell ht he) (Fin.last m)
  have hc : (univ.filter fun i : Fin (m+1) =>
      learnerExpandedFailure (zeroLearner n) (completeData ε F) ε i F t ell ht he).card = m+1 := by
    have hs : (univ.filter fun i : Fin (m+1) =>
      learnerExpandedFailure (zeroLearner n) (completeData ε F) ε i F t ell ht he) = univ := by
      ext i
      simp only [mem_filter, mem_univ, true_and, iff_true]
      exact complete_failure ε hε F t ell hFt ht he i
    rw [hs]
    simp
  rw [hc] at hp
  have hne : ((m+1 : ℕ) : ℝ) ≠ 0 := by positivity
  simpa only [Fintype.card_fin, div_self hne] using hp

/-- The t>F branch of the independently defined stable-class supremum. -/
theorem stableFiniteRankGamma_high_inner (m n F t ell : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hFt : F < t) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    stableFiniteRankGamma m n F t ell ε ht he = 1 := by
  obtain ⟨A, Z, hall, hp⟩ := stable_complete_attaining_model m n ε hε F t ell hFt ht he
  let μ := FiniteExchangeable.blockPermutationLaw Z
  have hprob : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  letI : IsProbabilityMeasure μ := hprob
  have hstable : μ.real {W | onSampleDeletionStable A W ε} = 1 := by
    have hs : {W : Fin (m+1) → Block UniversalCovariate n | onSampleDeletionStable A W ε} = Set.univ := by
      ext W
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact hall W
    rw [hs]
    exact measureReal_univ_eq_one
  have hmem : (1 : ℝ) ∈ {r : ℝ | ∃ (A : Learner UniversalCovariate n)
      (ν : Measure (Fin (m+1) → Block UniversalCovariate n)),
      IsProbabilityMeasure ν ∧ Exchangeable ν ∧
      ν.real {W | onSampleDeletionStable A W ε} = 1 ∧
      r = ν.real {W | learnerExpandedFailure A W ε (Fin.last m) F t ell ht he}} :=
    ⟨A, μ, hprob, FiniteExchangeable.blockPermutationLaw_exchangeable Z, hstable, hp.symm⟩
  have hbound : ∀ r ∈ {r : ℝ | ∃ (A : Learner UniversalCovariate n)
      (ν : Measure (Fin (m+1) → Block UniversalCovariate n)),
      IsProbabilityMeasure ν ∧ Exchangeable ν ∧
      ν.real {W | onSampleDeletionStable A W ε} = 1 ∧
      r = ν.real {W | learnerExpandedFailure A W ε (Fin.last m) F t ell ht he}}, r ≤ 1 := by
    intro r hr
    obtain ⟨B, ν, hν, hex, hs, rfl⟩ := hr
    letI : IsProbabilityMeasure ν := hν
    exact measureReal_le_one
  unfold stableFiniteRankGamma
  exact le_antisymm (csSup_le ⟨_, hmem⟩ hbound) (le_csSup ⟨_, hbound⟩ hmem)

end
end MEJF.StabilitySharpness
