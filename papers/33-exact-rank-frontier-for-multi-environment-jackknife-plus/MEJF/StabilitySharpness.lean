import MEJF.StabilityProbability
import MEJF.FiniteExchangeable
import Mathlib.Order.Interval.Finset.Fin

/-! Constant-learner sharpness of the stable positive-rank law (6.30).
All coordinates of each base block have one separated positive response. -/
namespace MEJF.StabilitySharpness
open MeasureTheory Setup Stability StabilityProbability Exchangeability Finset
noncomputable section
attribute [local instance] Classical.propDecidable

variable {m n : ℕ}

def zeroLearner (n : ℕ) : Learner UniversalCovariate n :=
  ⟨fun _ _ => 0, fun _ => measurable_const⟩

def spaced (ε : ℝ) (i : Fin (m+1)) : ℝ := (2*ε+1)*(i.val+1)

def baseData (ε : ℝ) : Fin (m+1) → Block UniversalCovariate n :=
  fun i _j => (⟨0, by norm_num⟩, spaced ε i)

lemma spaced_pos (ε : ℝ) (hε : 0 ≤ ε) (i : Fin (m+1)) : 0 < spaced ε i := by
  unfold spaced
  positivity

lemma spaced_mono (ε : ℝ) (hε : 0 ≤ ε) : Monotone (spaced ε : Fin (m+1) → ℝ) := by
  intro i k hik
  have hh : (i.val : ℝ) ≤ k.val := by exact_mod_cast hik
  unfold spaced
  nlinarith

lemma spaced_gap (ε : ℝ) (hε : 0 ≤ ε) (i k : Fin (m+1)) :
    spaced ε k+2*ε < spaced ε i ↔ k < i := by
  constructor
  · intro h
    by_contra! hki
    have hh := spaced_mono ε hε hki
    linarith
  · intro hki
    have hh : (k.val : ℝ)+1 ≤ i.val := by exact_mod_cast (show k.val+1 ≤ i.val by omega)
    unfold spaced
    nlinarith

lemma stat_self_of_monotone (u : Fin m → ℝ) (hu : Monotone u) (k : Fin m) :
    OrderStatistics.stat u k = u k := by
  have hh := Tuple.unique_monotone (Tuple.monotone_sort u) (σ := Tuple.sort u)
    (τ := Equiv.refl (Fin m)) hu
  exact congrFun hh k

lemma zero_stable (ε : ℝ) (hε : 0 ≤ ε)
    (Z : Fin (m+1) → Block UniversalCovariate n) :
    onSampleDeletionStable (zeroLearner n) Z ε := by
  intro i k hik j
  simpa [Setup.pairPrediction, Stability.referencePrediction, zeroLearner] using hε

lemma base_radius (ε : ℝ) (hε : 0 ≤ ε) (i k : Fin (m+1))
    (t : ℕ) (ht : 1 ≤ t ∧ t ≤ n) :
    Setup.radius (zeroLearner n) (baseData ε) i k t ht = spaced ε i := by
  simp [Setup.radius, Setup.pairPrediction, zeroLearner, baseData,
    abs_of_nonneg (le_of_lt (spaced_pos ε hε i)), OrderStatistics.stat_const]

lemma base_upper (ε : ℝ) (hε : 0 ≤ ε) (i : Fin (m+1)) (j : Fin n)
    (t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    Setup.upperEndpoint (zeroLearner n) (baseData ε) i j t ell ht he =
      spaced ε (i.succAbove (Setup.upperIndex m ell he)) := by
  unfold Setup.upperEndpoint
  simp_rw [base_radius ε hε]
  simp only [Setup.pairPrediction, zeroLearner, zero_add]
  apply stat_self_of_monotone
  exact (spaced_mono ε hε).comp (Fin.strictMono_succAbove i).monotone

lemma base_lower (ε : ℝ) (hε : 0 ≤ ε) (i : Fin (m+1)) (j : Fin n)
    (t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    Setup.lowerEndpoint (zeroLearner n) (baseData ε) i j t ell ht he =
      -spaced ε (i.succAbove (Setup.upperIndex m ell he)) := by
  unfold Setup.lowerEndpoint
  simp_rw [base_radius ε hε]
  simp only [Setup.pairPrediction, zeroLearner, zero_sub]
  rw [Stability.stat_neg]
  have hrev : (Setup.lowerIndex m ell he).rev = Setup.upperIndex m ell he := by
    apply Fin.ext
    simp only [Fin.val_rev, Setup.lowerIndex, Setup.upperIndex]
    omega
  rw [hrev]
  congr 1
  apply stat_self_of_monotone
  exact (spaced_mono ε hε).comp (Fin.strictMono_succAbove i).monotone

lemma base_coordinate_miss (ε : ℝ) (hε : 0 ≤ ε) (i : Fin (m+1)) (j : Fin n)
    (t ell : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    ¬ (Setup.lowerEndpoint (zeroLearner n) (baseData ε) i j t ell ht he-2*ε ≤
      (baseData ε i j).2 ∧ (baseData ε i j).2 ≤
      Setup.upperEndpoint (zeroLearner n) (baseData ε) i j t ell ht he+2*ε) ↔
      m+1-ell ≤ i.val := by
  rw [base_lower ε hε, base_upper ε hε]
  change ¬ (-spaced ε (i.succAbove (Setup.upperIndex m ell he))-2*ε ≤ spaced ε i ∧
    spaced ε i ≤ spaced ε (i.succAbove (Setup.upperIndex m ell he))+2*ε) ↔ _
  have hlo : -spaced ε (i.succAbove (Setup.upperIndex m ell he))-2*ε ≤ spaced ε i := by
    have h1 := spaced_pos ε hε i
    have h2 := spaced_pos ε hε (i.succAbove (Setup.upperIndex m ell he))
    linarith
  simp only [hlo, true_and, not_le, spaced_gap ε hε, Fin.succAbove_lt_iff_castSucc_lt]
  change m-ell < i.val ↔ m+1-ell ≤ i.val
  omega

lemma base_failure_iff (ε : ℝ) (hε : 0 ≤ ε) (i : Fin (m+1))
    (F t ell : ℕ) (hF : 1 ≤ F) (hFn : F ≤ n)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    learnerExpandedFailure (zeroLearner n) (baseData ε) ε i F t ell ht he ↔
      m+1-ell ≤ i.val := by
  unfold learnerExpandedFailure
  simp_rw [base_coordinate_miss ε hε]
  by_cases hi : m+1-ell ≤ i.val
  · simp [hi, hFn]
  · simp [hi, show F ≠ 0 by omega]

lemma base_failure_count (ε : ℝ) (hε : 0 ≤ ε) (F t ell : ℕ)
    (hF : 1 ≤ F) (hFn : F ≤ n) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    (univ.filter fun i => learnerExpandedFailure (zeroLearner n) (baseData ε) ε i
      F t ell ht he).card = ell := by
  simp_rw [base_failure_iff ε hε _ F t ell hF hFn ht he]
  have hs : (univ.filter fun i : Fin (m+1) => m+1-ell ≤ i.val) =
      Finset.Ici (⟨m+1-ell, by omega⟩ : Fin (m+1)) := by
    ext i
    simp [Fin.le_def]
  rw [hs, Fin.card_Ici]
  change m+1-(m+1-ell) = ell
  omega

/-- An actual measurable constant learner and finite exchangeable permutation
law attain ell/N, and stability holds for every possible sample. -/
theorem stable_attaining_model (m n : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (F t ell : ℕ)
    (hF : 1 ≤ F) (hFn : F ≤ n) (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    ∃ (A : Learner UniversalCovariate n)
      (Z : Fin (m+1) → Block UniversalCovariate n),
      (∀ W : Fin (m+1) → Block UniversalCovariate n, onSampleDeletionStable A W ε) ∧
      (FiniteExchangeable.blockPermutationLaw Z).real
        {W | learnerExpandedFailure A W ε (Fin.last m) F t ell ht he} =
          (ell : ℝ)/(m+1 : ℕ) := by
  refine ⟨zeroLearner n, baseData ε, zero_stable ε hε, ?_⟩
  have hp := FiniteExchangeable.blockPermutationLaw_equivariant_probability (baseData ε)
    (fun W i => learnerExpandedFailure (zeroLearner n) W ε i F t ell ht he)
    (fun i => measurableSet_learnerExpandedFailure (zeroLearner n) ε i F t ell ht he)
    (learnerExpandedFailure_equivariant (zeroLearner n) ε F t ell ht he) (Fin.last m)
  simpa only [base_failure_count ε hε F t ell hF hFn ht he, Fintype.card_fin] using hp

/-- Actual stable-class minimax problem for positive finite ranks. -/
def stableFiniteRankGamma (m n F t ell : ℕ) (ε : ℝ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) : ℝ :=
  sSup {r : ℝ | ∃ (A : Learner UniversalCovariate n)
    (μ : Measure (Fin (m+1) → Block UniversalCovariate n)),
    IsProbabilityMeasure μ ∧ Exchangeable μ ∧
    μ.real {Z | onSampleDeletionStable A Z ε} = 1 ∧
    r = μ.real {Z | learnerExpandedFailure A Z ε (Fin.last m) F t ell ht he}}

/-- Stable finite-rank law (6.30), positive branch t≤F, as an actual
supremum over measurable learners and exchangeable block probability laws. -/
theorem stableFiniteRankGamma_eq (m n F t ell : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hF : 1 ≤ F) (hFn : F ≤ n) (ht : 1 ≤ t ∧ t ≤ n)
    (he : 1 ≤ ell ∧ ell ≤ m) (htF : t ≤ F) :
    stableFiniteRankGamma m n F t ell ε ht he = (ell : ℝ)/(m+1 : ℕ) := by
  obtain ⟨A, Z, hall, hp⟩ := stable_attaining_model m n ε hε F t ell hF hFn ht he
  let μ := FiniteExchangeable.blockPermutationLaw Z
  have hprob : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  letI : IsProbabilityMeasure μ := hprob
  have hstable : μ.real {W | onSampleDeletionStable A W ε} = 1 := by
    have hs : {W : Fin (m+1) → Block UniversalCovariate n |
        onSampleDeletionStable A W ε} = Set.univ := by
      ext W
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact hall W
    rw [hs]
    exact measureReal_univ_eq_one
  have hmem : (ell : ℝ)/(m+1 : ℕ) ∈
      {r : ℝ | ∃ (A : Learner UniversalCovariate n)
        (ν : Measure (Fin (m+1) → Block UniversalCovariate n)),
        IsProbabilityMeasure ν ∧ Exchangeable ν ∧
        ν.real {W | onSampleDeletionStable A W ε} = 1 ∧
        r = ν.real {W | learnerExpandedFailure A W ε (Fin.last m) F t ell ht he}} :=
    ⟨A, μ, hprob, FiniteExchangeable.blockPermutationLaw_exchangeable Z, hstable, hp.symm⟩
  have hbound : ∀ r ∈ {r : ℝ | ∃ (A : Learner UniversalCovariate n)
        (ν : Measure (Fin (m+1) → Block UniversalCovariate n)),
        IsProbabilityMeasure ν ∧ Exchangeable ν ∧
        ν.real {W | onSampleDeletionStable A W ε} = 1 ∧
        r = ν.real {W | learnerExpandedFailure A W ε (Fin.last m) F t ell ht he}},
      r ≤ (ell : ℝ)/(m+1 : ℕ) := by
    intro r hr
    obtain ⟨B, ν, hν, hex, hs, rfl⟩ := hr
    letI : IsProbabilityMeasure ν := hν
    exact expanded_failure_probability_le_stable B ν hex ε hε F t ell ht he htF hs (Fin.last m)
  unfold stableFiniteRankGamma
  exact le_antisymm (csSup_le ⟨_, hmem⟩ hbound) (le_csSup ⟨_, hbound⟩ hmem)

end
end MEJF.StabilitySharpness
