import MEJF.StabilityCompleteFailure
import MEJF.ExtendedRule

/-! The expanded rule on the full rank range, using actual EReal endpoints.
The infinite endpoints at rank zero are computed, not encoded as a Gamma law. -/
namespace MEJF.StabilityExtended
open MeasureTheory Setup Stability StabilitySharpness Exchangeability Finset
noncomputable section
attribute [local instance] Classical.propDecidable

variable {X : Type*} [MeasurableSpace X] {m n : ℕ}

def covered (A : Learner X n) (Z : Fin (m+1) → Block X n) (ε : ℝ)
    (i : Fin (m+1)) (j : Fin n) (t ell : ℕ) : Prop :=
  ((Z i j).2 : EReal) ∈ Set.Icc
    (ExtendedRule.lowerEndpoint A Z i j t ell-(2*ε : ℝ))
    (ExtendedRule.upperEndpoint A Z i j t ell+(2*ε : ℝ))

def failure (A : Learner X n) (Z : Fin (m+1) → Block X n) (ε : ℝ)
    (i : Fin (m+1)) (F t ell : ℕ) : Prop :=
  F ≤ (univ.filter fun j => ¬ covered A Z ε i j t ell).card

lemma covered_finite (A : Learner X n) (Z : Fin (m+1) → Block X n) (ε : ℝ)
    (i : Fin (m+1)) (j : Fin n) (t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    covered A Z ε i j t ell ↔
      Setup.lowerEndpoint A Z i j t ell ht he-2*ε ≤ (Z i j).2 ∧
        (Z i j).2 ≤ Setup.upperEndpoint A Z i j t ell ht he+2*ε := by
  simp only [covered, ExtendedRule.lowerEndpoint_finite ht he,
    ExtendedRule.upperEndpoint_finite ht he, ← EReal.coe_sub, ← EReal.coe_add,
    Set.mem_Icc, EReal.coe_le_coe_iff]

lemma failure_finite (A : Learner X n) (Z : Fin (m+1) → Block X n) (ε : ℝ)
    (i : Fin (m+1)) (F t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    failure A Z ε i F t ell ↔ learnerExpandedFailure A Z ε i F t ell ht he := by
  simp only [failure, learnerExpandedFailure, covered_finite A Z ε i _ t ell ht he]

lemma covered_zero_rank (A : Learner X n) (Z : Fin (m+1) → Block X n) (ε : ℝ)
    (i : Fin (m+1)) (j : Fin n) (t ell : ℕ) (hell : ell ≤ m)
    (hz : t = 0 ∨ ell = 0) : covered A Z ε i j t ell := by
  rcases hz with rfl | rfl
  · simp only [covered, ExtendedRule.lowerEndpoint_zero_inner A Z i j hell,
      ExtendedRule.upperEndpoint_zero_inner A Z i j hell, Set.mem_Icc,
      EReal.bot_sub, EReal.top_add_coe, bot_le, le_top, and_self]
  · simp only [covered, ExtendedRule.lowerEndpoint_zero_outer,
      ExtendedRule.upperEndpoint_zero_outer, Set.mem_Icc,
      EReal.bot_sub, EReal.top_add_coe, bot_le, le_top, and_self]

lemma no_failure_zero_rank (A : Learner X n) (Z : Fin (m+1) → Block X n) (ε : ℝ)
    (i : Fin (m+1)) (F t ell : ℕ) (hF : 0 < F) (hell : ell ≤ m)
    (hz : t = 0 ∨ ell = 0) : ¬ failure A Z ε i F t ell := by
  have hs : (univ.filter fun j => ¬ covered A Z ε i j t ell) = ∅ := by
    ext j
    simp [covered_zero_rank A Z ε i j t ell hell hz]
  unfold failure
  rw [hs, card_empty]
  omega

def values (m n F t ell : ℕ) (ε : ℝ) : Set ℝ :=
  {r | ∃ (A : Learner UniversalCovariate n)
    (μ : Measure (Fin (m+1) → Block UniversalCovariate n)),
    IsProbabilityMeasure μ ∧ Exchangeable μ ∧
    μ.real {Z | onSampleDeletionStable A Z ε} = 1 ∧
    r = μ.real {Z | failure A Z ε (Fin.last m) F t ell}}

def gamma (m n F t ell : ℕ) (ε : ℝ) : ℝ := sSup (values m n F t ell ε)

lemma gamma_finite (m n F t ell : ℕ) (ε : ℝ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    gamma m n F t ell ε = stableFiniteRankGamma m n F t ell ε ht he := by
  unfold gamma values stableFiniteRankGamma
  congr 1
  ext r
  simp only [failure_finite _ _ _ _ _ _ _ ht he]

/-- Zero inner or outer rank has actual stable-class worst-case failure zero. -/
theorem gamma_zero_rank (m n F t ell : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hF : 0 < F) (hell : ell ≤ m) (hz : t = 0 ∨ ell = 0) :
    gamma m n F t ell ε = 0 := by
  have hnone (A : Learner UniversalCovariate n) :
      {Z : Fin (m+1) → Block UniversalCovariate n |
        failure A Z ε (Fin.last m) F t ell} = ∅ := by
    ext Z
    simp [no_failure_zero_rank A Z ε (Fin.last m) F t ell hF hell hz]
  let A := zeroLearner n
  let Z : Fin (m+1) → Block UniversalCovariate n := baseData ε
  let μ := FiniteExchangeable.blockPermutationLaw Z
  have hprob : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  letI : IsProbabilityMeasure μ := hprob
  have hstable : μ.real {W | onSampleDeletionStable A W ε} = 1 := by
    have hs : {W : Fin (m+1) → Block UniversalCovariate n |
        onSampleDeletionStable A W ε} = Set.univ := by
      ext W
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact zero_stable ε hε W
    rw [hs]
    exact measureReal_univ_eq_one
  have hmem : (0 : ℝ) ∈ values m n F t ell ε := by
    refine ⟨A, μ, hprob, FiniteExchangeable.blockPermutationLaw_exchangeable Z, hstable, ?_⟩
    rw [hnone, measureReal_empty]
  have hbound : ∀ r ∈ values m n F t ell ε, r ≤ 0 := by
    intro r hr
    obtain ⟨B, ν, hν, hex, hs, rfl⟩ := hr
    rw [hnone, measureReal_empty]
  unfold gamma
  exact le_antisymm (csSup_le ⟨_, hmem⟩ hbound) (le_csSup ⟨_, hbound⟩ hmem)

/-- The complete exact stable-class law (6.30), with zero-rank axes computed
using the EReal convention and positive branches proved by actual models. -/
theorem gamma_eq (m n F t ell : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hF : 1 ≤ F) (hFn : F ≤ n) (htn : t ≤ n) (helm : ell ≤ m) :
    gamma m n F t ell ε =
      if t = 0 ∨ ell = 0 then 0 else if F < t then 1 else (ell : ℝ)/(m+1 : ℕ) := by
  by_cases hz : t = 0 ∨ ell = 0
  · rw [if_pos hz]
    exact gamma_zero_rank m n F t ell ε hε hF helm hz
  · rw [if_neg hz, gamma_finite m n F t ell ε ⟨by omega, htn⟩ ⟨by omega, helm⟩]
    by_cases hFt : F < t
    · rw [if_pos hFt]
      exact stableFiniteRankGamma_high_inner m n F t ell ε hε hFt _ _
    · rw [if_neg hFt]
      exact stableFiniteRankGamma_eq m n F t ell ε hε hF hFn _ _ (by omega)

end
end MEJF.StabilityExtended
