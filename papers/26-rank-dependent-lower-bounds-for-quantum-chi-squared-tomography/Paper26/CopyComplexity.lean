import Paper26.OperatorPOVMTransport
import Paper26.AdaptiveCoordinateTransport

/-! Definition 1.1's minimum copy counts, with explicit infimum probability
and existence over measurable experiment/estimator data. If no learner exists,
the minimum is infinity. No statistical theorem is built into these definitions.
The adaptive minimum uses the existing joint dominated representation; the
transport of a completely general operator-valued adaptive protocol is separate.
-/
noncomputable section
open scoped ENNReal
open MeasureTheory
attribute [local instance] Classical.propDecidable

namespace Paper26.CopyComplexity
open QuantumModel OperatorPOVMTransport
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Minimum of the achievable natural copy counts, as an extended real. -/
def minimumCopies (achievable : ℕ → Prop) : ℝ≥0∞ :=
  ⨅ n : ℕ, if achievable n then (n : ℝ≥0∞) else ∞

theorem minimumCopies_le {achievable : ℕ → Prop} {n : ℕ} (hn : achievable n) :
    minimumCopies achievable ≤ (n : ℝ≥0∞) := by
  apply iInf_le_of_le n
  simp [hn]

theorem le_minimumCopies {achievable : ℕ → Prop} {b : ℝ≥0∞}
    (h : ∀ n, achievable n → b ≤ (n : ℝ≥0∞)) : b ≤ minimumCopies achievable := by
  apply le_iInf
  intro n
  split_ifs with hn
  · exact h n hn
  · exact le_top

/-- Whenever any finite learner exists, the infimum is the actual least
achievable natural copy count. -/
theorem minimumCopies_eq_find {achievable : ℕ → Prop} [DecidablePred achievable]
    (h : ∃ n, achievable n) : minimumCopies achievable = (Nat.find h : ℝ≥0∞) := by
  apply le_antisymm (minimumCopies_le (Nat.find_spec h))
  apply le_minimumCopies
  intro n hn
  exact_mod_cast Nat.find_min' h hn

/-- All measurable outcome spaces and unrestricted estimators are quantified
before the learner's uniform success property. -/
def collectiveAchievable (loss : Density ι → Density ι → ℝ≥0∞)
    (r : ℕ) (ε : ℝ≥0∞) (n : ℕ) : Prop :=
  ∃ (Ω : Type) (mΩ : MeasurableSpace Ω),
    letI := mΩ
    ∃ A : OperatorLearner ι Ω n, A.LearnsRank loss r ε ((2 : ℝ≥0∞) / 3)

/-- Every consumed fresh copy, including rejected measurements, is one of
exactly n stages in the actual adaptive protocol. -/
def adaptiveAchievable (loss : Density ι → Density ι → ℝ≥0∞)
    (r : ℕ) (ε : ℝ≥0∞) (n : ℕ) : Prop :=
  ∃ (Seed Ω : Type) (mSeed : MeasurableSpace Seed) (mΩ : MeasurableSpace Ω),
    letI := mSeed
    letI := mΩ
    ∃ A : AdaptiveModel.Learner ι Seed Ω n, A.LearnsRank loss r ε ((2 : ℝ≥0∞) / 3)

/-- The paper's collective minimum, with infinity if no finite learner exists. -/
def Ncoll (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε : ℝ≥0∞) : ℝ≥0∞ :=
  minimumCopies (collectiveAchievable loss r ε)

/-- The paper's one-copy minimum in the jointly measurable dominated model. -/
def Nonecopy (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε : ℝ≥0∞) : ℝ≥0∞ :=
  minimumCopies (adaptiveAchievable loss r ε)

/-- A bound for every actual operator learner is a bound on the true minimum. -/
theorem collective_lower_of_all_learners (loss : Density ι → Density ι → ℝ≥0∞)
    (r : ℕ) (ε b : ℝ≥0∞)
    (h : ∀ (n : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω),
      letI := mΩ
      ∀ A : OperatorLearner ι Ω n,
        A.LearnsRank loss r ε ((2 : ℝ≥0∞) / 3) → b ≤ (n : ℝ≥0∞)) :
    b ≤ Ncoll loss r ε := by
  apply le_minimumCopies
  rintro n ⟨Ω, mΩ, A, hA⟩
  exact h n Ω mΩ A hA

theorem adaptive_lower_of_all_learners (loss : Density ι → Density ι → ℝ≥0∞)
    (r : ℕ) (ε b : ℝ≥0∞)
    (h : ∀ (n : ℕ) (Seed Ω : Type) (mSeed : MeasurableSpace Seed) (mΩ : MeasurableSpace Ω),
      letI := mSeed
      letI := mΩ
      ∀ A : AdaptiveModel.Learner ι Seed Ω n,
        A.LearnsRank loss r ε ((2 : ℝ≥0∞) / 3) → b ≤ (n : ℝ≥0∞)) :
    b ≤ Nonecopy loss r ε := by
  apply le_minimumCopies
  rintro n ⟨Seed, Ω, mSeed, mΩ, A, hA⟩
  exact h n Seed Ω mSeed mΩ A hA

/-- Equation (6)'s infimum over the rank-promised family is exactly the
pointwise uniform success condition, retaining the measurable-event clause. -/
theorem operator_learnsRank_iff_inf {Ω : Type} [MeasurableSpace Ω] {n : ℕ}
    (A : OperatorLearner ι Ω n) (loss : Density ι → Density ι → ℝ≥0∞)
    (r : ℕ) (ε q : ℝ≥0∞) : A.LearnsRank loss r ε q ↔
      (∀ ρ : Density ι, ρ.matrix.rank ≤ r → MeasurableSet (A.successSet loss ρ ε)) ∧
      q ≤ ⨅ ρ : {ρ : Density ι // ρ.matrix.rank ≤ r}, A.successProbability loss ρ.1 ε := by
  constructor
  · intro h
    refine ⟨fun ρ hr => (h ρ hr).1, le_iInf fun ρ => (h ρ.1 ρ.2).2⟩
  · rintro ⟨hm, hp⟩ ρ hr
    exact ⟨hm ρ hr, hp.trans (iInf_le (fun η : {ρ : Density ι // ρ.matrix.rank ≤ r} =>
      A.successProbability loss η.1 ε) (⟨ρ, hr⟩ : {ρ : Density ι // ρ.matrix.rank ≤ r}))⟩

end Paper26.CopyComplexity
