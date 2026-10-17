import Paper26.StagePolicy
import Paper26.ProductCollectiveMeasurement

/-! Sequential measurements of fixed-size fresh blocks are genuine collective
measurements on exactly N*L original copies. Stage kernels and first-failure
probabilities retain their actual sequential law after tensor regrouping. -/
noncomputable section
open scoped ENNReal BigOperators
open MeasureTheory

namespace Paper26.CollectiveBlockProtocol
open QuantumModel ContinuousPOVM CollectiveModel AdaptiveModel
open ProductCollectiveMeasurement
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {Seed Ω : Type} [MeasurableSpace Seed] [MeasurableSpace Ω] {N L : ℕ}

def measurement (A : AdaptiveModel.Learner (Fin N → ι) Seed Ω L) :
    DominatedPOVM (Fin (N*L) → ι) (History Seed Ω L) :=
  CoordinateTransport.povm (batchEquiv N L)
    (AdaptiveCollectiveEmbedding.prefixMeasurement A L (Nat.le_refl L))

theorem measurement_outcomeMeasure (A : AdaptiveModel.Learner (Fin N → ι) Seed Ω L)
    (ρ : Density ι) :
    (measurement A).outcomeMeasure (TensorCopies.density ρ (N*L)) =
      A.transcriptLaw (TensorCopies.density ρ N) := by
  rw [← batch_density ρ N L]
  unfold measurement
  rw [povm_outcomeMeasure]
  exact AdaptiveCollectiveEmbedding.prefixMeasurement_outcomeMeasure A
    (TensorCopies.density ρ N) L (Nat.le_refl L)

/-- The final output is a density on the original ambient space; it need
not be a density on the auxiliary block-copy Hilbert space. -/
def learner (A : AdaptiveModel.Learner (Fin N → ι) Seed Ω L)
    (T : Estimator ι (History Seed Ω L)) : Learner ι (History Seed Ω L) (N*L) :=
  ⟨measurement A, T⟩

theorem learner_outcomeMeasure (A : AdaptiveModel.Learner (Fin N → ι) Seed Ω L)
    (T : Estimator ι (History Seed Ω L)) (ρ : Density ι) :
    (learner A T).outcomeMeasure ρ = A.transcriptLaw (TensorCopies.density ρ N) :=
  measurement_outcomeMeasure A ρ

theorem learner_successProbability (A : AdaptiveModel.Learner (Fin N → ι) Seed Ω L)
    (T : Estimator ι (History Seed Ω L)) (loss : Density ι → Density ι → ℝ≥0∞)
    (ρ : Density ι) (ε : ℝ≥0∞) :
    (learner A T).successProbability loss ρ ε =
      A.transcriptLaw (TensorCopies.density ρ N) {z | loss ρ (T.estimate z) ≤ ε} := by
  unfold CollectiveModel.Learner.successProbability
  rw [learner_outcomeMeasure]
  rfl

/-- A conditional bound only on previously successful histories suffices.
The copy count is N*L, while the failure sum has exactly L block stages. -/
theorem success_of_conditional_stages
    (A : AdaptiveModel.Learner (Fin N → ι) Seed Ω L)
    (T : Estimator ι (History Seed Ω L)) (loss : Density ι → Density ι → ℝ≥0∞)
    (ρ : Density ι) (ε : ℝ≥0∞)
    (good : ∀ k : ℕ, Set (History Seed Ω (k+1)))
    (hg : ∀ k, MeasurableSet (good k)) (δ : ℕ → ℝ≥0∞)
    (hc : ∀ k (hk : k<L) h, h ∈ StagePolicy.goodPrefix good k →
      (A.step ⟨k, hk⟩).bornKernel (TensorCopies.density ρ N) h {y | (h,y) ∉ good k} ≤ δ k)
    (hfinal : ∀ z ∈ StagePolicy.goodPrefix good L, loss ρ (T.estimate z) ≤ ε) :
    1-(∑ j ∈ Finset.range L, δ j) ≤ (learner A T).successProbability loss ρ ε := by
  rw [learner_successProbability]
  apply (StagePolicy.learner_allGood_probability_ge A (TensorCopies.density ρ N) good hg δ hc).trans
  exact measure_mono hfinal

section SourceMinimum
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem collectiveAchievable (A : AdaptiveModel.Learner (Fin N → ι) Seed Ω L)
    (T : Estimator ι (History Seed Ω L)) (loss : Density ι → Density ι → ℝ≥0∞)
    (r : ℕ) (ε : ℝ≥0∞)
    (h : (learner A T).LearnsRank loss r ε ((2 : ℝ≥0∞)/3)) :
    CopyComplexity.collectiveAchievable loss r ε (N*L) := by
  refine ⟨History Seed Ω L, inferInstance, OperatorMeasureConstruction.toOperatorLearner (learner A T), ?_⟩
  exact (OperatorMeasureConstruction.toOperatorLearner_learnsRank_iff (learner A T) loss r ε _).mpr h

theorem Ncoll_le (A : AdaptiveModel.Learner (Fin N → ι) Seed Ω L)
    (T : Estimator ι (History Seed Ω L)) (loss : Density ι → Density ι → ℝ≥0∞)
    (r : ℕ) (ε : ℝ≥0∞)
    (h : (learner A T).LearnsRank loss r ε ((2 : ℝ≥0∞)/3)) :
    CopyComplexity.Ncoll loss r ε ≤ ((N*L : ℕ) : ℝ≥0∞) :=
  CopyComplexity.minimumCopies_le (collectiveAchievable A T loss r ε h)

end SourceMinimum
end Paper26.CollectiveBlockProtocol
