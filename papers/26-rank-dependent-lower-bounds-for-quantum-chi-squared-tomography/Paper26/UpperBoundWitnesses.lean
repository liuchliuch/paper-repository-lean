import Paper26.StagePolicy
import Paper26.OperatorMeasureConstruction

/-! Uniform upper bounds mean one actual experiment/estimator chosen before
all promised inputs. These definitions retain the original operator models,
arbitrary measurable outcomes and actual consumed natural copy counts. -/
noncomputable section
open scoped ENNReal
open MeasureTheory

namespace Paper26.UpperBoundWitnesses
open QuantumModel CollectiveModel ContinuousPOVM
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def Collective (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε q : ℝ≥0∞) (b : ℝ) : Prop :=
  ∃ (N : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω),
    (N : ℝ) ≤ b ∧
      (letI := mΩ
       ∃ A : OperatorPOVMTransport.OperatorLearner ι Ω N, A.LearnsRank loss r ε q)

def Adaptive (RN : SourceCopyComplexity.AllFixedOperatorRN ι)
    (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε q : ℝ≥0∞) (b : ℝ) : Prop :=
  ∃ (N : ℕ) (Seed Ω : Type) (mSeed : MeasurableSpace Seed) (mΩ : MeasurableSpace Ω),
    (N : ℝ) ≤ b ∧
      (letI := mSeed
       letI := mΩ
       ∃ A : AdaptiveOperatorModelTransport.OperatorLearner ι Seed Ω N,
         A.LearnsRank (RN Ω mΩ) loss r ε q)

theorem collective_of_learner {Ω : Type} [MeasurableSpace Ω] {N : ℕ}
    (A : Learner ι Ω N) (loss : Density ι → Density ι → ℝ≥0∞)
    (r : ℕ) (ε q : ℝ≥0∞) {b : ℝ} (hcost : (N : ℝ) ≤ b)
    (hA : A.LearnsRank loss r ε q) : Collective loss r ε q b := by
  exact ⟨N,Ω,inferInstance,hcost,OperatorMeasureConstruction.toOperatorLearner A,
    (OperatorMeasureConstruction.toOperatorLearner_learnsRank_iff A loss r ε q).mpr hA⟩

theorem collective_of_operator {Ω : Type} [MeasurableSpace Ω] {N : ℕ}
    (A : OperatorPOVMTransport.OperatorLearner ι Ω N)
    (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε q : ℝ≥0∞)
    {b : ℝ} (hcost : (N : ℝ) ≤ b) (hA : A.LearnsRank loss r ε q) : Collective loss r ε q b :=
  ⟨N,Ω,inferInstance,hcost,A,hA⟩

theorem adaptive_of_learner [Nonempty ι] {Seed Ω : Type}
    [MeasurableSpace Seed] [MeasurableSpace Ω] {N : ℕ}
    (RN : SourceCopyComplexity.AllFixedOperatorRN ι) (A : AdaptiveModel.Learner ι Seed Ω N)
    (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε q : ℝ≥0∞)
    {b : ℝ} (hcost : (N : ℝ) ≤ b) (hA : A.LearnsRank loss r ε q) : Adaptive RN loss r ε q b := by
  exact ⟨N,Seed,Ω,inferInstance,inferInstance,hcost,StagePolicy.operatorLearner A,
    (StagePolicy.operatorLearner_learnsRank_iff A (RN Ω inferInstance) loss r ε q).mpr hA⟩

theorem adaptive_of_operator {Seed Ω : Type} [MeasurableSpace Seed] [MeasurableSpace Ω] {N : ℕ}
    (RN : SourceCopyComplexity.AllFixedOperatorRN ι)
    (A : AdaptiveOperatorModelTransport.OperatorLearner ι Seed Ω N)
    (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε q : ℝ≥0∞)
    {b : ℝ} (hcost : (N : ℝ) ≤ b) (hA : A.LearnsRank (RN Ω inferInstance) loss r ε q) :
    Adaptive RN loss r ε q b := ⟨N,Seed,Ω,inferInstance,inferInstance,hcost,A,hA⟩

theorem collective_weaken {loss : Density ι → Density ι → ℝ≥0∞} {r s : ℕ}
    {ε q q' : ℝ≥0∞} {b b' : ℝ} (h : Collective loss r ε q b)
    (hrs : s ≤ r) (hq : q' ≤ q) (hb : b ≤ b') : Collective loss s ε q' b' := by
  obtain ⟨N,Ω,mΩ,hcost,A,hA⟩ := h
  letI := mΩ
  exact ⟨N,Ω,mΩ,hcost.trans hb,A,fun ρ hr => ⟨(hA ρ (hr.trans hrs)).1,
    hq.trans (hA ρ (hr.trans hrs)).2⟩⟩

theorem adaptive_weaken {RN : SourceCopyComplexity.AllFixedOperatorRN ι}
    {loss : Density ι → Density ι → ℝ≥0∞} {r s : ℕ} {ε q q' : ℝ≥0∞} {b b' : ℝ}
    (h : Adaptive RN loss r ε q b) (hrs : s ≤ r) (hq : q' ≤ q) (hb : b ≤ b') :
    Adaptive RN loss s ε q' b' := by
  obtain ⟨N,Seed,Ω,mSeed,mΩ,hcost,A,hA⟩ := h
  letI := mSeed
  letI := mΩ
  exact ⟨N,Seed,Ω,mSeed,mΩ,hcost.trans hb,A,fun ρ hr => ⟨(hA ρ (hr.trans hrs)).1,
    hq.trans (hA ρ (hr.trans hrs)).2⟩⟩

theorem Ncoll_le {loss : Density ι → Density ι → ℝ≥0∞} {r : ℕ} {ε : ℝ≥0∞} {b : ℝ}
    (h : Collective loss r ε ((2 : ℝ≥0∞)/3) b) : CopyComplexity.Ncoll loss r ε ≤ ENNReal.ofReal b := by
  obtain ⟨N,Ω,mΩ,hcost,A,hA⟩ := h
  apply (CopyComplexity.minimumCopies_le (show CopyComplexity.collectiveAchievable loss r ε N from
    ⟨Ω,mΩ,A,hA⟩)).trans
  simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hcost

theorem Nonecopy_le {RN : SourceCopyComplexity.AllFixedOperatorRN ι}
    {loss : Density ι → Density ι → ℝ≥0∞} {r : ℕ} {ε : ℝ≥0∞} {b : ℝ}
    (h : Adaptive RN loss r ε ((2 : ℝ≥0∞)/3) b) :
    SourceCopyComplexity.Nonecopy RN loss r ε ≤ ENNReal.ofReal b := by
  obtain ⟨N,Seed,Ω,mSeed,mΩ,hcost,A,hA⟩ := h
  apply (CopyComplexity.minimumCopies_le (show SourceCopyComplexity.adaptiveAchievable RN loss r ε N from
    ⟨Seed,Ω,mSeed,mΩ,A,hA⟩)).trans
  simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hcost

end Paper26.UpperBoundWitnesses
