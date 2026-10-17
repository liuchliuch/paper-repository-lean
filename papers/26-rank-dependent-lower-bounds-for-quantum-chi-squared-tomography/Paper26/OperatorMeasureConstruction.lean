import Paper26.OperatorPOVMTransport
import Paper26.AdaptiveCollectiveEmbedding
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-! Every actual dominated POVM defines an operator-valued POVM by set
integration. This reverse direction is native; it uses no RN existence input. -/
noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal
open MeasureTheory

namespace Paper26.OperatorMeasureConstruction
open QuantumModel ContinuousPOVM CollectiveModel OperatorPOVMTransport
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]

omit [DecidableEq ι] in
/-- Positivity is preserved by a finite Bochner matrix integral. -/
theorem integral_posSemidef {μ : Measure Ω} [IsFiniteMeasure μ]
    (F : Ω → Matrix ι ι ℂ) (hi : ∀ i j, Integrable (fun y => F y i j) μ)
    (hp : ∀ᵐ y ∂μ, (F y).PosSemidef) :
    (show Matrix ι ι ℂ from fun i j => ∫ y, F y i j ∂μ).PosSemidef := by
  by_cases hμ : μ = 0
  · have he : (show Matrix ι ι ℂ from fun i j => ∫ y, F y i j ∂μ) = 0 := by
      ext i j
      simp [hμ]
    rw [he]
    exact Matrix.PosSemidef.zero
  letI : NeZero μ := ⟨hμ⟩
  letI : NormedAddCommGroup (Matrix ι ι ℂ) :=
    inferInstanceAs (NormedAddCommGroup (ι → ι → ℂ))
  letI : NormedSpace ℝ (Matrix ι ι ℂ) :=
    inferInstanceAs (NormedSpace ℝ (ι → ι → ℂ))
  have hint : Integrable (fun y => (F y : ι → ι → ℂ)) μ :=
    Integrable.of_eval fun i => Integrable.of_eval fun j => hi i j
  have hc : Convex ℝ {E : Matrix ι ι ℂ | E.PosSemidef} := by
    intro E hE G hG a b ha hb _
    exact (hE.smul ha).add (hG.smul hb)
  have havg := hc.average_mem (AdaptiveCollectiveEmbedding.isClosed_setOf_posSemidef (ι := ι)) hp hint
  have hmean := havg.smul (measureReal_nonneg (μ := μ) (s := Set.univ))
  rw [measure_smul_average] at hmean
  have he : (∫ y, F y ∂μ) = fun i j => ∫ y, F y i j ∂μ := by
    funext i j
    rw [eval_integral (fun i => hint.eval i), eval_integral (fun j => (hint.eval i).eval j)]
  rwa [he] at hmean

/-- The set integral of the actual POVM density. -/
def toOperatorPOVM (M : DominatedPOVM ι Ω) : OperatorPOVM ι Ω where
  operator S i j := ∫ y in S, M.effect y i j ∂M.reference
  empty := by ext i j; simp
  positive S _ := integral_posSemidef M.effect
    (fun i j => (M.entry_integrable i j).integrableOn) (ae_restrict_of_ae M.positive_ae)
  total := by ext i j; simp only [Measure.restrict_univ]; exact M.total i j
  countable_additivity S hS hdisjoint i j :=
    hasSum_integral_iUnion hS hdisjoint (M.entry_integrable i j).integrableOn

theorem represents (M : DominatedPOVM ι Ω) : Represents (toOperatorPOVM M) M := by
  intro S hS i j
  rfl

variable {n : ℕ}

/-- The same actual collective learner, expressed as an operator POVM. -/
def toOperatorLearner (A : Learner ι Ω n) : OperatorLearner ι Ω n where
  measurement := toOperatorPOVM A.measurement
  estimator := A.estimator

theorem toOperatorLearner_successProbability (A : Learner ι Ω n)
    (loss : Density ι → Density ι → ℝ≥0∞) (ρ : Density ι) (ε : ℝ≥0∞)
    (hs : MeasurableSet (A.successSet loss ρ ε)) :
    (toOperatorLearner A).successProbability loss ρ ε = A.successProbability loss ρ ε := by
  exact ((toOperatorLearner A).representedLearner_successProbability A.measurement
    (represents A.measurement) loss ρ ε hs).symm

theorem toOperatorLearner_learnsRank_iff (A : Learner ι Ω n)
    (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε q : ℝ≥0∞) :
    (toOperatorLearner A).LearnsRank loss r ε q ↔ A.LearnsRank loss r ε q := by
  exact ((toOperatorLearner A).representedLearner_learnsRank_iff A.measurement
    (represents A.measurement) loss r ε q).symm

end Paper26.OperatorMeasureConstruction
