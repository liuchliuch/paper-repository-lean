import Paper26.ContinuousPOVM
import Paper26.TensorCopies

/-!
# Actual collective tomography experiments

A learner measures the actual `n`-fold tensor density of its input with a
dominated POVM on an arbitrary measurable outcome space, then applies a
measurable estimator with unrestricted density-matrix output.  Its outcome
and output laws are actual probability measures, obtained from Born's rule.
Success refers to the actual input matrix rank and actual chi-squared losses.
No success bound or loss-measurability assertion is built into the learner.

The final generic interface isolates the finite-dimensional operator
Radon--Nikodym representation required to pass from arbitrary operator-valued
POVMs to dominated POVMs.  It is an explicit proposition parameter, with no
claimed local witness or externally verified citation in this module, and it
has no statistical success conclusion.
-/

noncomputable section

namespace Paper26.CollectiveModel

open MeasureTheory QuantumModel ContinuousPOVM
open scoped BigOperators ComplexOrder ENNReal

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]

/-- An `n`-copy collective measurement followed by a measurable reconstruction.
Its output may have any rank, regardless of the input rank promise. -/
structure Learner (ι Ω : Type*) [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (n : ℕ) where
  measurement : DominatedPOVM (Fin n → ι) Ω
  estimator : Estimator ι Ω

namespace Learner

variable {n : ℕ} (A : Learner ι Ω n)

/-- The Born density of the actual tensor-copy input. -/
def born (ρ : Density ι) (y : Ω) : ℝ :=
  A.measurement.born (TensorCopies.density ρ n) y

theorem born_eq_trace (ρ : Density ι) (y : Ω) :
    A.born ρ y =
      (Matrix.trace (TensorCopies.matrix ρ.matrix n * A.measurement.effect y)).re := rfl

theorem born_measurable (ρ : Density ι) : Measurable (A.born ρ) :=
  A.measurement.born_measurable _

theorem born_integrable (ρ : Density ι) : Integrable (A.born ρ) A.measurement.reference :=
  A.measurement.born_integrable _

theorem born_nonneg_ae (ρ : Density ι) :
    0 ≤ᵐ[A.measurement.reference] A.born ρ := A.measurement.born_nonneg_ae _

theorem born_integral (ρ : Density ι) :
    ∫ y, A.born ρ y ∂A.measurement.reference = 1 := A.measurement.born_integral _

/-- The law of the measurement outcome on `ρ` tensor `n` times. -/
def outcomeMeasure (ρ : Density ι) : Measure Ω :=
  A.measurement.outcomeMeasure (TensorCopies.density ρ n)

instance outcomeMeasure_isProbabilityMeasure (ρ : Density ι) :
    IsProbabilityMeasure (A.outcomeMeasure ρ) :=
  A.measurement.outcomeMeasure_isProbabilityMeasure _

theorem outcomeMeasure_univ (ρ : Density ι) : A.outcomeMeasure ρ Set.univ = 1 :=
  A.measurement.outcomeMeasure_univ _

theorem outcomeMeasure_apply (ρ : Density ι) {S : Set Ω} (hS : MeasurableSet S) :
    A.outcomeMeasure ρ S =
      ∫⁻ y in S, ENNReal.ofReal (A.born ρ y) ∂A.measurement.reference :=
  A.measurement.outcomeMeasure_apply _ hS

/-- The estimator's actual output law on all density matrices. -/
def outputMeasure (ρ : Density ι) : Measure (Density ι) :=
  (A.outcomeMeasure ρ).map A.estimator.estimate

instance outputMeasure_isProbabilityMeasure (ρ : Density ι) :
    IsProbabilityMeasure (A.outputMeasure ρ) :=
  Measure.isProbabilityMeasure_map A.estimator.measurable_estimate.aemeasurable

theorem outputMeasure_univ (ρ : Density ι) : A.outputMeasure ρ Set.univ = 1 :=
  measure_univ

theorem outputMeasure_apply (ρ : Density ι) {S : Set (Density ι)}
    (hS : MeasurableSet S) :
    A.outputMeasure ρ S = A.outcomeMeasure ρ (A.estimator.estimate ⁻¹' S) :=
  Measure.map_apply A.estimator.measurable_estimate hS

theorem outputMeasure_eq_lintegral (ρ : Density ι) {S : Set (Density ι)}
    (hS : MeasurableSet S) :
    A.outputMeasure ρ S = ∫⁻ y in A.estimator.estimate ⁻¹' S,
      ENNReal.ofReal
        (Matrix.trace (TensorCopies.matrix ρ.matrix n * A.measurement.effect y)).re
          ∂A.measurement.reference := by
  rw [A.outputMeasure_apply ρ hS,
    A.outcomeMeasure_apply ρ (A.estimator.measurable_estimate hS)]
  rfl

/-- The actual successful-outcome event for a loss and divergence accuracy. -/
def successSet (loss : Density ι → Density ι → ℝ≥0∞) (ρ : Density ι)
    (ε : ℝ≥0∞) : Set Ω := {y | loss ρ (A.estimator.estimate y) ≤ ε}

theorem successSet_measurable (loss : Density ι → Density ι → ℝ≥0∞)
    (ρ : Density ι) (hLoss : Measurable (loss ρ)) (ε : ℝ≥0∞) :
    MeasurableSet (A.successSet loss ρ ε) :=
  measurableSet_le (hLoss.comp A.estimator.measurable_estimate) measurable_const

/-- The Born probability of the successful-outcome event.  The accompanying
measurability theorem supplies its event interpretation. -/
def successProbability (loss : Density ι → Density ι → ℝ≥0∞) (ρ : Density ι)
    (ε : ℝ≥0∞) : ℝ≥0∞ := A.outcomeMeasure ρ (A.successSet loss ρ ε)

theorem successProbability_le_one (loss : Density ι → Density ι → ℝ≥0∞)
    (ρ : Density ι) (ε : ℝ≥0∞) : A.successProbability loss ρ ε ≤ 1 := by
  calc
    _ ≤ A.outcomeMeasure ρ Set.univ := measure_mono (Set.subset_univ _)
    _ = 1 := A.outcomeMeasure_univ ρ

theorem successProbability_eq_outputMeasure (loss : Density ι → Density ι → ℝ≥0∞)
    (ρ : Density ι) (hLoss : Measurable (loss ρ)) (ε : ℝ≥0∞) :
    A.successProbability loss ρ ε = A.outputMeasure ρ {σ | loss ρ σ ≤ ε} := by
  rw [A.outputMeasure_apply ρ (measurableSet_le hLoss measurable_const)]
  rfl

theorem successProbability_eq_lintegral (loss : Density ι → Density ι → ℝ≥0∞)
    (ρ : Density ι) (hLoss : Measurable (loss ρ)) (ε : ℝ≥0∞) :
    A.successProbability loss ρ ε = ∫⁻ y in A.successSet loss ρ ε,
      ENNReal.ofReal
        (Matrix.trace (TensorCopies.matrix ρ.matrix n * A.measurement.effect y)).re
          ∂A.measurement.reference := by
  exact A.outcomeMeasure_apply ρ (A.successSet_measurable loss ρ hLoss ε)

/-- Uniform success on actual rank-at-most-`r` input density matrices.
Measurability is part of the requirement.  The output has no rank promise. -/
def LearnsRank (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε q : ℝ≥0∞) : Prop :=
  ∀ ρ : Density ι, ρ.matrix.rank ≤ r →
    MeasurableSet (A.successSet loss ρ ε) ∧ q ≤ A.successProbability loss ρ ε

/-- Definition 1.1's constant-confidence Bures chi-squared success property. -/
def BuresSuccess (r : ℕ) (ε : ℝ≥0∞) : Prop :=
  A.LearnsRank QuantumModel.chiB r ε ((2 : ℝ≥0∞) / 3)

/-- Definition 1.1's constant-confidence right-inverse chi-squared success property. -/
def RightSuccess (r : ℕ) (ε : ℝ≥0∞) : Prop :=
  A.LearnsRank QuantumModel.chiR r ε ((2 : ℝ≥0∞) / 3)

/-- A measurable loss section turns the uniform rank promise into exactly
the Born integrals of its success sets, rather than abstract success scalars. -/
theorem learnsRank_iff_born_integrals (loss : Density ι → Density ι → ℝ≥0∞)
    (r : ℕ) (ε q : ℝ≥0∞)
    (hLoss : ∀ ρ : Density ι, ρ.matrix.rank ≤ r → Measurable (loss ρ)) :
    A.LearnsRank loss r ε q ↔
      ∀ ρ : Density ι, ρ.matrix.rank ≤ r →
        q ≤ ∫⁻ y in A.successSet loss ρ ε,
          ENNReal.ofReal
            (Matrix.trace (TensorCopies.matrix ρ.matrix n * A.measurement.effect y)).re
              ∂A.measurement.reference := by
  constructor
  · intro h ρ hr
    rw [← A.successProbability_eq_lintegral loss ρ (hLoss ρ hr) ε]
    exact (h ρ hr).2
  · intro h ρ hr
    refine ⟨A.successSet_measurable loss ρ (hLoss ρ hr) ε, ?_⟩
    rw [A.successProbability_eq_lintegral loss ρ (hLoss ρ hr) ε]
    exact h ρ hr

end Learner

/-- An operator-valued POVM on the actual finite-dimensional matrix space.
Countable additivity is imposed entrywise on measurable disjoint sequences;
no dominated representation is assumed in this definition. -/
structure OperatorPOVM (ι Ω : Type*) [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] where
  operator : Set Ω → Matrix ι ι ℂ
  empty : operator ∅ = 0
  positive : ∀ S, MeasurableSet S → (operator S).PosSemidef
  total : operator Set.univ = 1
  countable_additivity : ∀ S : ℕ → Set Ω, (∀ k, MeasurableSet (S k)) →
    Pairwise (fun k l => Disjoint (S k) (S l)) → ∀ i j,
      HasSum (fun k => operator (S k) i j) (operator (⋃ k, S k) i j)

/-- Exact generic finite-dimensional operator Radon--Nikodym input.
It asks only for a representation of the given operator-valued measure;
there is no conclusion about learning, rank, loss, volume or Fisher information.
No witness is assumed globally or constructed in this file. -/
structure OperatorRadonNikodymInput (ι Ω : Type*) [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] : Prop where
  representation : ∀ P : OperatorPOVM ι Ω, ∃ M : DominatedPOVM ι Ω,
    (∀ S, MeasurableSet S → ∀ i j,
      P.operator S i j = ∫ y in S, M.effect y i j ∂M.reference) ∧
    (∀ S, MeasurableSet S →
      M.reference S = ENNReal.ofReal (Matrix.trace (P.operator S)).re)

end Paper26.CollectiveModel
