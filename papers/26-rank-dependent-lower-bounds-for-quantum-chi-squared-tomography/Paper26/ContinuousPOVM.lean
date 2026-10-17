import Paper26.QuantumModel
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.SpecialFunctions.RCLike
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Dominated POVMs on arbitrary measurable outcome spaces

A measurement consists of a finite scalar measure and an actual measurable
complex matrix density.  Its entries are integrable, its effects are positive
semidefinite almost everywhere, and their entrywise integrals form the identity.
The Born density is the real part of the actual matrix trace.  Its positivity,
integrability and normalization are proved from these measurement conditions;
the resulting `withDensity` measure is a probability measure.

The output space consists of all density matrices, with the measurable space
induced by their matrix coordinates.  The measurable estimator and success
probabilities below do not impose any output-rank restriction.  They describe
one dominated experiment, without asserting an adaptive transcript model or a
Radon--Nikodym representation theorem for all operator-valued measures.
-/

noncomputable section

namespace Paper26.ContinuousPOVM

open MeasureTheory QuantumModel
open scoped BigOperators ComplexOrder ENNReal

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]

/-- A genuine matrix density for a dominated finite-dimensional POVM.
The outcome sigma-algebra is arbitrary; no countability assumption is imposed. -/
structure DominatedPOVM (ι Ω : Type*) [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] where
  reference : Measure Ω
  reference_finite : IsFiniteMeasure reference
  effect : Ω → Matrix ι ι ℂ
  entry_measurable : ∀ i j, Measurable (fun y => effect y i j)
  positive_ae : ∀ᵐ y ∂reference, (effect y).PosSemidef
  entry_integrable : ∀ i j, Integrable (fun y => effect y i j) reference
  total : ∀ i j, ∫ y, effect y i j ∂reference = (1 : Matrix ι ι ℂ) i j

namespace DominatedPOVM

variable (M : DominatedPOVM ι Ω)

instance reference_isFiniteMeasure : IsFiniteMeasure M.reference := M.reference_finite

/-- The actual complex Born trace, before taking its real part. -/
def complexBorn (ρ : Density ι) (y : Ω) : ℂ :=
  Matrix.trace (ρ.matrix * M.effect y)

/-- The actual scalar Born density relative to the reference measure. -/
def born (ρ : Density ι) (y : Ω) : ℝ := (M.complexBorn ρ y).re

theorem complexBorn_eq_sum (ρ : Density ι) (y : Ω) :
    M.complexBorn ρ y = ∑ i, ∑ j, ρ.matrix i j * M.effect y j i := by
  simp [complexBorn, Matrix.trace, Matrix.mul_apply]

theorem complexBorn_measurable (ρ : Density ι) : Measurable (M.complexBorn ρ) := by
  change Measurable (fun y => ∑ i, ∑ j, ρ.matrix i j * M.effect y j i)
  exact Finset.measurable_sum Finset.univ fun i _ =>
    Finset.measurable_sum Finset.univ fun j _ =>
      (M.entry_measurable j i).const_mul (ρ.matrix i j)

theorem complexBorn_integrable (ρ : Density ι) :
    Integrable (M.complexBorn ρ) M.reference := by
  change Integrable (fun y => ∑ i, ∑ j, ρ.matrix i j * M.effect y j i) M.reference
  exact integrable_finset_sum Finset.univ fun i _ =>
    integrable_finset_sum Finset.univ fun j _ =>
      (M.entry_integrable j i).const_mul (ρ.matrix i j)

theorem complexBorn_integral (ρ : Density ι) :
    ∫ y, M.complexBorn ρ y ∂M.reference = 1 := by
  simp_rw [complexBorn_eq_sum]
  rw [integral_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum Finset.univ (fun j _ =>
      (M.entry_integrable j i).const_mul (ρ.matrix i j)))]
  simp_rw [integral_finset_sum Finset.univ (fun j _ =>
    (M.entry_integrable j _).const_mul (ρ.matrix _ j))]
  simp_rw [integral_const_mul, M.total]
  simpa [Matrix.trace, Matrix.one_apply] using ρ.trace_one

theorem born_measurable (ρ : Density ι) : Measurable (M.born ρ) :=
  (M.complexBorn_measurable ρ).re

theorem born_integrable (ρ : Density ι) : Integrable (M.born ρ) M.reference :=
  (M.complexBorn_integrable ρ).re

/-- A positive effect gives pointwise nonnegativity, independently of null sets. -/
theorem born_nonneg (ρ : Density ι) {y : Ω} (hy : (M.effect y).PosSemidef) :
    0 ≤ M.born ρ y := QuantumModel.trace_mul_effect_nonneg ρ hy

theorem born_nonneg_ae (ρ : Density ι) : 0 ≤ᵐ[M.reference] M.born ρ :=
  M.positive_ae.mono fun _ hy => M.born_nonneg ρ hy

theorem born_integral (ρ : Density ι) : ∫ y, M.born ρ y ∂M.reference = 1 := by
  change (∫ y, (M.complexBorn ρ y).re ∂M.reference) = 1
  calc
    _ = (∫ y, M.complexBorn ρ y ∂M.reference).re := by
      simpa only [RCLike.re_eq_complex_re] using integral_re (M.complexBorn_integrable ρ)
    _ = 1 := by rw [M.complexBorn_integral]; rfl

theorem born_distribution (ρ : Density ι) :
    (0 ≤ᵐ[M.reference] M.born ρ) ∧ Integrable (M.born ρ) M.reference ∧
      ∫ y, M.born ρ y ∂M.reference = 1 :=
  ⟨M.born_nonneg_ae ρ, M.born_integrable ρ, M.born_integral ρ⟩

/-- Born's actual probability measure, including continuous outcomes. -/
def outcomeMeasure (ρ : Density ι) : Measure Ω :=
  M.reference.withDensity (fun y => ENNReal.ofReal (M.born ρ y))

theorem outcomeMeasure_apply (ρ : Density ι) {S : Set Ω} (hS : MeasurableSet S) :
    M.outcomeMeasure ρ S = ∫⁻ y in S, ENNReal.ofReal (M.born ρ y) ∂M.reference :=
  withDensity_apply _ hS

theorem outcomeMeasure_univ (ρ : Density ι) : M.outcomeMeasure ρ Set.univ = 1 := by
  rw [M.outcomeMeasure_apply ρ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (M.born_integrable ρ) (M.born_nonneg_ae ρ),
    M.born_integral, ENNReal.ofReal_one]

instance outcomeMeasure_isProbabilityMeasure (ρ : Density ι) :
    IsProbabilityMeasure (M.outcomeMeasure ρ) := ⟨M.outcomeMeasure_univ ρ⟩

theorem outcomeMeasure_le_one (ρ : Density ι) (S : Set Ω) :
    M.outcomeMeasure ρ S ≤ 1 := by
  calc
    M.outcomeMeasure ρ S ≤ M.outcomeMeasure ρ Set.univ := measure_mono (Set.subset_univ _)
    _ = 1 := M.outcomeMeasure_univ ρ

end DominatedPOVM

local instance matrixMeasurableSpace : MeasurableSpace (Matrix ι ι ℂ) :=
  inferInstanceAs (MeasurableSpace (ι → ι → ℂ))

/-- All density matrices carry the sigma-algebra induced by their actual
complex entries, with no bound on the output rank.  Writing the codomain as
the underlying Pi type avoids depending on a matrix-specific measurable instance. -/
instance densityMeasurableSpace : MeasurableSpace (Density ι) :=
  MeasurableSpace.comap (fun ρ : Density ι => (ρ.matrix : ι → ι → ℂ)) inferInstance

omit [DecidableEq ι] in
theorem measurable_density_matrix :
    Measurable (fun ρ : Density ι => (ρ.matrix : ι → ι → ℂ)) :=
  comap_measurable _

/-- A measurable reconstruction with unrestricted density-matrix output. -/
structure Estimator (ι Ω : Type*) [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω] where
  estimate : Ω → Density ι
  measurable_estimate : Measurable estimate

namespace Estimator

variable (T : Estimator ι Ω) (M : DominatedPOVM ι Ω) (ρ : Density ι)

theorem measurable_matrix : Measurable (fun y => (T.estimate y).matrix : Ω → ι → ι → ℂ) :=
  measurable_density_matrix.comp T.measurable_estimate

/-- The actual distribution of the reconstructed density matrix. -/
def outputMeasure : Measure (Density ι) := (M.outcomeMeasure ρ).map T.estimate

instance outputMeasure_isProbabilityMeasure : IsProbabilityMeasure (T.outputMeasure M ρ) :=
  Measure.isProbabilityMeasure_map T.measurable_estimate.aemeasurable

/-- Success for an output acceptance set, evaluated under the Born law. -/
def successProbability (good : Set (Density ι)) : ℝ≥0∞ :=
  M.outcomeMeasure ρ (T.estimate ⁻¹' good)

theorem successProbability_eq_outputMeasure {good : Set (Density ι)}
    (hgood : MeasurableSet good) :
    T.successProbability M ρ good = T.outputMeasure M ρ good := by
  exact (Measure.map_apply T.measurable_estimate hgood).symm

theorem successProbability_eq_lintegral {good : Set (Density ι)}
    (hgood : MeasurableSet good) :
    T.successProbability M ρ good =
      ∫⁻ y in T.estimate ⁻¹' good, ENNReal.ofReal (M.born ρ y) ∂M.reference :=
  M.outcomeMeasure_apply ρ (T.measurable_estimate hgood)

theorem successProbability_le_one (good : Set (Density ι)) :
    T.successProbability M ρ good ≤ 1 :=
  M.outcomeMeasure_le_one ρ _

/-- The concrete event for any measurable section of a nonnegative loss.
Measurability of a particular spectral loss is a separate obligation. -/
def lossSuccessSet (loss : Density ι → Density ι → ℝ≥0∞) (ε : ℝ≥0∞) : Set Ω :=
  {y | loss ρ (T.estimate y) ≤ ε}

theorem lossSuccessSet_measurable (loss : Density ι → Density ι → ℝ≥0∞)
    (hLoss : Measurable (loss ρ)) (ε : ℝ≥0∞) :
    MeasurableSet (T.lossSuccessSet ρ loss ε) :=
  measurableSet_le (hLoss.comp T.measurable_estimate) measurable_const

end Estimator

end Paper26.ContinuousPOVM
