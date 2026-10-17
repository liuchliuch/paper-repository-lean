import Paper26.ContinuousPOVM
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Actual history-dependent one-copy quantum experiments

Every step specifies a genuine matrix-valued measurement density relative to an
s-finite reference kernel. Its Born kernel is proved Markov from positivity and
the entrywise identity integral. The outcome sigma-algebra is arbitrary. A finite
protocol composes exactly `n` such steps, with a parameter-independent random seed,
and a measurable density-matrix estimator of unrestricted output rank.

This is a dominated, jointly measurable representation of an adaptive protocol.
It does not prove that every family of arbitrary operator-valued POVMs admits a
jointly measurable choice of Radon--Nikodym densities/reference kernels. Positivity
is allowed almost everywhere for each history, so no pointwise PSD repair is
required here. No Fisher bound, score identity, or success lower bound is a field.
-/

noncomputable section

namespace Paper26.AdaptiveModel

open MeasureTheory ProbabilityTheory QuantumModel ContinuousPOVM
open scoped BigOperators ComplexOrder ENNReal

universe u

variable {ι H : Type*} {Ω Seed : Type u} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace H] [MeasurableSpace Ω] [MeasurableSpace Seed]

/-- One copy of the unknown state is measured after observing history `h`.
The reference kernel is independent of the state and need only be s-finite. -/
structure OneCopyStep (ι H Ω : Type*) [Fintype ι] [DecidableEq ι]
    [MeasurableSpace H] [MeasurableSpace Ω] where
  reference : Kernel H Ω
  reference_sfinite : IsSFiniteKernel reference
  effect : H → Ω → Matrix ι ι ℂ
  entry_measurable : ∀ i j, Measurable (fun z : H × Ω => effect z.1 z.2 i j)
  positive_ae : ∀ h, ∀ᵐ y ∂reference h, (effect h y).PosSemidef
  entry_integrable : ∀ h i j, Integrable (fun y => effect h y i j) (reference h)
  total : ∀ h i j, ∫ y, effect h y i j ∂reference h = (1 : Matrix ι ι ℂ) i j

namespace OneCopyStep

variable (M : OneCopyStep ι H Ω)

instance reference_isSFiniteKernel : IsSFiniteKernel M.reference := M.reference_sfinite

/-- The actual single-copy complex Born trace. -/
def complexBorn (ρ : Density ι) (h : H) (y : Ω) : ℂ :=
  Matrix.trace (ρ.matrix * M.effect h y)

/-- The actual single-copy Born density. -/
def born (ρ : Density ι) (h : H) (y : Ω) : ℝ := (M.complexBorn ρ h y).re

theorem complexBorn_eq_sum (ρ : Density ι) (h : H) (y : Ω) :
    M.complexBorn ρ h y = ∑ i, ∑ j, ρ.matrix i j * M.effect h y j i := by
  simp [complexBorn, Matrix.trace, Matrix.mul_apply]

theorem complexBorn_joint_measurable (ρ : Density ι) :
    Measurable (fun z : H × Ω => M.complexBorn ρ z.1 z.2) := by
  change Measurable (fun z : H × Ω => ∑ i, ∑ j, ρ.matrix i j * M.effect z.1 z.2 j i)
  exact Finset.measurable_sum Finset.univ fun i _ =>
    Finset.measurable_sum Finset.univ fun j _ =>
      (M.entry_measurable j i).const_mul (ρ.matrix i j)

theorem born_joint_measurable (ρ : Density ι) :
    Measurable (Function.uncurry (M.born ρ)) :=
  (M.complexBorn_joint_measurable ρ).re

/-- Joint measurability also includes the unknown density-matrix parameter.
It is obtained directly from finitely many actual matrix entries. -/
theorem born_parameter_joint_measurable :
    Measurable (fun z : (Density ι × H) × Ω => M.born z.1.1 z.1.2 z.2) := by
  have hc : Measurable (fun z : (Density ι × H) × Ω =>
      M.complexBorn z.1.1 z.1.2 z.2) := by
    change Measurable (fun z : (Density ι × H) × Ω =>
      ∑ i, ∑ j, z.1.1.matrix i j * M.effect z.1.2 z.2 j i)
    refine Finset.measurable_sum Finset.univ fun i _ =>
      Finset.measurable_sum Finset.univ fun j _ => ?_
    have hρ : Measurable (fun z : (Density ι × H) × Ω => z.1.1.matrix i j) :=
      ((measurable_pi_apply j).comp
        ((measurable_pi_apply i).comp measurable_density_matrix)).comp
          (measurable_fst.comp measurable_fst)
    exact hρ.mul ((M.entry_measurable j i).comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  exact hc.re

theorem born_measurable (ρ : Density ι) (h : H) : Measurable (M.born ρ h) :=
  (M.born_joint_measurable ρ).of_uncurry_left

theorem complexBorn_integrable (ρ : Density ι) (h : H) :
    Integrable (M.complexBorn ρ h) (M.reference h) := by
  change Integrable (fun y => ∑ i, ∑ j, ρ.matrix i j * M.effect h y j i) (M.reference h)
  exact integrable_finset_sum Finset.univ fun i _ =>
    integrable_finset_sum Finset.univ fun j _ =>
      (M.entry_integrable h j i).const_mul (ρ.matrix i j)

theorem complexBorn_integral (ρ : Density ι) (h : H) :
    ∫ y, M.complexBorn ρ h y ∂M.reference h = 1 := by
  simp_rw [complexBorn_eq_sum]
  rw [integral_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum Finset.univ (fun j _ =>
      (M.entry_integrable h j i).const_mul (ρ.matrix i j)))]
  simp_rw [integral_finset_sum Finset.univ (fun j _ =>
    (M.entry_integrable h j _).const_mul (ρ.matrix _ j))]
  simp_rw [integral_const_mul, M.total]
  simpa [Matrix.trace, Matrix.one_apply] using ρ.trace_one

theorem born_integrable (ρ : Density ι) (h : H) :
    Integrable (M.born ρ h) (M.reference h) := (M.complexBorn_integrable ρ h).re

theorem born_nonneg_ae (ρ : Density ι) (h : H) :
    0 ≤ᵐ[M.reference h] M.born ρ h :=
  (M.positive_ae h).mono fun _ hy => QuantumModel.trace_mul_effect_nonneg ρ hy

theorem born_integral (ρ : Density ι) (h : H) :
    ∫ y, M.born ρ h y ∂M.reference h = 1 := by
  change (∫ y, (M.complexBorn ρ h y).re ∂M.reference h) = 1
  calc
    _ = (∫ y, M.complexBorn ρ h y ∂M.reference h).re := by
      simpa only [RCLike.re_eq_complex_re] using integral_re (M.complexBorn_integrable ρ h)
    _ = 1 := by rw [M.complexBorn_integral]; rfl

/-- The Born transition kernel is a construction, not a protocol assumption. -/
def bornKernel (ρ : Density ι) : Kernel H Ω :=
  M.reference.withDensity (fun h y => ENNReal.ofReal (M.born ρ h y))

theorem bornKernel_apply (ρ : Density ι) (h : H) :
    M.bornKernel ρ h = (M.reference h).withDensity
      (fun y => ENNReal.ofReal (M.born ρ h y)) :=
  Kernel.withDensity_apply _ (M.born_joint_measurable ρ).ennreal_ofReal h

theorem bornKernel_apply_set (ρ : Density ι) (h : H) {S : Set Ω}
    (hS : MeasurableSet S) :
    M.bornKernel ρ h S = ∫⁻ y in S, ENNReal.ofReal
      (Matrix.trace (ρ.matrix * M.effect h y)).re ∂M.reference h := by
  rw [M.bornKernel_apply ρ h, withDensity_apply _ hS]
  rfl

theorem bornKernel_univ (ρ : Density ι) (h : H) : M.bornKernel ρ h Set.univ = 1 := by
  rw [M.bornKernel_apply_set ρ h MeasurableSet.univ, Measure.restrict_univ]
  change (∫⁻ y, ENNReal.ofReal (M.born ρ h y) ∂M.reference h) = 1
  rw [← ofReal_integral_eq_lintegral_ofReal (M.born_integrable ρ h)
    (M.born_nonneg_ae ρ h), M.born_integral, ENNReal.ofReal_one]

instance bornKernel_isMarkovKernel (ρ : Density ι) : IsMarkovKernel (M.bornKernel ρ) :=
  ⟨fun h => ⟨M.bornKernel_univ ρ h⟩⟩

theorem bornKernel_lintegral (ρ : Density ι) (h : H) {f : Ω → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ y, f y ∂M.bornKernel ρ h =
      ∫⁻ y, ENNReal.ofReal (M.born ρ h y) * f y ∂M.reference h :=
  Kernel.lintegral_withDensity M.reference (f := fun h y => ENNReal.ofReal (M.born ρ h y))
    (M.born_joint_measurable ρ).ennreal_ofReal h hf

/-- The transition is also an actual kernel jointly in state and history.
This supplies parameter measurability for later Bayesian/Fisher arguments. -/
def parameterBornKernel : Kernel (Density ι × H) Ω :=
  (M.reference.comap Prod.snd measurable_snd).withDensity
    (fun z y => ENNReal.ofReal (M.born z.1 z.2 y))

theorem parameterBornKernel_apply (ρ : Density ι) (h : H) :
    M.parameterBornKernel (ρ, h) = M.bornKernel ρ h := by
  rw [parameterBornKernel, Kernel.withDensity_apply _
    M.born_parameter_joint_measurable.ennreal_ofReal, Kernel.comap_apply]
  exact (M.bornKernel_apply ρ h).symm

instance parameterBornKernel_isMarkovKernel : IsMarkovKernel M.parameterBornKernel := by
  constructor
  intro z
  rw [M.parameterBornKernel_apply z.1 z.2]
  infer_instance

end OneCopyStep

/-- The seed together with exactly `k` successive observed outcomes. -/
def History (Seed Ω : Type u) : ℕ → Type u
  | 0 => Seed
  | k + 1 => History Seed Ω k × Ω

instance historyMeasurableSpace (Seed Ω : Type u) [MeasurableSpace Seed] [MeasurableSpace Ω] :
    (k : ℕ) → MeasurableSpace (History Seed Ω k)
  | 0 => inferInstanceAs (MeasurableSpace Seed)
  | k + 1 => @Prod.instMeasurableSpace (History Seed Ω k) Ω
      (historyMeasurableSpace Seed Ω k) inferInstance

/-- An exactly `n`-copy adaptive experiment. The single fixed seed law is
independent of the unknown density matrix. Each step may depend on the entire
preceding history. Every step's effect acts on the original one-copy space `ι`. -/
structure Learner (ι : Type*) (Seed Ω : Type u) [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Seed] [MeasurableSpace Ω] (n : ℕ) where
  seed : Measure Seed
  seed_probability : IsProbabilityMeasure seed
  step : ∀ k : Fin n, OneCopyStep ι (History Seed Ω k.val) Ω
  estimator : Estimator ι (History Seed Ω n)

namespace Learner

variable {n : ℕ} (A : Learner ι Seed Ω n)

instance seed_isProbabilityMeasure : IsProbabilityMeasure A.seed := A.seed_probability

/-- Sequentially constructed laws of prefixes. Each successor consumes one copy
through the actual Born kernel on the original matrix space. -/
def prefixLaw (ρ : Density ι) : (k : ℕ) → k ≤ n → Measure (History Seed Ω k)
  | 0, _ => A.seed
  | k + 1, hk => (prefixLaw ρ k (Nat.le_trans (Nat.le_succ k) hk)).compProd
      ((A.step ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩).bornKernel ρ)

instance prefixLaw_isProbabilityMeasure (ρ : Density ι) (k : ℕ) (hk : k ≤ n) :
    IsProbabilityMeasure (A.prefixLaw ρ k hk) := by
  induction k with
  | zero => exact A.seed_probability
  | succ k ih =>
      change IsProbabilityMeasure ((A.prefixLaw ρ k
        (Nat.le_trans (Nat.le_succ k) hk)).compProd _)
      letI := ih (Nat.le_trans (Nat.le_succ k) hk)
      infer_instance

theorem prefixLaw_zero (ρ : Density ι) (h0 : 0 ≤ n) :
    A.prefixLaw ρ 0 h0 = A.seed := rfl

/-- Extending the transcript by one observation preserves the previous
history law. This is the actual marginal identity, with no conditional-law
or statistical assumption in its statement. -/
theorem prefixLaw_succ_fst (ρ : Density ι) (k : ℕ) (hk : k + 1 ≤ n) :
    (A.prefixLaw ρ (k + 1) hk).fst =
      A.prefixLaw ρ k (Nat.le_trans (Nat.le_succ k) hk) := by
  change ((A.prefixLaw ρ k (Nat.le_trans (Nat.le_succ k) hk)).compProd
    ((A.step ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩).bornKernel ρ)).fst = _
  exact Measure.fst_compProd _ _

/-- The defining history-dependent Born integral for every next-step event. -/
theorem prefixLaw_succ_apply (ρ : Density ι) (k : ℕ) (hk : k + 1 ≤ n)
    {S : Set (History Seed Ω k × Ω)} (hS : MeasurableSet S) :
    A.prefixLaw ρ (k + 1) hk S =
      ∫⁻ h, ∫⁻ y in Prod.mk h ⁻¹' S, ENNReal.ofReal
        (Matrix.trace (ρ.matrix *
          (A.step ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩).effect h y)).re
          ∂(A.step ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩).reference h
        ∂A.prefixLaw ρ k (Nat.le_trans (Nat.le_succ k) hk) := by
  change ((A.prefixLaw ρ k (Nat.le_trans (Nat.le_succ k) hk)).compProd
    ((A.step ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩).bornKernel ρ)) S = _
  rw [Measure.compProd_apply hS]
  congr 1
  funext h
  exact OneCopyStep.bornKernel_apply_set _ ρ h (measurable_prodMk_left hS)

/-- Iterated expectation with the actual scalar Born factor. This is a direct
interface for a later generic score/Fisher chain rule; none is assumed here. -/
theorem prefixLaw_succ_lintegral (ρ : Density ι) (k : ℕ) (hk : k + 1 ≤ n)
    {f : History Seed Ω k × Ω → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, f z ∂A.prefixLaw ρ (k + 1) hk =
      ∫⁻ h, ∫⁻ y,
        ENNReal.ofReal ((A.step ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩).born ρ h y)
          * f (h, y)
        ∂(A.step ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩).reference h
        ∂A.prefixLaw ρ k (Nat.le_trans (Nat.le_succ k) hk) := by
  change (∫⁻ z : History Seed Ω k × Ω, f z ∂
    (A.prefixLaw ρ k (Nat.le_trans (Nat.le_succ k) hk)).compProd
      ((A.step ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩).bornKernel ρ)) = _
  rw [Measure.lintegral_compProd hf]
  congr 1
  funext h
  exact OneCopyStep.bornKernel_lintegral _ ρ h (hf.comp measurable_prodMk_left)

/-- Actual full transcript law, after exactly `n` one-copy measurement steps. -/
def transcriptLaw (ρ : Density ι) : Measure (History Seed Ω n) :=
  A.prefixLaw ρ n (Nat.le_refl n)

instance transcriptLaw_isProbabilityMeasure (ρ : Density ι) :
    IsProbabilityMeasure (A.transcriptLaw ρ) := A.prefixLaw_isProbabilityMeasure ρ n _

theorem transcriptLaw_univ (ρ : Density ι) : A.transcriptLaw ρ Set.univ = 1 := measure_univ

/-- The actual reconstructed density matrix distribution; output rank is free. -/
def outputLaw (ρ : Density ι) : Measure (Density ι) :=
  (A.transcriptLaw ρ).map A.estimator.estimate

instance outputLaw_isProbabilityMeasure (ρ : Density ι) :
    IsProbabilityMeasure (A.outputLaw ρ) :=
  Measure.isProbabilityMeasure_map A.estimator.measurable_estimate.aemeasurable

theorem outputLaw_univ (ρ : Density ι) : A.outputLaw ρ Set.univ = 1 := measure_univ

theorem outputLaw_apply (ρ : Density ι) {S : Set (Density ι)} (hS : MeasurableSet S) :
    A.outputLaw ρ S = A.transcriptLaw ρ (A.estimator.estimate ⁻¹' S) :=
  Measure.map_apply A.estimator.measurable_estimate hS

/-- Success event for a genuine loss of the actual input and actual estimate. -/
def successSet (loss : Density ι → Density ι → ℝ≥0∞) (ρ : Density ι)
    (ε : ℝ≥0∞) : Set (History Seed Ω n) := {z | loss ρ (A.estimator.estimate z) ≤ ε}

theorem successSet_measurable (loss : Density ι → Density ι → ℝ≥0∞) (ρ : Density ι)
    (hLoss : Measurable (loss ρ)) (ε : ℝ≥0∞) :
    MeasurableSet (A.successSet loss ρ ε) :=
  measurableSet_le (hLoss.comp A.estimator.measurable_estimate) measurable_const

def successProbability (loss : Density ι → Density ι → ℝ≥0∞) (ρ : Density ι)
    (ε : ℝ≥0∞) : ℝ≥0∞ := A.transcriptLaw ρ (A.successSet loss ρ ε)

theorem successProbability_le_one (loss : Density ι → Density ι → ℝ≥0∞)
    (ρ : Density ι) (ε : ℝ≥0∞) : A.successProbability loss ρ ε ≤ 1 := by
  calc
    _ ≤ A.transcriptLaw ρ Set.univ := measure_mono (Set.subset_univ _)
    _ = 1 := A.transcriptLaw_univ ρ

theorem successProbability_eq_outputLaw (loss : Density ι → Density ι → ℝ≥0∞)
    (ρ : Density ι) (hLoss : Measurable (loss ρ)) (ε : ℝ≥0∞) :
    A.successProbability loss ρ ε = A.outputLaw ρ {σ | loss ρ σ ≤ ε} := by
  rw [A.outputLaw_apply ρ (measurableSet_le hLoss measurable_const)]
  rfl

/-- Uniform success for actual rank-at-most-`r` inputs. Event measurability is
explicit, and no measurability of a spectral divergence is silently asserted. -/
def LearnsRank (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε q : ℝ≥0∞) : Prop :=
  ∀ ρ : Density ι, ρ.matrix.rank ≤ r →
    MeasurableSet (A.successSet loss ρ ε) ∧ q ≤ A.successProbability loss ρ ε

def BuresSuccess (r : ℕ) (ε : ℝ≥0∞) : Prop :=
  A.LearnsRank QuantumModel.chiB r ε ((2 : ℝ≥0∞) / 3)

def RightSuccess (r : ℕ) (ε : ℝ≥0∞) : Prop :=
  A.LearnsRank QuantumModel.chiR r ε ((2 : ℝ≥0∞) / 3)

end Learner
end Paper26.AdaptiveModel
