import Paper26.AdaptiveLowerBounds
import Paper26.CoordinateTransport

/-!
# Exact adaptive coordinate transport and all-rank lower bounds

Finite index relabeling acts on every actual one-copy effect and on the final
estimated density. Seed, outcomes, histories and reference kernels are exactly
preserved. The actual Born kernels, prefix and transcript laws, transported
output laws, success probabilities and rank learning promises agree.

The final theorems therefore apply the proved adaptive graph/posterior lower
bounds to arbitrary finite ambient indices. This does not assert a jointly
measurable Radon--Nikodym representation for arbitrary operator-valued adaptive
POVM families on arbitrary outcome sigma-algebras.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal
open MeasureTheory ProbabilityTheory

namespace Paper26.AdaptiveCoordinateTransport

open QuantumModel ContinuousPOVM AdaptiveModel SymmetricSupport
open CoordinateTransport

variable {ι κ H Ω : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [MeasurableSpace H] [MeasurableSpace Ω]

/-- Actual history-dependent effects with their finite matrix indices
reindexed. Every reference kernel and history is retained. -/
def step (e : ι ≃ κ) (M : OneCopyStep ι H Ω) : OneCopyStep κ H Ω where
  reference := M.reference
  reference_sfinite := M.reference_sfinite
  effect h y := matrix e (M.effect h y)
  entry_measurable i j := M.entry_measurable (e.symm i) (e.symm j)
  positive_ae h := (M.positive_ae h).mono fun _ hy => matrix_posSemidef e hy
  entry_integrable h i j := M.entry_integrable h (e.symm i) (e.symm j)
  total h i j := by
    change (∫ y, M.effect h y (e.symm i) (e.symm j) ∂M.reference h) = _
    rw [M.total]
    exact congrArg (fun B : Matrix κ κ ℂ => B i j) (matrix_one e)

theorem step_complexBorn (e : ι ≃ κ) (M : OneCopyStep ι H Ω)
    (ρ : Density ι) (h : H) (y : Ω) :
    (step e M).complexBorn (density e ρ) h y = M.complexBorn ρ h y := by
  change Matrix.trace (matrix e ρ.matrix * matrix e (M.effect h y)) = _
  rw [← matrix_mul, matrix_trace]
  rfl

theorem step_born (e : ι ≃ κ) (M : OneCopyStep ι H Ω)
    (ρ : Density ι) (h : H) (y : Ω) :
    (step e M).born (density e ρ) h y = M.born ρ h y :=
  congrArg Complex.re (step_complexBorn e M ρ h y)

/-- The entire actual transition kernel is preserved, rather than merely
its integral on a selected event. -/
theorem step_bornKernel (e : ι ≃ κ) (M : OneCopyStep ι H Ω) (ρ : Density ι) :
    (step e M).bornKernel (density e ρ) = M.bornKernel ρ := by
  apply Kernel.ext
  intro h
  rw [(step e M).bornKernel_apply, M.bornKernel_apply]
  change (M.reference h).withDensity
    (fun y => ENNReal.ofReal ((step e M).born (density e ρ) h y)) = _
  simp only [step_born]

end Paper26.AdaptiveCoordinateTransport

namespace Paper26.AdaptiveCoordinateTransport

open QuantumModel ContinuousPOVM AdaptiveModel SymmetricSupport
open CoordinateTransport

universe u
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  {Seed Ω : Type u} [MeasurableSpace Seed] [MeasurableSpace Ω]

/-- The actual adaptive protocol in the new matrix coordinates. No seed,
outcome, history or measurement reference is changed. The estimator is the
same matrix-valued reconstruction in the new indices. -/
def learner {n : ℕ} (e : ι ≃ κ) (A : AdaptiveModel.Learner ι Seed Ω n) :
    AdaptiveModel.Learner κ Seed Ω n where
  seed := A.seed
  seed_probability := A.seed_probability
  step k := step e (A.step k)
  estimator :=
    { estimate := fun z => density e (A.estimator.estimate z)
      measurable_estimate := (measurable_density e).comp A.estimator.measurable_estimate }

theorem learner_prefixLaw {n : ℕ} (e : ι ≃ κ) (A : AdaptiveModel.Learner ι Seed Ω n)
    (ρ : Density ι) (k : ℕ) (hk : k ≤ n) :
    (learner e A).prefixLaw (density e ρ) k hk = A.prefixLaw ρ k hk := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change ((learner e A).prefixLaw (density e ρ) k
        (Nat.le_trans (Nat.le_succ k) hk)).compProd
          ((step e (A.step ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩)).bornKernel
            (density e ρ)) = _
      rw [ih _, step_bornKernel]
      rfl

theorem learner_transcriptLaw {n : ℕ} (e : ι ≃ κ) (A : AdaptiveModel.Learner ι Seed Ω n)
    (ρ : Density ι) :
    (learner e A).transcriptLaw (density e ρ) = A.transcriptLaw ρ :=
  learner_prefixLaw e A ρ n _

/-- Output distributions are exactly the pushforward by the measurable
actual density-coordinate equivalence. -/
theorem learner_outputLaw {n : ℕ} (e : ι ≃ κ) (A : AdaptiveModel.Learner ι Seed Ω n)
    (ρ : Density ι) :
    (learner e A).outputLaw (density e ρ) = (A.outputLaw ρ).map (density e) := by
  unfold AdaptiveModel.Learner.outputLaw
  rw [learner_transcriptLaw, Measure.map_map (measurable_density e) A.estimator.measurable_estimate]
  rfl

section Loss
variable {n : ℕ} (e : ι ≃ κ) (A : AdaptiveModel.Learner ι Seed Ω n)
  (Lι : Density ι → Density ι → ℝ≥0∞) (Lκ : Density κ → Density κ → ℝ≥0∞)
  (hL : ∀ ρ σ, Lκ (density e ρ) (density e σ) = Lι ρ σ)
include hL

theorem learner_successSet (ρ : Density ι) (ε : ℝ≥0∞) :
    (learner e A).successSet Lκ (density e ρ) ε = A.successSet Lι ρ ε := by
  ext z
  change Lκ (density e ρ) (density e (A.estimator.estimate z)) ≤ ε ↔
    Lι ρ (A.estimator.estimate z) ≤ ε
  rw [hL]

theorem learner_successProbability (ρ : Density ι) (ε : ℝ≥0∞) :
    (learner e A).successProbability Lκ (density e ρ) ε = A.successProbability Lι ρ ε := by
  unfold AdaptiveModel.Learner.successProbability
  rw [learner_successSet e A Lι Lκ hL, learner_transcriptLaw]

/-- Full measurable-event rank learning is preserved in both directions. -/
theorem learner_learnsRank_iff (r : ℕ) (ε q : ℝ≥0∞) :
    (learner e A).LearnsRank Lκ r ε q ↔ A.LearnsRank Lι r ε q := by
  constructor
  · intro h ρ hρ
    have hp := h (density e ρ) (by simpa using hρ)
    simpa only [learner_successSet e A Lι Lκ hL,
      learner_successProbability e A Lι Lκ hL] using hp
  · intro h ρ hρ
    obtain ⟨hm, hp⟩ := h (density e.symm ρ) (by simpa using hρ)
    have hs := learner_successSet e A Lι Lκ hL (density e.symm ρ) ε
    have hprob := learner_successProbability e A Lι Lκ hL (density e.symm ρ) ε
    have hback : density e (density e.symm ρ) = ρ := density_symm e.symm ρ
    rw [hback] at hs hprob
    exact ⟨hs.symm ▸ hm, hprob.symm ▸ hp⟩

end Loss

theorem buresSuccess_iff {n : ℕ} (e : ι ≃ κ) (A : AdaptiveModel.Learner ι Seed Ω n)
    (r : ℕ) (ε : ℝ≥0∞) :
    (learner e A).BuresSuccess r ε ↔ A.BuresSuccess r ε :=
  learner_learnsRank_iff e A chiB chiB (chiB_density e) r ε _

theorem rightSuccess_iff {n : ℕ} (e : ι ≃ κ) (A : AdaptiveModel.Learner ι Seed Ω n)
    (r : ℕ) (ε : ℝ≥0∞) :
    (learner e A).RightSuccess r ε ↔ A.RightSuccess r ε :=
  learner_learnsRank_iff e A chiR chiR (chiR_density e) r ε _

omit [Fintype κ] [DecidableEq κ] in
/-- The actual adaptive Bures lower bound for every finite ambient index of
cardinalityd, every nontrivial dimension and every promised input rank. -/
theorem bures_adaptive {d r n : ℕ} (hcard : Fintype.card ι = d)
    (hd : 2 ≤ d) (hr : 1 ≤ r) (hrd : r ≤ d)
    (V : CollectiveMainLowerBounds.RawVolumeInputs
      (RankReduction.reducedRank d r) (d - RankReduction.reducedRank d r))
    (An : 2 ≤ RankReduction.reducedRank d r * (d - RankReduction.reducedRank d r) →
      CollectiveMainLowerBounds.AnalysisInputs
        (2 * RankReduction.reducedRank d r * (d - RankReduction.reducedRank d r)))
    (P : SymmetricProjectorInput (CollectiveMainLowerBounds.AmbientIndex d r) n)
    (A : AdaptiveModel.Learner ι Seed Ω n) (G : GraphFisherBudget.GraphTangentInput)
    {C ε : ℝ} (hC : 0 < C) (N : GraphPrior.NZSmoothLocalPriorInput C)
    (hε : 0 < ε) (hsmall : ε ≤ CollectiveMainLowerBounds.accuracyThreshold C)
    (hA : A.BuresSuccess r (ENNReal.ofReal ε)) :
    CollectiveMainLowerBounds.sampleConstant C *
      ((r : ℝ) * Real.sqrt (r : ℝ) * d * Real.sqrt (d : ℝ) / ε) ≤ (n : ℝ) := by
  let e : ι ≃ CollectiveMainLowerBounds.AmbientIndex d r := ambientEquiv hcard
  exact AdaptiveLowerBounds.Main.bures_adaptive hd hr hrd V An P (learner e A)
    G hC N hε hsmall ((buresSuccess_iff e A r _).mpr hA)

omit [Fintype κ] [DecidableEq κ] in
/-- The actual adaptive right-inverse lower bound on every finite ambient
index, with the same coefficient and accuracy threshold. -/
theorem right_adaptive {d r n : ℕ} (hcard : Fintype.card ι = d)
    (hd : 2 ≤ d) (hr : 1 ≤ r) (hrd : r ≤ d)
    (V : CollectiveMainLowerBounds.RawVolumeInputs
      (RankReduction.reducedRank d r) (d - RankReduction.reducedRank d r))
    (An : 2 ≤ RankReduction.reducedRank d r * (d - RankReduction.reducedRank d r) →
      CollectiveMainLowerBounds.AnalysisInputs
        (2 * RankReduction.reducedRank d r * (d - RankReduction.reducedRank d r)))
    (P : SymmetricProjectorInput (CollectiveMainLowerBounds.AmbientIndex d r) n)
    (A : AdaptiveModel.Learner ι Seed Ω n) (G : GraphFisherBudget.GraphTangentInput)
    {C ε : ℝ} (hC : 0 < C) (N : GraphPrior.NZSmoothLocalPriorInput C)
    (hε : 0 < ε) (hsmall : ε ≤ CollectiveMainLowerBounds.accuracyThreshold C)
    (hA : A.RightSuccess r (ENNReal.ofReal ε)) :
    CollectiveMainLowerBounds.sampleConstant C * ((r : ℝ) * (d : ℝ) ^ 2 / ε ^ 2) ≤ (n : ℝ) := by
  let e : ι ≃ CollectiveMainLowerBounds.AmbientIndex d r := ambientEquiv hcard
  exact AdaptiveLowerBounds.Main.right_adaptive hd hr hrd V An P (learner e A)
    G hC N hε hsmall ((rightSuccess_iff e A r _).mpr hA)

end Paper26.AdaptiveCoordinateTransport
