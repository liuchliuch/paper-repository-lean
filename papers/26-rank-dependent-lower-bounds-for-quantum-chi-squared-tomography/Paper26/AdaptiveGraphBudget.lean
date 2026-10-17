import Paper26.AdaptiveCollectiveEmbedding
import Paper26.AdaptiveFisherChain
import Paper26.GraphFisherBudget

/-!
# Actual adaptive graph scores

The probability reference is the maximally mixed Born law, constructed in
`AdaptiveCollectiveEmbedding`. The score below differentiates the actual Born
trace, with inverse zero at zero likelihood. Positivity makes its derivative
zero on that branch. No score, chain identity or quantum budget is an input.
-/

noncomputable section

namespace Paper26.AdaptiveGraphBudget

open MeasureTheory ProbabilityTheory QuantumModel ContinuousPOVM AdaptiveModel
open scoped BigOperators ComplexOrder ENNReal Matrix

section NormalizedStep
variable {ι H Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace H] [MeasurableSpace Ω]

/-- A normalized history-dependent step, at one fixed history, is a genuine
finite-reference POVM. Its reference is a probability, even when the original
reference kernel is merely s-finite. -/
def normalizedStepPOVM (M : OneCopyStep ι H Ω) (h : H) : DominatedPOVM ι Ω where
  reference := M.normalize.reference h
  reference_finite := inferInstance
  effect := M.normalize.effect h
  entry_measurable i j := by
    intro t ht
    exact measurable_prodMk_left ((M.normalize.entry_measurable i j) ht)
  positive_ae := M.normalize.positive_ae h
  entry_integrable := M.normalize.entry_integrable h
  total := M.normalize.total h

/-- The same one-copy POVM in the actual tensor-copy index convention. -/
def normalizedStepLearner (M : OneCopyStep ι H Ω) (h : H) :
    CollectiveModel.Learner ι Ω 1 where
  measurement := {
    reference := (normalizedStepPOVM M h).reference
    reference_finite := inferInstance
    effect y := ((normalizedStepPOVM M h).effect y).submatrix
      (GraphFisherBudget.oneCopyEquiv (ι := ι)).symm
      (GraphFisherBudget.oneCopyEquiv (ι := ι)).symm
    entry_measurable i j := (normalizedStepPOVM M h).entry_measurable _ _
    positive_ae := (normalizedStepPOVM M h).positive_ae.mono fun _ hy => hy.submatrix _
    entry_integrable i j := (normalizedStepPOVM M h).entry_integrable _ _
    total i j := by
      simpa only [Matrix.one_apply,
        (GraphFisherBudget.oneCopyEquiv (ι := ι)).symm.injective.eq_iff] using
        (normalizedStepPOVM M h).total
          ((GraphFisherBudget.oneCopyEquiv (ι := ι)).symm i)
          ((GraphFisherBudget.oneCopyEquiv (ι := ι)).symm j) }
  estimator := ⟨fun _ => AdaptiveCollectiveEmbedding.uniformState ι, measurable_const⟩

theorem normalizedStepLearner_born (M : OneCopyStep ι H Ω) (h : H)
    (ρ : Density ι) (y : Ω) :
    (normalizedStepLearner M h).born ρ y = M.normalize.born ρ h y := by
  have he : GraphFisherBudget.oneCopyPOVM (normalizedStepLearner M h).measurement =
      normalizedStepPOVM M h := by
    congr 1
  rw [CollectiveModel.Learner.born,
    ← GraphFisherBudget.oneCopyPOVM_born, he]
  rfl

theorem normalizedStepLearner_outcomeMeasure (M : OneCopyStep ι H Ω) (h : H)
    (ρ : Density ι) :
    (normalizedStepLearner M h).outcomeMeasure ρ = M.bornKernel ρ h := by
  rw [← M.normalize_bornKernel ρ]
  change (M.normalize.reference h).withDensity
    (fun y => ENNReal.ofReal ((normalizedStepLearner M h).born ρ y)) = _
  simp_rw [normalizedStepLearner_born]
  exact (M.normalize.bornKernel_apply ρ h).symm

end NormalizedStep

section Score
variable {r s n : ℕ} [NeZero r] {Y : Type*} [MeasurableSpace Y]
  (A : CollectiveModel.Learner (Fin r ⊕ Fin s) Y n)

/-- The actual logarithmic Born derivative as a real covector. The inverse at
zero is totalized; the PSD zero branch is proved harmless below. -/
def scoreDual (θ : GraphExperiment.Parameter r s) (y : Y) :=
  (GraphExperiment.likelihood A θ y)⁻¹ • GraphExperiment.likelihoodDerivative A θ y

/-- Riesz coordinates of the actual Born score, in the graph parameter space. -/
def score (θ : GraphExperiment.Parameter r s) (y : Y) : GraphExperiment.Parameter r s :=
  (InnerProductSpace.toDual ℝ (GraphExperiment.Parameter r s)).symm (scoreDual A θ y)

theorem score_measurable (θ : GraphExperiment.Parameter r s) : Measurable (score A θ) := by
  apply (InnerProductSpace.toDual ℝ (GraphExperiment.Parameter r s)).symm.continuous.measurable.comp
  have hd : Measurable (fun y : Y => GraphExperiment.likelihoodDerivative A θ y) := by
    intro t ht
    exact measurable_prodMk_right ((GraphExperiment.likelihoodDerivative_joint_measurable A) ht)
  exact (GraphExperiment.likelihood_measurable A θ).inv.smul hd

theorem weighted_scoreDual (θ : GraphExperiment.Parameter r s) {y : Y}
    (hy : (A.measurement.effect y).PosSemidef) :
    GraphExperiment.likelihood A θ y • scoreDual A θ y =
      GraphExperiment.likelihoodDerivative A θ y := by
  by_cases hz : GraphExperiment.likelihood A θ y = 0
  · have hd := GraphExperiment.likelihoodRoot_score_eq A hy θ
    simpa [scoreDual, GraphExperiment.likelihoodRoot, hz] using hd
  · simp [scoreDual, smul_smul, hz]

/-- Density times score squared is the actual root Fisher contribution,
including the zero-likelihood branch. -/
theorem weighted_score_norm_sq (θ : GraphExperiment.Parameter r s) {y : Y}
    (hy : (A.measurement.effect y).PosSemidef) :
    GraphExperiment.likelihood A θ y * ‖score A θ y‖ ^ 2 =
      4 * ‖fderiv ℝ (GraphExperiment.likelihoodRoot A y) θ‖ ^ 2 := by
  have hn := A.measurement.born_nonneg (GraphExperiment.copyState θ) hy
  change 0 ≤ GraphExperiment.likelihood A θ y at hn
  rw [score, LinearIsometryEquiv.norm_map, scoreDual, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, inv_pow, GraphExperiment.likelihoodRoot_fderiv]
  by_cases hz : GraphExperiment.likelihood A θ y = 0
  · simp [hz, GraphExperiment.likelihoodRoot]
  · simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, div_pow]
    rw [GraphExperiment.likelihoodRoot, Real.sq_sqrt hn]
    field_simp
    ring

/-- The actual outcome-law score mean is zero. This uses the proved finite
matrix differentiation of the normalized Born integral. -/
theorem score_integral (θ : GraphExperiment.Parameter r s) :
    (∫ y, score A θ y ∂A.outcomeMeasure (GraphExperiment.state θ)) = 0 := by
  change (∫ y, score A θ y ∂A.measurement.reference.withDensity
    (fun y => ENNReal.ofReal (GraphExperiment.likelihood A θ y))) = 0
  rw [integral_withDensity_eq_integral_toReal_smul
    (GraphExperiment.likelihood_measurable A θ).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  calc
    _ = ∫ y, (InnerProductSpace.toDual ℝ (GraphExperiment.Parameter r s)).symm
        (GraphExperiment.likelihoodDerivative A θ y) ∂A.measurement.reference := by
      apply integral_congr_ae
      filter_upwards [A.measurement.positive_ae] with y hy
      have hn : 0 ≤ GraphExperiment.likelihood A θ y :=
        A.measurement.born_nonneg (GraphExperiment.copyState θ) hy
      rw [ENNReal.toReal_ofReal hn]
      rw [score, ← map_smul, weighted_scoreDual A θ hy]
    _ = _ := by
      have hi := (InnerProductSpace.toDual ℝ (GraphExperiment.Parameter r s)).symm.toContinuousLinearEquiv.integral_comp_comm
        (μ := A.measurement.reference) (GraphExperiment.likelihoodDerivative A θ)
      simpa only [GraphExperiment.likelihoodDerivative_integral, map_zero] using hi

/-- Actual change of measure, rather than a Fisher identity assumption. -/
theorem score_energy_lintegral (θ : GraphExperiment.Parameter r s) :
    (∫⁻ y, ENNReal.ofReal (‖score A θ y‖ ^ 2)
      ∂A.outcomeMeasure (GraphExperiment.state θ)) =
      ∫⁻ y, ENNReal.ofReal (4 * ‖fderiv ℝ (GraphExperiment.likelihoodRoot A y) θ‖ ^ 2)
        ∂A.measurement.reference := by
  change (∫⁻ y, ENNReal.ofReal (‖score A θ y‖ ^ 2)
    ∂A.measurement.reference.withDensity
      (fun y => ENNReal.ofReal (GraphExperiment.likelihood A θ y))) = _
  rw [lintegral_withDensity_eq_lintegral_mul _
    (GraphExperiment.likelihood_measurable A θ).ennreal_ofReal
    ((score_measurable A θ).norm.pow_const 2).ennreal_ofReal]
  apply lintegral_congr_ae
  filter_upwards [A.measurement.positive_ae] with y hy
  have hn : 0 ≤ GraphExperiment.likelihood A θ y :=
    A.measurement.born_nonneg (GraphExperiment.copyState θ) hy
  rw [Pi.mul_apply, ← ENNReal.ofReal_mul hn, weighted_score_norm_sq A θ hy]

end Score

section ActualStep
variable {r s : ℕ} [NeZero r] {H Ω : Type*}
  [MeasurableSpace H] [MeasurableSpace Ω]
  (M : OneCopyStep (Fin r ⊕ Fin s) H Ω)

/-- Joint measurability follows from the actual finite effect entries. -/
theorem normalizedStep_score_measurable (θ : GraphExperiment.Parameter r s) :
    Measurable (fun z : H × Ω => score (normalizedStepLearner M z.1) θ z.2) := by
  have hl : Measurable (fun z : H × Ω =>
      GraphExperiment.likelihood (normalizedStepLearner M z.1) θ z.2) := by
    simpa only [GraphExperiment.likelihood, normalizedStepLearner_born] using
      M.normalize.born_joint_measurable (GraphExperiment.state θ)
  have hd : Measurable (fun z : H × Ω =>
      GraphExperiment.likelihoodDerivative (normalizedStepLearner M z.1) θ z.2) := by
    simp_rw [GraphFisherBudget.likelihoodDerivative_eq_ambient]
    apply ((ContinuousLinearMap.compL ℝ (GraphExperiment.Parameter r s) ℂ ℝ)
      Complex.reCLM).continuous.measurable.comp
    exact Finset.measurable_sum Finset.univ fun i _ =>
      Finset.measurable_sum Finset.univ fun j _ =>
        (M.normalize.entry_measurable j i).smul_const
          (fderiv ℝ (fun t : GraphExperiment.Parameter r s =>
            (GraphExperiment.state t).matrix i j) θ)
  exact (InnerProductSpace.toDual ℝ (GraphExperiment.Parameter r s)).symm.continuous.measurable.comp
    (hl.inv.smul hd)

/-- Conditional mean0 under the original actual Born transition kernel. -/
theorem normalizedStep_score_integral (h : H) (θ : GraphExperiment.Parameter r s) :
    (∫ y, score (normalizedStepLearner M h) θ y
      ∂M.bornKernel (GraphExperiment.state θ) h) = 0 := by
  rw [← normalizedStepLearner_outcomeMeasure]
  exact score_integral _ θ

/-- The one-step conditional information is at most4s/r, proved by applying
one-copy graph geometry to the normalized actual POVM. -/
theorem normalizedStep_score_energy (G : GraphFisherBudget.GraphTangentInput)
    (h : H) (θ : GraphExperiment.Parameter r s) :
    (∫⁻ y, ENNReal.ofReal (‖score (normalizedStepLearner M h) θ y‖ ^ 2)
      ∂M.bornKernel (GraphExperiment.state θ) h) ≤
      ENNReal.ofReal (4 * (s : ℝ) / (r : ℝ)) := by
  rw [← normalizedStepLearner_outcomeMeasure, score_energy_lintegral]
  exact GraphFisherBudget.onecopy_fisher_budget_lintegral _ G θ

end ActualStep

section ActualProcess
universe u
variable {r s n : ℕ} [NeZero r] {Seed Ω : Type u}
  [MeasurableSpace Seed] [MeasurableSpace Ω]
  (A : AdaptiveModel.Learner (Fin r ⊕ Fin s) Seed Ω n)
  (G : GraphFisherBudget.GraphTangentInput) (θ : GraphExperiment.Parameter r s)

/-- The score increment of the actual history-dependent normalized Born
transition. Normalization preserves every actual input-state law. -/
def stepScore (k : Fin n) (z : History Seed Ω (k.val + 1)) :
    GraphExperiment.Parameter r s :=
  score (normalizedStepLearner (A.step k) z.1) θ z.2

theorem stepScore_measurable (k : Fin n) : Measurable (stepScore A θ k) :=
  normalizedStep_score_measurable (A.step k) θ

include G

theorem stepScore_energy_lintegral (k : Fin n) :
    (∫⁻ z, ENNReal.ofReal (‖stepScore A θ k z‖ ^ 2)
      ∂A.prefixLaw (GraphExperiment.state θ) (k.val + 1) (Nat.succ_le_iff.mpr k.isLt)) ≤
      ENNReal.ofReal (4 * (s : ℝ) / (r : ℝ)) := by
  change (∫⁻ z : History Seed Ω k.val × Ω,
    ENNReal.ofReal (‖stepScore A θ k z‖ ^ 2)
      ∂(A.prefixLaw (GraphExperiment.state θ) k.val (Nat.le_of_lt k.isLt)).compProd
        ((A.step k).bornKernel (GraphExperiment.state θ))) ≤ _
  rw [Measure.lintegral_compProd ((stepScore_measurable A θ k).norm.pow_const 2).ennreal_ofReal]
  calc
    _ ≤ ∫⁻ _h : History Seed Ω k.val, ENNReal.ofReal (4 * (s : ℝ) / (r : ℝ))
        ∂A.prefixLaw (GraphExperiment.state θ) k.val (Nat.le_of_lt k.isLt) := by
      apply lintegral_mono
      intro h
      exact normalizedStep_score_energy (A.step k) G h θ
    _ = _ := by simp

theorem stepScore_memLp (k : Fin n) : MemLp (stepScore A θ k) 2
    (A.prefixLaw (GraphExperiment.state θ) (k.val + 1) (Nat.succ_le_iff.mpr k.isLt)) := by
  apply (memLp_two_iff_integrable_sq_norm (stepScore_measurable A θ k).aestronglyMeasurable).2
  apply (lintegral_ofReal_ne_top_iff_integrable
    ((stepScore_measurable A θ k).aestronglyMeasurable.norm.pow 2)
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)).1
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (stepScore_energy_lintegral A G θ k)

/-- A genuine score process, built from the actual adaptive measurements.
Its measurability, joint L2 and conditional mean0 are deductions. -/
def actualScoreProcess : AdaptiveFisherChain.ScoreProcess A (GraphExperiment.state θ) (2 * r * s) where
  score := stepScore A θ
  measurable_score := stepScore_measurable A θ
  memLp_score := stepScore_memLp A G θ
  conditional_mean_zero k := Filter.Eventually.of_forall fun h =>
    normalizedStep_score_integral (A.step k) h θ

theorem actual_stepEnergy_le (k : Fin n) :
    (actualScoreProcess A G θ).stepEnergy k ≤ 4 * (s : ℝ) / (r : ℝ) := by
  have hi := (stepScore_memLp A G θ k).norm.integrable_sq
  have he := stepScore_energy_lintegral A G θ k
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)] at he
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 he

/-- Native martingale energy addition with the actual one-copy quantum
budget. Identifying this accumulated score with the full transcript Born
score is proved separately below. -/
theorem actual_accumulated_score_energy :
    (∫ z, ‖(actualScoreProcess A G θ).totalScore z‖ ^ 2
      ∂A.transcriptLaw (GraphExperiment.state θ)) ≤
      (n : ℝ) * (4 * (s : ℝ) / (r : ℝ)) :=
  (actualScoreProcess A G θ).totalScore_energy_le _ (actual_stepEnergy_le A G θ)

end ActualProcess

section Transcript
universe u
variable {r s n : ℕ} [NeZero r] {Seed Ω : Type u}
  [MeasurableSpace Seed] [MeasurableSpace Ω]
  (A : AdaptiveModel.Learner (Fin r ⊕ Fin s) Seed Ω n)

/-- The constructed actual prefix POVM with an immaterial constant estimator. -/
def prefixLearner (k : ℕ) (hk : k ≤ n) :
    CollectiveModel.Learner (Fin r ⊕ Fin s) (History Seed Ω k) k where
  measurement := AdaptiveCollectiveEmbedding.prefixMeasurement A k hk
  estimator := ⟨fun _ => AdaptiveCollectiveEmbedding.uniformState (Fin r ⊕ Fin s),
    measurable_const⟩

theorem prefixLearner_outcomeMeasure (k : ℕ) (hk : k ≤ n)
    (ρ : Density (Fin r ⊕ Fin s)) :
    (prefixLearner A k hk).outcomeMeasure ρ = A.prefixLaw ρ k hk :=
  AdaptiveCollectiveEmbedding.prefixMeasurement_outcomeMeasure A ρ k hk

/-- A common PSD set makes the real Born product identity valid for every
parameter, before differentiation. No parameter-dependent exceptional set is
used for differentiating this identity. -/
theorem prefix_likelihood_mul (k : ℕ) (hk : k + 1 ≤ n)
    (z : History Seed Ω k × Ω)
    (hz : ((A.step ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩).normalize.effect
      z.1 z.2).PosSemidef) (θ : GraphExperiment.Parameter r s) :
    GraphExperiment.likelihood (prefixLearner A (k + 1) hk) θ z =
      GraphExperiment.likelihood (prefixLearner A k (Nat.le_trans (Nat.le_succ k) hk)) θ z.1 *
      GraphExperiment.likelihood
        (normalizedStepLearner (A.step ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩) z.1) θ z.2 := by
  have hi := EnergyReality.trace_hermitian_product_im
    (GraphExperiment.state θ).matrix _ (GraphExperiment.state θ).hermitian.eq hz.isHermitian.eq
  change ((AdaptiveCollectiveEmbedding.prefixMeasurement A (k + 1) hk).complexBorn
    (TensorCopies.density (GraphExperiment.state θ) (k + 1)) z).re = _
  rw [AdaptiveCollectiveEmbedding.prefix_complexBorn_succ, Complex.mul_re]
  rw [show ((A.step ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩).normalize.complexBorn
    (GraphExperiment.state θ) z.1 z.2).im = 0 from hi, mul_zero, sub_zero]
  simp only [GraphExperiment.likelihood, normalizedStepLearner_born]
  rfl

/-- Logarithmic differentiation of the actual product, at a nonzero joint
likelihood. The product zero branch has zero actual Born probability. -/
theorem prefix_score_succ (k : ℕ) (hk : k + 1 ≤ n)
    (z : History Seed Ω k × Ω)
    (hz : ((A.step ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩).normalize.effect
      z.1 z.2).PosSemidef) (θ : GraphExperiment.Parameter r s)
    (hn : GraphExperiment.likelihood (prefixLearner A (k + 1) hk) θ z ≠ 0) :
    score (prefixLearner A (k + 1) hk) θ z =
      score (prefixLearner A k (Nat.le_trans (Nat.le_succ k) hk)) θ z.1 +
      stepScore A θ ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩ z := by
  let B := prefixLearner A k (Nat.le_trans (Nat.le_succ k) hk)
  let C := normalizedStepLearner
    (A.step ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩) z.1
  have hf : (fun t : GraphExperiment.Parameter r s =>
      GraphExperiment.likelihood (prefixLearner A (k + 1) hk) t z) =
      fun t => GraphExperiment.likelihood B t z.1 * GraphExperiment.likelihood C t z.2 :=
    funext (prefix_likelihood_mul A k hk z hz)
  have hd := (GraphExperiment.likelihood_hasFDerivAt B θ z.1).mul
    (GraphExperiment.likelihood_hasFDerivAt C θ z.2)
  change HasFDerivAt (fun t : GraphExperiment.Parameter r s =>
    GraphExperiment.likelihood B t z.1 * GraphExperiment.likelihood C t z.2) _ θ at hd
  rw [← hf] at hd
  have he := (GraphExperiment.likelihood_hasFDerivAt (prefixLearner A (k + 1) hk) θ z).unique hd
  have hp := congrFun hf θ
  have hab : GraphExperiment.likelihood B θ z.1 ≠ 0 ∧
      GraphExperiment.likelihood C θ z.2 ≠ 0 := by
    rw [hp, mul_ne_zero_iff] at hn
    exact hn
  have hc1 : (GraphExperiment.likelihood B θ z.1 * GraphExperiment.likelihood C θ z.2)⁻¹ *
      GraphExperiment.likelihood B θ z.1 = (GraphExperiment.likelihood C θ z.2)⁻¹ := by
    field_simp [hab.1, hab.2]
  have hc2 : (GraphExperiment.likelihood B θ z.1 * GraphExperiment.likelihood C θ z.2)⁻¹ *
      GraphExperiment.likelihood C θ z.2 = (GraphExperiment.likelihood B θ z.1)⁻¹ := by
    field_simp [hab.1, hab.2]
  change (InnerProductSpace.toDual ℝ (GraphExperiment.Parameter r s)).symm
    (scoreDual (prefixLearner A (k + 1) hk) θ z) =
      (InnerProductSpace.toDual ℝ (GraphExperiment.Parameter r s)).symm (scoreDual B θ z.1) +
      (InnerProductSpace.toDual ℝ (GraphExperiment.Parameter r s)).symm (scoreDual C θ z.2)
  rw [← map_add]
  congr 1
  unfold scoreDual
  rw [he, hp]
  simp only [smul_add, smul_smul, hc1, hc2]
  exact add_comm _ _

/-- The a.e. statement is under the actual Born history law. Its zero-density
branch is removed by the native withDensity a.e. theorem. -/
theorem prefix_score_succ_ae (k : ℕ) (hk : k + 1 ≤ n)
    (θ : GraphExperiment.Parameter r s) :
    ∀ᵐ z ∂A.prefixLaw (GraphExperiment.state θ) (k + 1) hk,
      score (prefixLearner A (k + 1) hk) θ z =
        score (prefixLearner A k (Nat.le_trans (Nat.le_succ k) hk)) θ z.1 +
        stepScore A θ ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩ z := by
  rw [← prefixLearner_outcomeMeasure A (k + 1) hk]
  change ∀ᵐ z ∂(prefixLearner A (k + 1) hk).measurement.reference.withDensity
    (fun z => ENNReal.ofReal (GraphExperiment.likelihood (prefixLearner A (k + 1) hk) θ z)), _
  apply (ae_withDensity_iff (GraphExperiment.likelihood_measurable _ θ).ennreal_ofReal).2
  filter_upwards [AdaptiveCollectiveEmbedding.siteEffect_posSemidef_ae A (k + 1) hk] with z hz hn
  have hp : ((A.step ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩).normalize.effect
      z.1 z.2).PosSemidef := by
    simpa only [AdaptiveCollectiveEmbedding.siteEffect, Fin.lastCases_last] using hz (Fin.last k)
  exact prefix_score_succ A k hk z hp θ (fun h => hn (by simp [h]))

theorem prefix_score_zero (h0 : 0 ≤ n) (θ : GraphExperiment.Parameter r s)
    (z : History Seed Ω 0) : score (prefixLearner A 0 h0) θ z = 0 := by
  have hl : (fun t : GraphExperiment.Parameter r s =>
      GraphExperiment.likelihood (prefixLearner A 0 h0) t z) = fun _ => (1 : ℝ) := by
    funext t
    simp [GraphExperiment.likelihood, CollectiveModel.Learner.born, DominatedPOVM.born,
      DominatedPOVM.complexBorn, prefixLearner, AdaptiveCollectiveEmbedding.prefixMeasurement,
      AdaptiveCollectiveEmbedding.effectProduct, TensorSLD.tensor, TensorCopies.density,
      TensorCopies.matrix, Matrix.trace, Matrix.mul_apply]
  have hd := GraphExperiment.likelihood_hasFDerivAt (prefixLearner A 0 h0) θ z
  rw [hl] at hd
  have he := hd.unique (hasFDerivAt_const 1 θ)
  simp [score, scoreDual, he]

variable (G : GraphFisherBudget.GraphTangentInput)
include G

/-- The accumulated scores constructed from the actual one-copy Born kernels
are the derivative of the actual joint transcript likelihood, a.e. under its
actual probability law. -/
theorem prefix_score_eq_sum (k : ℕ) (hk : k ≤ n) (θ : GraphExperiment.Parameter r s) :
    ∀ᵐ z ∂A.prefixLaw (GraphExperiment.state θ) k hk,
      score (prefixLearner A k hk) θ z = (actualScoreProcess A G θ).sumScore k hk z := by
  induction k with
  | zero =>
      exact Filter.Eventually.of_forall fun z => prefix_score_zero A hk θ z
  | succ k ih =>
      have hold := (AdaptiveFisherChain.fst_measurePreserving
        (A.prefixLaw (GraphExperiment.state θ) k (Nat.le_trans (Nat.le_succ k) hk))
        ((A.step ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩).bornKernel
          (GraphExperiment.state θ))).quasiMeasurePreserving.ae (ih _)
      filter_upwards [prefix_score_succ_ae A k hk θ, hold] with z hz ho
      rw [hz, ho]
      rfl

/-- Genuine adaptive Fisher budget for the actual embedded transcript POVM.
All regularity and the score chain are proved from its actual finite effects;
the only geometry input is the pre-existing raw graph tangent formula. -/
theorem adaptive_fisher_budget_lintegral (θ : GraphExperiment.Parameter r s) :
    (∫⁻ z, ENNReal.ofReal (4 * ‖fderiv ℝ
      (GraphExperiment.likelihoodRoot (AdaptiveCollectiveEmbedding.collectiveLearner A) z) θ‖ ^ 2)
      ∂(AdaptiveCollectiveEmbedding.collectiveLearner A).measurement.reference) ≤
      ENNReal.ofReal ((n : ℝ) * (4 * (s : ℝ) / (r : ℝ))) := by
  rw [← score_energy_lintegral]
  have he : ∀ᵐ z ∂A.transcriptLaw (GraphExperiment.state θ),
      score (AdaptiveCollectiveEmbedding.collectiveLearner A) θ z =
        (actualScoreProcess A G θ).totalScore z :=
    prefix_score_eq_sum A G n (Nat.le_refl n) θ
  rw [AdaptiveCollectiveEmbedding.collectiveLearner_outcomeMeasure]
  calc
    _ = ∫⁻ z, ENNReal.ofReal (‖(actualScoreProcess A G θ).totalScore z‖ ^ 2)
        ∂A.transcriptLaw (GraphExperiment.state θ) :=
      lintegral_congr_ae (he.mono fun _ hz => by rw [hz])
    _ = ENNReal.ofReal (∫ z, ‖(actualScoreProcess A G θ).totalScore z‖ ^ 2
        ∂A.transcriptLaw (GraphExperiment.state θ)) := by
      symm
      exact ofReal_integral_eq_lintegral_ofReal
        ((actualScoreProcess A G θ).sumScore_memLp n (Nat.le_refl n)).norm.integrable_sq
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)
    _ ≤ _ := ENNReal.ofReal_le_ofReal (actual_accumulated_score_energy A G θ)

/-- The Fisher integrand of the actual transcript is genuinely integrable. -/
theorem adaptive_fisher_integrable (θ : GraphExperiment.Parameter r s) :
    Integrable (fun z => 4 * ‖fderiv ℝ
      (GraphExperiment.likelihoodRoot (AdaptiveCollectiveEmbedding.collectiveLearner A) z) θ‖ ^ 2)
      (AdaptiveCollectiveEmbedding.collectiveLearner A).measurement.reference := by
  have hm : Measurable (fun z => fderiv ℝ
      (GraphExperiment.likelihoodRoot (AdaptiveCollectiveEmbedding.collectiveLearner A) z) θ) := by
    intro t ht
    exact measurable_prodMk_right
      ((GraphExperiment.likelihoodRoot_fderiv_joint_measurable
        (AdaptiveCollectiveEmbedding.collectiveLearner A)) ht)
  apply (lintegral_ofReal_ne_top_iff_integrable
    ((hm.norm.pow_const 2).const_mul 4).aestronglyMeasurable
    (Filter.Eventually.of_forall fun _ => by positivity)).1
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (adaptive_fisher_budget_lintegral A G θ)

/-- Real-integral version of the actual n-step Fisher bound4ns/r. -/
theorem adaptive_fisher_budget (θ : GraphExperiment.Parameter r s) :
    (∫ z, 4 * ‖fderiv ℝ
      (GraphExperiment.likelihoodRoot (AdaptiveCollectiveEmbedding.collectiveLearner A) z) θ‖ ^ 2
      ∂(AdaptiveCollectiveEmbedding.collectiveLearner A).measurement.reference) ≤
      (n : ℝ) * (4 * (s : ℝ) / (r : ℝ)) := by
  have he := adaptive_fisher_budget_lintegral A G θ
  rw [← ofReal_integral_eq_lintegral_ofReal (adaptive_fisher_integrable A G θ)
    (Filter.Eventually.of_forall fun _ => by positivity)] at he
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 he

/-- The unscaled root-gradient energy is integrable. -/
theorem adaptive_root_energy_integrable (θ : GraphExperiment.Parameter r s) :
    Integrable (fun z => ‖fderiv ℝ
      (GraphExperiment.likelihoodRoot (AdaptiveCollectiveEmbedding.collectiveLearner A) z) θ‖ ^ 2)
      (AdaptiveCollectiveEmbedding.collectiveLearner A).measurement.reference := by
  simpa only [← mul_assoc, one_div_mul_cancel (by norm_num : (4 : ℝ) ≠ 0), one_mul] using
    (adaptive_fisher_integrable A G θ).const_mul (1 / 4 : ℝ)

/-- The normalization consumed by the actual posterior identity. -/
theorem adaptive_root_energy_budget (θ : GraphExperiment.Parameter r s) :
    (∫ z, ‖fderiv ℝ
      (GraphExperiment.likelihoodRoot (AdaptiveCollectiveEmbedding.collectiveLearner A) z) θ‖ ^ 2
      ∂(AdaptiveCollectiveEmbedding.collectiveLearner A).measurement.reference) ≤
      (n : ℝ) * (s : ℝ) / (r : ℝ) := by
  have he := adaptive_fisher_budget A G θ
  rw [integral_const_mul] at he
  nlinarith [show (n : ℝ) * (4 * (s : ℝ) / (r : ℝ)) =
    4 * ((n : ℝ) * (s : ℝ) / (r : ℝ)) by ring]

end Transcript

end Paper26.AdaptiveGraphBudget
