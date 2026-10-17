import Paper26.PurePosterior
import Paper26.PureCovariantRisk
import Paper26.LossMeasurability
import Paper26.SingularHaarLoss
import Paper26.OperatorPOVMTransport

/-!
# Appendix A.1: actual Bayesian risk lower bounds

The posterior first moment is supplied by the proved Equation (51), rather
than by a statistical input.  In particular, singular-output infinite risk
below is derived from the positive definite actual posterior mean.
-/
noncomputable section
set_option maxHeartbeats 2000000
open scoped BigOperators Matrix ComplexOrder ENNReal
open MeasureTheory

namespace Paper26.A1LowerRisk
open QuantumModel HaarFrames PurePosterior PureCovariant SymmetricSupport CollectiveModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def conditionalRisk (ν : Measure (Frame ι (Fin 1))) (σ : Density ι) : ℝ≥0∞ :=
  ∫⁻ U, chiR U.density σ ∂ν

omit [Nonempty ι] in
theorem measurable_frame_density : Measurable (fun U : Frame ι (Fin 1) => U.density) := by
  intro s hs
  rcases hs with ⟨t, ht, rfl⟩
  exact Frame.measurable_density_matrix ht

omit [Nonempty ι] in
theorem frame_entry_integrable (ν : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure ν]
    (i j : ι) : Integrable (fun U : Frame ι (Fin 1) => U.density.matrix i j) ν := by
  apply Integrable.of_bound
    (((measurable_pi_apply j).comp ((measurable_pi_apply i).comp
      Frame.measurable_density_matrix)).aestronglyMeasurable) 1
  exact ae_of_all _ fun U => density_entry_norm_le_one U.density i j

omit [Nonempty ι] in
theorem mean_mulVec (ν : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure ν]
    (M : Matrix ι ι ℂ)
    (hM : ∀ i j, (∫ U, U.density.matrix i j ∂ν) = M i j) (x : ι → ℂ) (i : ι) :
    (∫ U, (U.density.matrix *ᵥ x) i ∂ν) = (M *ᵥ x) i := by
  simp only [Matrix.mulVec, dotProduct]
  rw [integral_finset_sum _ (fun j _ => (frame_entry_integrable ν i j).mul_const (x j))]
  simp_rw [integral_mul_const, hM]

omit [Nonempty ι] in
theorem mean_trace_integrable (ν : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure ν]
    (A : Matrix ι ι ℂ) :
    Integrable (fun U : Frame ι (Fin 1) => Matrix.trace (U.density.matrix * A)) ν := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  exact integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ =>
    (frame_entry_integrable ν i j).mul_const (A j i)

omit [Nonempty ι] in
theorem mean_trace (ν : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure ν]
    (M A : Matrix ι ι ℂ)
    (hM : ∀ i j, (∫ U, U.density.matrix i j ∂ν) = M i j) :
    (∫ U, Matrix.trace (U.density.matrix * A) ∂ν) = Matrix.trace (M * A) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun j _ =>
    (frame_entry_integrable ν i j).mul_const (A j i))]
  simp_rw [integral_finset_sum _ (fun j _ =>
    (frame_entry_integrable ν _ j).mul_const (A j _)), integral_mul_const, hM]

omit [Nonempty ι] in
/-- A singular output has infinite actual expected loss whenever the
actual posterior mean is positive definite.  No Haar-nullity input is used. -/
theorem conditionalRisk_singular (ν : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure ν]
    (M : Matrix ι ι ℂ) (hM : M.PosDef)
    (hMean : ∀ i j, (∫ U, U.density.matrix i j ∂ν) = M i j)
    (σ : Density ι) (hσ : ¬ σ.matrix.PosDef) : conditionalRisk ν σ = ∞ := by
  by_contra hfin
  have hm : Measurable (fun U : Frame ι (Fin 1) => chiR U.density σ) :=
    LossMeasurability.measurable_chiR_comp _ _ measurable_frame_density measurable_const
  have hs : ∀ᵐ U : Frame ι (Fin 1) ∂ν, SupportContained U.density σ := by
    filter_upwards [ae_lt_top hm hfin] with U hU
    exact (chiR_ne_top_iff _ _).1 hU.ne
  obtain ⟨x, hx, hker⟩ := SingularHaarLoss.singular_density_has_kernel σ hσ
  have hMx : M *ᵥ x = 0 := by
    ext i
    rw [← mean_mulVec ν M hMean x i]
    apply integral_eq_zero_of_ae
    filter_upwards [hs] with U hU
    exact congrFun (hU x hker) i
  have hp := hM.re_dotProduct_pos hx
  rw [hMx, dotProduct_zero] at hp
  exact lt_irrefl 0 hp

omit [Nonempty ι] in
theorem pure_inverse_trace_nonneg (U : Frame ι (Fin 1)) (σ : Density ι)
    (hσ : σ.matrix.PosDef) : 0 ≤ (Matrix.trace (U.density.matrix * σ.matrix⁻¹)).re - 1 := by
  have h := PositiveLossBridge.standardRightEnergy_nonneg U.density σ hσ
  rw [CommonCenter.standardRightEnergy_expansion _ _ hσ,
    PureMinimax.pure_idempotent U.density (by simpa using U.density_rank)] at h
  exact h

omit [Nonempty ι] in
/-- At positive outputs, actual pure loss is affine in the actual state,
so the conditional expectation is the inverse risk of its actual mean. -/
theorem conditionalRisk_positive (ν : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure ν]
    (M : Matrix ι ι ℂ)
    (hMean : ∀ i j, (∫ U, U.density.matrix i j ∂ν) = M i j)
    (σ : Density ι) (hσ : σ.matrix.PosDef) :
    conditionalRisk ν σ = ENNReal.ofReal ((Matrix.trace (M * σ.matrix⁻¹)).re - 1) := by
  unfold conditionalRisk
  have hf (U : Frame ι (Fin 1)) : chiR U.density σ =
      ENNReal.ofReal ((Matrix.trace (U.density.matrix * σ.matrix⁻¹)).re - 1) :=
    PureMinimax.pure_chiR_positive _ _ (by simpa using U.density_rank) hσ
  simp_rw [hf]
  have hir : Integrable (fun U : Frame ι (Fin 1) =>
      (Matrix.trace (U.density.matrix * σ.matrix⁻¹)).re) ν :=
    (mean_trace_integrable ν σ.matrix⁻¹).re
  have hi : Integrable (fun U : Frame ι (Fin 1) =>
      (Matrix.trace (U.density.matrix * σ.matrix⁻¹)).re - 1) ν :=
    hir.sub (integrable_const _)
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ fun U => pure_inverse_trace_nonneg U σ hσ)]
  congr 1
  rw [integral_sub hir (integrable_const _),
    integral_const, measureReal_univ_eq_one, one_smul]
  have hr := integral_re (mean_trace_integrable ν σ.matrix⁻¹)
  simp only [RCLike.re_eq_complex_re] at hr
  rw [hr, mean_trace ν M σ.matrix⁻¹ hMean]

/-- Every unrestricted density output obeys the posterior risk bound;
singular outputs are included with their genuine infinite loss. -/
theorem conditionalRisk_lower (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) {n : ℕ}
    (P : SymmetricProjectorInput ι (n + 1)) (Q : SymmetricProjectorInput ι (n + 2))
    (E : Matrix (Fin (n + 1) → ι) (Fin (n + 1) → ι) ℂ)
    (hE : E.PosSemidef) (hTr : 0 < (Matrix.trace E).re)
    (hComp : E = P.projector.matrix * E * P.projector.matrix) (σ : Density ι) :
    ENNReal.ofReal (PureMinimax.appendixARisk (ι := ι) (n + 1)) ≤
      conditionalRisk (posteriorMeasure μ E) σ := by
  let τ := reducedDensity E hE hTr
  let M := PureMinimax.posteriorMean τ (n + 1) (by positivity)
  letI := posteriorMeasure_probability μ E hE (evidence_pos μ H P E hComp hTr)
  have hMean : ∀ i j, (∫ U, U.density.matrix i j ∂posteriorMeasure μ E) = M.matrix i j :=
    equation_51_integral μ H P Q E hE hTr hComp
  by_cases hσ : σ.matrix.PosDef
  · rw [conditionalRisk_positive _ M.matrix hMean σ hσ]
    exact ENNReal.ofReal_le_ofReal (PureMinimax.posterior_matrix_risk_lower τ σ (n + 1)
      (by positivity) hσ)
  · rw [conditionalRisk_singular _ M.matrix (PureMinimax.posteriorMean_posDef _ _ _) hMean σ hσ]
    exact le_top

def compress {n : ℕ} (P : SymmetricProjectorInput ι n)
    (E : Matrix (Fin n → ι) (Fin n → ι) ℂ) := P.projector.matrix * E * P.projector.matrix

omit [DecidableEq ι] [Nonempty ι] in
theorem compress_positive {n : ℕ} (P : SymmetricProjectorInput ι n)
    (E : Matrix (Fin n → ι) (Fin n → ι) ℂ) (hE : E.PosSemidef) : (compress P E).PosSemidef := by
  simpa only [compress, P.projector.hermitian.eq] using hE.conjTranspose_mul_mul_same P.projector.matrix

omit [DecidableEq ι] [Nonempty ι] in
theorem compress_compressed {n : ℕ} (P : SymmetricProjectorInput ι n)
    (E : Matrix (Fin n → ι) (Fin n → ι) ℂ) :
    compress P E = P.projector.matrix * compress P E * P.projector.matrix := by
  simp only [compress, ← Matrix.mul_assoc, P.projector.idempotent]
  simp only [Matrix.mul_assoc, P.projector.idempotent]

omit [DecidableEq ι] [Nonempty ι] in
theorem trace_compress {n : ℕ} (P : SymmetricProjectorInput ι n)
    (E : Matrix (Fin n → ι) (Fin n → ι) ℂ) :
    Matrix.trace (compress P E) = Matrix.trace (P.projector.matrix * E) := by
  rw [compress, Matrix.trace_mul_cycle, P.projector.idempotent]

omit [Nonempty ι] in
theorem likelihood_compress {n : ℕ} (P : SymmetricProjectorInput ι n)
    (E : Matrix (Fin n → ι) (Fin n → ι) ℂ) (U : Frame ι (Fin 1)) :
    likelihood (compress P E) U = likelihood E U := by
  have hleft := contains_frame_tensor P U
  have hright := congrArg Matrix.conjTranspose hleft
  simp only [Matrix.conjTranspose_mul, (TensorCopies.density U.density n).hermitian.eq,
    P.projector.hermitian.eq] at hright
  unfold likelihood complexLikelihood compress
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hright, Matrix.trace_mul_cycle,
    hleft]

def weightedRisk (μ : Measure (Frame ι (Fin 1))) {n : ℕ}
    (E : Matrix (Fin n → ι) (Fin n → ι) ℂ) (σ : Density ι) : ℝ≥0∞ :=
  ∫⁻ U, ENNReal.ofReal (likelihood E U) * chiR U.density σ ∂μ

omit [Nonempty ι] in
theorem conditionalRisk_mul_evidence (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    {n : ℕ} (E : Matrix (Fin n → ι) (Fin n → ι) ℂ) (he : 0 < evidence μ E)
    (σ : Density ι) :
    ENNReal.ofReal (evidence μ E) * conditionalRisk (posteriorMeasure μ E) σ =
      weightedRisk μ E σ := by
  have hm : Measurable (fun U : Frame ι (Fin 1) => chiR U.density σ) :=
    LossMeasurability.measurable_chiR_comp _ _ measurable_frame_density measurable_const
  have hw : Measurable (fun U => ENNReal.ofReal (posteriorWeight μ E U)) :=
    ((likelihood_measurable E).const_mul _).ennreal_ofReal
  unfold conditionalRisk posteriorMeasure
  rw [lintegral_withDensity_eq_lintegral_mul μ hw hm]
  simp only [Pi.mul_apply, posteriorWeight, ENNReal.ofReal_mul (inv_nonneg.mpr he.le), mul_assoc]
  rw [lintegral_const_mul _ ((likelihood_measurable E).ennreal_ofReal.mul hm),
    ← mul_assoc, ← ENNReal.ofReal_mul he.le, mul_inv_cancel₀ he.ne', ENNReal.ofReal_one, one_mul]
  rfl

/-- Zero-trace effects contribute zero weight, rather than requiring a
fabricated posterior at an impossible outcome. -/
theorem weightedRisk_lower (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) {n : ℕ}
    (P : SymmetricProjectorInput ι (n + 1)) (Q : SymmetricProjectorInput ι (n + 2))
    (E : Matrix (Fin (n + 1) → ι) (Fin (n + 1) → ι) ℂ)
    (hE : E.PosSemidef) (hComp : E = P.projector.matrix * E * P.projector.matrix)
    (σ : Density ι) :
    ENNReal.ofReal (evidence μ E) * ENNReal.ofReal (PureMinimax.appendixARisk (ι := ι) (n + 1)) ≤
      weightedRisk μ E σ := by
  by_cases ht : 0 < (Matrix.trace E).re
  · have he := evidence_pos μ H P E hComp ht
    have h := mul_le_mul_left' (conditionalRisk_lower μ H P Q E hE ht hComp σ)
      (ENNReal.ofReal (evidence μ E))
    rwa [conditionalRisk_mul_evidence μ E he σ] at h
  · have ht0 : (Matrix.trace E).re = 0 :=
      le_antisymm (le_of_not_gt ht) (Complex.nonneg_iff.mp hE.trace_nonneg).1
    have he : evidence μ E = 0 := by rw [evidence, likelihood_integral_real μ H P E hComp, ht0, mul_zero]
    simp only [he, ENNReal.ofReal_zero, zero_mul, zero_le]

open ContinuousPOVM
variable {Ω : Type*} [MeasurableSpace Ω]

theorem evidence_compress_eq_born (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) {n : ℕ} (P : SymmetricProjectorInput ι n)
    (M : DominatedPOVM (Fin n → ι) Ω) (y : Ω) :
    evidence μ (compress P (M.effect y)) =
      M.born (P.projector.flat (by rw [P.dimension]; exact dimension_pos n)) y := by
  have hP : 0 < P.projector.matrix.rank := by rw [P.dimension]; exact dimension_pos n
  rw [evidence, likelihood_integral_real μ H P _ (compress_compressed P _), trace_compress,
    PureTensorSuccess.trace_projector_eq_rank_mul_born P.projector hP M y]
  have hr : (P.projector.matrix.rank : ℝ) = (dimension ι n : ℝ) := by exact_mod_cast P.dimension
  rw [hr]
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast (dimension_pos (ι := ι) n).ne' :
    (dimension ι n : ℝ) ≠ 0), one_mul]

def bayesRisk (μ : Measure (Frame ι (Fin 1))) {n : ℕ} (A : Learner ι Ω n) : ℝ≥0∞ :=
  ∫⁻ U, PureCovariantRisk.expectedRisk A U.density ∂μ

omit [Nonempty ι] in
theorem bayesRisk_eq_weightedRisk (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    {n : ℕ} (P : SymmetricProjectorInput ι n) (A : Learner ι Ω n) :
    bayesRisk μ A = ∫⁻ y, weightedRisk μ (compress P (A.measurement.effect y))
      (A.estimator.estimate y) ∂A.measurement.reference := by
  let f : Frame ι (Fin 1) × Ω → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (A.born z.1.density z.2) * chiR z.1.density (A.estimator.estimate z.2)
  have hf : Measurable f := (PureTensorSuccess.measurable_joint_born A).ennreal_ofReal.mul
    (LossMeasurability.measurable_joint_chiR _ _ measurable_frame_density A.estimator.measurable_estimate)
  have hrep : bayesRisk μ A = ∫⁻ U, ∫⁻ y, f (U, y) ∂A.measurement.reference ∂μ := by
    apply lintegral_congr
    intro U
    unfold PureCovariantRisk.expectedRisk Learner.outcomeMeasure DominatedPOVM.outcomeMeasure
    exact lintegral_withDensity_eq_lintegral_mul _ (A.measurement.born_measurable _).ennreal_ofReal
      (LossMeasurability.measurable_chiR_comp _ _ measurable_const A.estimator.measurable_estimate)
  rw [hrep, lintegral_lintegral_swap hf.aemeasurable]
  apply lintegral_congr
  intro y
  unfold weightedRisk
  simp_rw [likelihood_compress]
  rfl

/-- The actual Haar Bayes risk of every collective learner on an arbitrary
measurable outcome space obeys Appendix A.1's exact lower bound. -/
theorem bayesRisk_lower (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) {n : ℕ}
    (P : SymmetricProjectorInput ι (n + 1)) (Q : SymmetricProjectorInput ι (n + 2))
    (A : Learner ι Ω (n + 1)) :
    ENNReal.ofReal (PureMinimax.appendixARisk (ι := ι) (n + 1)) ≤ bayesRisk μ A := by
  let c := ENNReal.ofReal (PureMinimax.appendixARisk (ι := ι) (n + 1))
  let ρ := P.projector.flat (by rw [P.dimension]; exact dimension_pos (n + 1))
  have hb : (∫⁻ y, ENNReal.ofReal (A.measurement.born ρ y) ∂A.measurement.reference) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal (A.measurement.born_integrable ρ)
      (A.measurement.born_nonneg_ae ρ), A.measurement.born_integral ρ, ENNReal.ofReal_one]
  rw [bayesRisk_eq_weightedRisk μ P A]
  calc
    _ = ∫⁻ y, ENNReal.ofReal (A.measurement.born ρ y) * c ∂A.measurement.reference := by
      rw [lintegral_mul_const _ (A.measurement.born_measurable ρ).ennreal_ofReal, hb, one_mul]
    _ ≤ _ := by
      apply lintegral_mono_ae
      filter_upwards [A.measurement.positive_ae] with y hy
      have h := weightedRisk_lower μ H P Q (compress P (A.measurement.effect y))
        (compress_positive P _ hy) (compress_compressed P _) (A.estimator.estimate y)
      rwa [evidence_compress_eq_born μ H P A.measurement y] at h

theorem priorRisk_lower (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) (P : SymmetricProjectorInput ι 1) (σ : Density ι) :
    ENNReal.ofReal (PureMinimax.appendixARisk (ι := ι) 0) ≤ conditionalRisk μ σ := by
  let τ := AdaptiveCollectiveEmbedding.uniformState ι
  let M := PureMinimax.posteriorMean τ 0 (by norm_num)
  have heq : M.matrix = τ.matrix := by
    simp [M, PureMinimax.posteriorMean_affine, τ, AdaptiveCollectiveEmbedding.uniformState,
      one_div]
    ext i j
    simp [Matrix.smul_apply, Complex.real_smul]
  have hMean : ∀ i j, (∫ U, U.density.matrix i j ∂μ) = M.matrix i j := by
    intro i j
    rw [prior_mean μ H P, heq]
  by_cases hσ : σ.matrix.PosDef
  · rw [conditionalRisk_positive μ M.matrix hMean σ hσ]
    exact ENNReal.ofReal_le_ofReal (PureMinimax.posterior_matrix_risk_lower τ σ 0 (by norm_num) hσ)
  · rw [conditionalRisk_singular μ M.matrix (PureMinimax.posteriorMean_posDef _ _ _) hMean σ hσ]
    exact le_top

omit [Nonempty ι] in
theorem weightedRisk_zero (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (E : Matrix (Fin 0 → ι) (Fin 0 → ι) ℂ) (σ : Density ι) :
    weightedRisk μ E σ = ENNReal.ofReal (evidence μ E) * conditionalRisk μ σ := by
  have hm : Measurable (fun U : Frame ι (Fin 1) => chiR U.density σ) :=
    LossMeasurability.measurable_chiR_comp _ _ measurable_frame_density measurable_const
  simp only [weightedRisk, evidence, likelihood, complexLikelihood_zero, integral_const,
    measureReal_univ_eq_one, one_smul]
  rw [lintegral_const_mul _ hm]
  rfl

theorem bayesRisk_lower_zero (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) (P : SymmetricProjectorInput ι 0)
    (Q : SymmetricProjectorInput ι 1) (A : Learner ι Ω 0) :
    ENNReal.ofReal (PureMinimax.appendixARisk (ι := ι) 0) ≤ bayesRisk μ A := by
  let c := ENNReal.ofReal (PureMinimax.appendixARisk (ι := ι) 0)
  let ρ := P.projector.flat (by rw [P.dimension]; exact dimension_pos 0)
  have hb : (∫⁻ y, ENNReal.ofReal (A.measurement.born ρ y) ∂A.measurement.reference) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal (A.measurement.born_integrable ρ)
      (A.measurement.born_nonneg_ae ρ), A.measurement.born_integral ρ, ENNReal.ofReal_one]
  rw [bayesRisk_eq_weightedRisk μ P A]
  calc
    _ = ∫⁻ y, ENNReal.ofReal (A.measurement.born ρ y) * c ∂A.measurement.reference := by
      rw [lintegral_mul_const _ (A.measurement.born_measurable ρ).ennreal_ofReal, hb, one_mul]
    _ ≤ _ := by
      apply lintegral_mono
      intro y
      change ENNReal.ofReal (A.measurement.born ρ y) * c ≤
        weightedRisk μ (compress P (A.measurement.effect y)) (A.estimator.estimate y)
      rw [weightedRisk_zero, evidence_compress_eq_born μ H P A.measurement y]
      exact mul_le_mul_left' (priorRisk_lower μ H Q (A.estimator.estimate y)) _

/-- All copy numbers, including the actual zero-copy experiment. -/
theorem bayesRisk_lower_all (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) {n : ℕ}
    (P : SymmetricProjectorInput ι n) (Q : SymmetricProjectorInput ι (n + 1))
    (A : Learner ι Ω n) :
    ENNReal.ofReal (PureMinimax.appendixARisk (ι := ι) n) ≤ bayesRisk μ A := by
  cases n with
  | zero => simpa only [Nat.cast_zero] using bayesRisk_lower_zero μ H P Q A
  | succ n => simpa only [Nat.cast_add, Nat.cast_one] using bayesRisk_lower μ H P Q A

/-- Worst expected loss over the full actual rank-at-most-one family. -/
def worstRisk {n : ℕ} (A : Learner ι Ω n) : ℝ≥0∞ :=
  ⨆ ρ : Density ι, ⨆ _ : ρ.matrix.rank ≤ 1, PureCovariantRisk.expectedRisk A ρ

omit [Nonempty ι] in
theorem bayesRisk_le_worstRisk (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    {n : ℕ} (A : Learner ι Ω n) : bayesRisk μ A ≤ worstRisk A := by
  calc
    _ ≤ ∫⁻ _U : Frame ι (Fin 1), worstRisk A ∂μ := by
      apply lintegral_mono
      intro U
      exact le_iSup_of_le U.density (le_iSup_of_le (by simpa using U.density_rank.le) le_rfl)
    _ = _ := by simp

/-- Appendix A.1's minimax lower bound for every actual collective learner,
on arbitrary measurable outcomes and with unrestricted density outputs. -/
theorem worstRisk_lower (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) {n : ℕ}
    (P : SymmetricProjectorInput ι n) (Q : SymmetricProjectorInput ι (n + 1))
    (A : Learner ι Ω n) :
    ENNReal.ofReal (PureMinimax.appendixARisk (ι := ι) n) ≤ worstRisk A :=
  (bayesRisk_lower_all μ H P Q A).trans (bayesRisk_le_worstRisk μ A)

omit [DecidableEq ι] [Nonempty ι] in
theorem appendixARisk_eq (n m : ℕ) (hd : Fintype.card ι = m + 1) :
    PureMinimax.appendixARisk (ι := ι) n =
      (Real.sqrt ((n : ℝ) + 1) + m) ^ 2 / ((n : ℝ) + Fintype.card ι) - 1 := by
  have he : Real.sqrt ((n : ℝ) + 1) + Fintype.card ι - 1 = Real.sqrt ((n : ℝ) + 1) + m := by
    rw [hd]
    push_cast
    ring
  unfold PureMinimax.appendixARisk
  rw [he]

/-- The explicit covariant experiment achieves the matching worst risk.
The present construction uses `d=m+1≥2`; no minimax interchange is assumed. -/
theorem worstRisk_covariant (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) {n : ℕ}
    (P : SymmetricProjectorInput ι n) (Q : SymmetricProjectorInput ι (n + 1))
    (m : ℕ) (hm : 0 < m) (hd : Fintype.card ι = m + 1) :
    worstRisk (PureUpperBounds.learner μ H P m hm hd (PureCovariantRisk.isotropicMass n m)
      (PureCovariantRisk.isotropicMass_pos n m hm).le (PureCovariantRisk.isotropicMass_lt_one n m).le) =
      ENNReal.ofReal (PureMinimax.appendixARisk (ι := ι) n) := by
  apply le_antisymm
  · apply iSup_le
    intro ρ
    apply iSup_le
    intro hρ
    rw [PureCovariantRisk.achieved_risk_all_pure μ H P Q m hm hd ρ hρ,
      appendixARisk_eq n m hd]
  · exact worstRisk_lower μ H P Q _

open OperatorPOVMTransport

/-- Expected loss for the actual outcome law of an operator-valued POVM.
The RN choice represents that intrinsic law, as proved in the transport module. -/
def operatorExpectedRisk {n : ℕ} (R : OperatorRadonNikodymInput (Fin n → ι) Ω)
    (A : OperatorLearner ι Ω n) (ρ : Density ι) : ℝ≥0∞ :=
  ∫⁻ y, chiR ρ (A.estimator.estimate y) ∂A.outcomeMeasure R ρ

def operatorWorstRisk {n : ℕ} (R : OperatorRadonNikodymInput (Fin n → ι) Ω)
    (A : OperatorLearner ι Ω n) : ℝ≥0∞ :=
  ⨆ ρ : Density ι, ⨆ _ : ρ.matrix.rank ≤ 1, operatorExpectedRisk R A ρ

omit [Nonempty ι] in
theorem operatorExpectedRisk_eq {n : ℕ} (R : OperatorRadonNikodymInput (Fin n → ι) Ω)
    (A : OperatorLearner ι Ω n) (ρ : Density ι) :
    operatorExpectedRisk R A ρ = PureCovariantRisk.expectedRisk (A.toDominated R) ρ := rfl

omit [Nonempty ι] in
theorem operatorWorstRisk_eq {n : ℕ} (R : OperatorRadonNikodymInput (Fin n → ι) Ω)
    (A : OperatorLearner ι Ω n) : operatorWorstRisk R A = worstRisk (A.toDominated R) := rfl

omit [Nonempty ι] in
/-- The expected risk is independent of the classical RN witness used to
describe the intrinsic operator POVM outcome law. -/
theorem operatorExpectedRisk_independent {n : ℕ}
    (R S : OperatorRadonNikodymInput (Fin n → ι) Ω) (A : OperatorLearner ι Ω n) (ρ : Density ι) :
    operatorExpectedRisk R A ρ = operatorExpectedRisk S A ρ := by
  unfold operatorExpectedRisk OperatorLearner.outcomeMeasure
  rw [operatorOutcomeMeasure_choice_independent R S A.measurement (TensorCopies.density ρ n)]

omit [Nonempty ι] in
theorem operatorWorstRisk_independent {n : ℕ}
    (R S : OperatorRadonNikodymInput (Fin n → ι) Ω) (A : OperatorLearner ι Ω n) :
    operatorWorstRisk R A = operatorWorstRisk S A := by
  simp only [operatorWorstRisk, operatorExpectedRisk_independent R S A]

/-- The lower bound covers every actual operator POVM on arbitrary outcomes,
relative only to the existing classical matrix Radon--Nikodym representation. -/
theorem operatorWorstRisk_lower (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) {n : ℕ}
    (P : SymmetricProjectorInput ι n) (Q : SymmetricProjectorInput ι (n + 1))
    (R : OperatorRadonNikodymInput (Fin n → ι) Ω) (A : OperatorLearner ι Ω n) :
    ENNReal.ofReal (PureMinimax.appendixARisk (ι := ι) n) ≤ operatorWorstRisk R A := by
  rw [operatorWorstRisk_eq]
  exact worstRisk_lower μ H P Q (A.toDominated R)

omit [DecidableEq ι] in
/-- In dimension one the density type itself is a singleton. -/
theorem density_eq_of_card_one (hd : Fintype.card ι = 1) (ρ σ : Density ι) : ρ = σ := by
  letI : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.1 hd.le
  letI : Unique ι := uniqueOfSubsingleton (Classical.choice inferInstance)
  have hm : ρ.matrix = σ.matrix := by
    ext i j
    have hr : ρ.matrix default default = 1 := by simpa [Matrix.trace] using ρ.trace_one
    have hs : σ.matrix default default = 1 := by simpa [Matrix.trace] using σ.trace_one
    simp only [Subsingleton.elim i default, Subsingleton.elim j default, hr, hs]
  cases ρ
  cases σ
  cases hm
  rfl

omit [DecidableEq ι] [Nonempty ι] in
theorem appendixARisk_card_one (hd : Fintype.card ι = 1) (n : ℕ) :
    PureMinimax.appendixARisk (ι := ι) n = 0 := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  simp [PureMinimax.appendixARisk, hd, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1), hn]

/-- The degenerate one-dimensional boundary has zero risk for every
actual learner, so it needs no regularized covariant output construction. -/
theorem worstRisk_card_one (hd : Fintype.card ι = 1) {n : ℕ} (A : Learner ι Ω n) :
    worstRisk A = 0 := by
  apply le_antisymm _ (zero_le _)
  apply iSup_le
  intro ρ
  apply iSup_le
  intro _
  have hf (y : Ω) : chiR ρ (A.estimator.estimate y) = 0 := by
    rw [density_eq_of_card_one hd (A.estimator.estimate y) ρ, chiR_self]
  simp only [PureCovariantRisk.expectedRisk, hf, lintegral_zero, le_refl]

/-- A normalized actual experiment with a constant output, used only for
the one-dimensional boundary where every density is that output. -/
def constantLearner (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) {n : ℕ} (P : SymmetricProjectorInput ι n) :
    Learner ι (Frame ι (Fin 1)) n where
  measurement := measurement μ H P
  estimator := ⟨fun _ => AdaptiveCollectiveEmbedding.uniformState ι, measurable_const⟩

/-- An actual learner attains the exact value in every nonzero ambient
dimension and every copy number, including `d=1` and `n=0`. -/
theorem exists_attaining (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) {n : ℕ}
    (P : SymmetricProjectorInput ι n) (Q : SymmetricProjectorInput ι (n + 1)) :
    ∃ A : Learner ι (Frame ι (Fin 1)) n,
      worstRisk A = ENNReal.ofReal (PureMinimax.appendixARisk (ι := ι) n) := by
  by_cases hd : Fintype.card ι = 1
  · refine ⟨constantLearner μ H P, ?_⟩
    rw [worstRisk_card_one hd, appendixARisk_card_one hd, ENNReal.ofReal_zero]
  · let m := Fintype.card ι - 1
    have hd0 : 0 < Fintype.card ι := Fintype.card_pos
    have hm : 0 < m := by dsimp [m]; omega
    have hdim : Fintype.card ι = m + 1 := by dsimp [m]; omega
    exact ⟨_, worstRisk_covariant μ H P Q m hm hdim⟩

/-- Appendix A.1 / Equation (50), in operational minimax form: every
actual collective learner on the arbitrary outcome space has at least this
worst risk, and a genuine normalized experiment attains it.  No minimax
interchange, posterior formula, covariance assertion, or risk bound is an input. -/
theorem appendix_A_1 (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) {n : ℕ}
    (P : SymmetricProjectorInput ι n) (Q : SymmetricProjectorInput ι (n + 1)) :
    (∀ A : Learner ι Ω n,
      ENNReal.ofReal (PureMinimax.appendixARisk (ι := ι) n) ≤ worstRisk A) ∧
    (∃ A : Learner ι (Frame ι (Fin 1)) n,
      worstRisk A = ENNReal.ofReal (PureMinimax.appendixARisk (ι := ι) n)) :=
  ⟨worstRisk_lower μ H P Q, exists_attaining μ H P Q⟩

end Paper26.A1LowerRisk
