import Paper26.OneCopyMeanVariance
import Paper26.OneCopyNormalized
import Paper26.OneCopyProductProtocol

/-! The source's constant-confidence full-rank one-copy right-loss upper
bound without a logarithm. It uses the actual mean observation, native
Frobenius projection onto density matrices, Markov and regularization. -/
noncomputable section
open scoped ENNReal BigOperators ComplexOrder
open MeasureTheory

namespace Paper26.OneCopyFullRank
open QuantumModel CollectiveModel ContinuousPOVM OneCopyObservation OneCopySubmatrix
open OneCopyMeanVariance OneCopyNormalized FrobeniusLearning
variable {d : ℕ} [NeZero d]
local instance matrixMeasurableSpace (m n : Type*) : MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))

def projectedEstimator (N : ℕ) : Estimator (Fin d) (Fin N → Outcome (Fin d)) :=
  ⟨fun z => DensityProjection.project d (sampleAverage N z),
    (DensityProjection.measurable_project d).comp (sampleAverage_measurable N)⟩

def squaredError (N : ℕ) (ρ : Density (Fin d)) (z : Fin N → Outcome (Fin d)) : ℝ :=
  ShellAccounting.frobeniusSq (((projectedEstimator N).estimate z).matrix - ρ.matrix)

theorem squaredError_nonneg (N : ℕ) (ρ : Density (Fin d)) (z : Fin N → Outcome (Fin d)) :
    0 ≤ squaredError N ρ z := ShellAccounting.frobeniusSq_nonneg _

theorem squaredError_measurable (N : ℕ) (ρ : Density (Fin d)) : Measurable (squaredError N ρ) :=
  frobenius_error_measurable _ (projectedEstimator N).measurable_matrix ρ.matrix

theorem squaredError_le (N : ℕ) (ρ : Density (Fin d)) (z : Fin N → Outcome (Fin d)) :
    squaredError N ρ z ≤ ShellAccounting.frobeniusSq (sampleAverage N z-ρ.matrix) := by
  simpa only [Regularization.frobeniusSq_eq_entryNorm, squaredError, projectedEstimator] using
    DensityProjection.frobenius_error_le d (sampleAverage N z) ρ

theorem mean_error_le (μ : Measure (OneCopyObservation.PureFrame (Fin d))) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (ρ : Density (Fin d)) (N : ℕ) (hN : 0 < N) :
    (∫⁻ z, ENNReal.ofReal (squaredError N ρ z) ∂sampleMeasure μ ρ.matrix N) ≤
      ENNReal.ofReal (2*(d : ℝ)^2/(N : ℝ)) := by
  apply (lintegral_mono (fun z => ENNReal.ofReal_le_ofReal (squaredError_le N ρ z))).trans
  rw [← ofReal_integral_eq_lintegral_ofReal
    (average_error_integrable μ H ρ.matrix ρ.positive (by simp [ρ.trace_one]) N hN)
    (ae_of_all _ fun z => ShellAccounting.frobeniusSq_nonneg _), equation_54 μ H ρ N hN]
  apply ENNReal.ofReal_le_ofReal
  have ht : 0 ≤ (Matrix.trace (ρ.matrix*ρ.matrix)).re := trace_mul_effect_nonneg ρ ρ.positive
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast NeZero.pos d
  simp only [Fintype.card_fin]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  nlinarith [sq_nonneg ((d : ℝ)-1)]

theorem failure_le_quarter (μ : Measure (OneCopyObservation.PureFrame (Fin d))) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (ρ : Density (Fin d)) (N : ℕ) (hN : 0 < N)
    {η : ℝ} (hη : 0 < η) (hcost : 8*(d : ℝ)^2 ≤ η*N) :
    sampleMeasure μ ρ.matrix N {z | η < squaredError N ρ z} ≤ (1 : ℝ≥0∞)/4 := by
  letI : IsProbabilityMeasure (outcomeMeasure μ ρ.matrix) :=
    ⟨outcomeMeasure_univ μ H ρ.matrix ρ.positive (by simp [ρ.trace_one])⟩
  letI : IsProbabilityMeasure (sampleMeasure μ ρ.matrix N) := by unfold sampleMeasure; infer_instance
  have hm : (∫⁻ z, ENNReal.ofReal (squaredError N ρ z) ∂sampleMeasure μ ρ.matrix N) ≤
      ENNReal.ofReal (η/4) := by
    apply (mean_error_le μ H ρ N hN).trans
    apply ENNReal.ofReal_le_ofReal
    exact (div_le_iff₀ (Nat.cast_pos.mpr hN)).2 (by nlinarith)
  have hp : ENNReal.ofReal η ≠ 0 := (ENNReal.ofReal_pos.mpr hη).ne'
  calc
    _ ≤ sampleMeasure μ ρ.matrix N {z | ENNReal.ofReal η ≤ ENNReal.ofReal (squaredError N ρ z)} :=
      measure_mono (fun z hz => ENNReal.ofReal_le_ofReal hz.le)
    _ ≤ (∫⁻ z, ENNReal.ofReal (squaredError N ρ z) ∂sampleMeasure μ ρ.matrix N) /
        ENNReal.ofReal η := meas_ge_le_lintegral_div
      (squaredError_measurable N ρ).ennreal_ofReal.aemeasurable hp ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (η/4)/ENNReal.ofReal η := by gcongr
    _ = (1 : ℝ≥0∞)/4 := by
      rw [← ENNReal.ofReal_div_of_pos hη]
      have he : η/4/η = (1/4 : ℝ) := by field_simp
      rw [he, ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num

omit [NeZero d] in
theorem frobenius_sub_comm (A B : Matrix (Fin d) (Fin d) ℂ) :
    SpectralLoss.frobeniusSq (A-B) = ShellAccounting.frobeniusSq (B-A) := by
  rw [Regularization.frobeniusSq_eq_entryNorm]
  simp only [ShellAccounting.frobeniusSq, Matrix.sub_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [norm_sub_rev]

def regularizedEstimator (N : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Estimator (Fin d) (Fin N → Outcome (Fin d)) :=
  ⟨fun z => regularizedDensity (ε/8) (by positivity) (by linarith)
      ((projectedEstimator N).estimate z),
    (measurable_regularizedDensity (ε/8) (by positivity) (by linarith)).comp
      (projectedEstimator N).measurable_estimate⟩

theorem frobenius_implies_right (N : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ρ : Density (Fin d)) (z : Fin N → Outcome (Fin d))
    (hz : squaredError N ρ z ≤ ε^2/(64*(d : ℝ))) :
    chiR ρ ((regularizedEstimator N ε hε hε1).estimate z) ≤ ENNReal.ofReal ε := by
  let T := (projectedEstimator N).estimate z
  let σ := regularizedDensity (ε/8) (by positivity) (by linarith : ε/8<1) T
  change chiR ρ σ ≤ _
  rw [PositiveLossBridge.chiR_eq_standardRightEnergy ρ σ
    (Regularization.regularize_posDef _ T.positive (by positivity) (by linarith))]
  apply ENNReal.ofReal_le_ofReal
  apply Regularization.regularization_epsilon _ _ ρ.hermitian T.positive T.trace_one hε hε1
  simpa only [Fintype.card_fin, frobenius_sub_comm] using hz

theorem regularized_success (μ : Measure (OneCopyObservation.PureFrame (Fin d))) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (N : ℕ) (hN : 0 < N)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hcost : 512*(d : ℝ)^3/ε^2 ≤ N)
    (ρ : Density (Fin d)) :
    (2 : ℝ≥0∞)/3 ≤
      (Measure.pi (fun _ : Fin N => (fullMeasurement μ H).outcomeMeasure ρ))
        {z | chiR ρ ((regularizedEstimator N ε hε hε1).estimate z) ≤ ENNReal.ofReal ε} := by
  let η := ε^2/(64*(d : ℝ))
  have hd : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have hη : 0 < η := by dsimp [η]; positivity
  have hc : 8*(d : ℝ)^2 ≤ η*N := by
    have h := (div_le_iff₀ (sq_pos_of_pos hε)).mp hcost
    dsimp [η]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity : 0 < 64*(d : ℝ))).mpr
    nlinarith
  letI : IsProbabilityMeasure (outcomeMeasure μ ρ.matrix) :=
    ⟨outcomeMeasure_univ μ H ρ.matrix ρ.positive (by simp [ρ.trace_one])⟩
  letI : IsProbabilityMeasure (sampleMeasure μ ρ.matrix N) := by unfold sampleMeasure; infer_instance
  rw [fullSampleMeasure_eq]
  have hs := success_lower_from_failure (sampleMeasure μ ρ.matrix N) (squaredError N ρ) η
    (1/4) (by norm_num) (by simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ)<4),
      ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using failure_le_quarter μ H ρ N hN hη hc)
  have hthree : (2 : ℝ≥0∞)/3 ≤ ENNReal.ofReal (1-(1/4 : ℝ)) := by
    have h := ENNReal.ofReal_le_ofReal (show (2 : ℝ)/3 ≤ 1-(1/4 : ℝ) by norm_num)
    simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ)<3),
      ENNReal.ofReal_ofNat] using h
  apply (hthree.trans hs).trans
  exact measure_mono fun z hz => frobenius_implies_right N hε hε1 ρ z hz

def copies (ε : ℝ) : ℕ := ⌈512*(d : ℝ)^3/ε^2⌉₊

theorem copies_bound {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ((copies (d := d) ε : ℕ) : ℝ) ≤ 513*(d : ℝ)^3/ε^2 := by
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast NeZero.pos d
  have hscale : 1 ≤ (d : ℝ)^3/ε^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
    nlinarith [sq_nonneg ((d : ℝ)-1)]
  have h := (Nat.ceil_lt_add_one (show 0 ≤ 512*(d : ℝ)^3/ε^2 by positivity)).le
  change ((copies (d := d) ε : ℕ) : ℝ) ≤ _ at h
  calc
    _ ≤ 512*(d : ℝ)^3/ε^2+1 := h
    _ = 512*((d : ℝ)^3/ε^2)+1 := by ring
    _ ≤ 513*((d : ℝ)^3/ε^2) := by linarith
    _ = _ := by ring

theorem full_rank_upper (μ : Measure (OneCopyObservation.PureFrame (Fin d))) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (RN : SourceCopyComplexity.AllFixedOperatorRN (Fin d))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    SourceCopyComplexity.Nonecopy RN chiR d (ENNReal.ofReal ε) ≤
      ENNReal.ofReal (513*(d : ℝ)^3/ε^2) := by
  let N := copies (d := d) ε
  have hN : 0 < N := by
    change 0 < ⌈512*(d : ℝ)^3/ε^2⌉₊
    apply Nat.ceil_pos.mpr
    have hd : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
    positivity
  have hcost : 512*(d : ℝ)^3/ε^2 ≤ N := Nat.le_ceil _
  apply (OneCopyProductProtocol.Nonecopy_le (fullMeasurement μ H)
    (regularizedEstimator N ε hε hε1) RN chiR d (ENNReal.ofReal ε) ?_).trans
  · simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal (copies_bound hε hε1)
  · intro ρ _
    refine ⟨measurableSet_le ((LossMeasurability.measurable_chiR_comp
      (fun _ : Fin N → Outcome (Fin d) => ρ) (regularizedEstimator N ε hε hε1).estimate
      measurable_const (regularizedEstimator N ε hε hε1).measurable_estimate)) measurable_const, ?_⟩
    exact regularized_success μ H N hN hε hε1 hcost ρ

end Paper26.OneCopyFullRank
