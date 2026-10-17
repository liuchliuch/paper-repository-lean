import Paper26.SymmetricSupport
import Paper26.CollectiveModel
import Mathlib.MeasureTheory.Integral.Prod

/-! The measurement-to-success-volume argument in Section 4, on actual
pure tensor inputs and actual dominated collective POVMs. -/
noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal
open MeasureTheory
set_option maxHeartbeats 2000000

namespace Paper26.PureTensorSuccess
open QuantumModel HaarFrames ContinuousPOVM CollectiveModel SymmetricSupport

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]

theorem measurable_frame_tensor_entry (n : ℕ) (i j : Fin n → ι) :
    Measurable (fun U : Frame ι (Fin 1) =>
      (TensorCopies.density U.density n).matrix i j) := by
  change Measurable (fun U : Frame ι (Fin 1) => ∏ k, U.density.matrix (i k) (j k))
  apply Finset.measurable_prod Finset.univ
  intro k _
  exact (measurable_pi_apply (j k)).comp
    ((measurable_pi_apply (i k)).comp Frame.measurable_density_matrix)

theorem measurable_joint_born {n : ℕ} (A : Learner ι Ω n) :
    Measurable (fun z : Frame ι (Fin 1) × Ω => A.born z.1.density z.2) := by
  change Measurable (fun z : Frame ι (Fin 1) × Ω =>
    (∑ i, ∑ j, (TensorCopies.density z.1.density n).matrix i j *
      A.measurement.effect z.2 j i).re)
  apply Measurable.re (𝕜 := ℂ)
  apply Finset.measurable_sum Finset.univ
  intro i _
  apply Finset.measurable_sum Finset.univ
  intro j _
  exact ((measurable_frame_tensor_entry n i j).comp measurable_fst).mul
    ((A.measurement.entry_measurable j i).comp measurable_snd)

theorem trace_projector_eq_rank_mul_born {η : Type*} [Fintype η] [DecidableEq η]
    (P : OrthogonalProjector η) (hP : 0 < P.matrix.rank)
    (M : DominatedPOVM η Ω) (y : Ω) :
    (Matrix.trace (P.matrix * M.effect y)).re =
      (P.matrix.rank : ℝ) * M.born (P.flat hP) y := by
  have hR : (P.matrix.rank : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
  simp only [DominatedPOVM.born, DominatedPOVM.complexBorn, OrthogonalProjector.flat,
    Matrix.smul_mul, Matrix.trace_smul, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  field_simp

/-- Pure-state average success is bounded by the symmetric dimension times
the largest successful pure-state volume. The only event regularity premise
is explicit joint measurability; no statistical inequality is an input. -/
theorem average_success_le_dimension_volume {n : ℕ}
    (P : SymmetricProjectorInput ι n) (hP : 0 < P.projector.matrix.rank)
    (A : Learner ι Ω n) (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (loss : Density ι → Density ι → ℝ≥0∞) (ε v : ℝ≥0∞)
    (hgood : MeasurableSet {z : Frame ι (Fin 1) × Ω |
      loss z.1.density (A.estimator.estimate z.2) ≤ ε})
    (hvolume : ∀ τ : Density ι, μ {U | loss U.density τ ≤ ε} ≤ v) :
    (∫⁻ U, A.successProbability loss U.density ε ∂μ) ≤
      ((n + Fintype.card ι - 1).choose n : ℝ≥0∞) * v := by
  classical
  let G : Set (Frame ι (Fin 1) × Ω) :=
    {z | loss z.1.density (A.estimator.estimate z.2) ≤ ε}
  let f : Frame ι (Fin 1) × Ω → ℝ≥0∞ :=
    G.indicator (fun z => ENNReal.ofReal (A.born z.1.density z.2))
  let c : Ω → ℝ≥0∞ := fun y => (P.projector.matrix.rank : ℝ≥0∞) *
    ENNReal.ofReal (A.measurement.born (P.projector.flat hP) y)
  have hf : Measurable f :=
    ((measurable_joint_born A).ennreal_ofReal).indicator hgood
  have hc : Measurable c := measurable_const.mul
    (A.measurement.born_measurable _).ennreal_ofReal
  have hdom : ∀ᵐ y ∂A.measurement.reference, ∀ U : Frame ι (Fin 1),
      ENNReal.ofReal (A.born U.density y) ≤ c y := by
    filter_upwards [A.measurement.positive_ae] with y hy U
    have h := frame_tensor_effect_le P U (A.measurement.effect y) hy
    rw [trace_projector_eq_rank_mul_born P.projector hP A.measurement y] at h
    have hh := ENNReal.ofReal_le_ofReal h
    simpa only [A.born_eq_trace, TensorCopies.density, ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ENNReal.ofReal_natCast, c] using hh
  have hinner : ∀ᵐ y ∂A.measurement.reference,
      (∫⁻ U, f (U, y) ∂μ) ≤ c y * v := by
    filter_upwards [hdom] with y hy
    let S : Set (Frame ι (Fin 1)) := {U | loss U.density (A.estimator.estimate y) ≤ ε}
    calc
      _ ≤ ∫⁻ U, S.indicator (fun _ => c y) U ∂μ := by
        apply lintegral_mono
        intro U
        by_cases hU : U ∈ S
        · have hG : (U, y) ∈ G := hU
          change G.indicator _ (U, y) ≤ S.indicator _ U
          rw [Set.indicator_of_mem hG, Set.indicator_of_mem hU]
          exact hy U
        · have hG : (U, y) ∉ G := hU
          change G.indicator _ (U, y) ≤ S.indicator _ U
          rw [Set.indicator_of_notMem hG, Set.indicator_of_notMem hU]
      _ ≤ c y * μ S := lintegral_indicator_const_le S (c y)
      _ ≤ c y * v := mul_le_mul_left' (hvolume _) _
  have hcIntegral : (∫⁻ y, c y ∂A.measurement.reference) =
      (P.projector.matrix.rank : ℝ≥0∞) := by
    have hmean : (∫⁻ y, ENNReal.ofReal
        (A.measurement.born (P.projector.flat hP) y) ∂A.measurement.reference) = 1 := by
      rw [← ofReal_integral_eq_lintegral_ofReal
        (A.measurement.born_integrable (P.projector.flat hP))
        (A.measurement.born_nonneg_ae (P.projector.flat hP)),
        A.measurement.born_integral (P.projector.flat hP), ENNReal.ofReal_one]
    change (∫⁻ y, (P.projector.matrix.rank : ℝ≥0∞) *
      ENNReal.ofReal (A.measurement.born (P.projector.flat hP) y) ∂A.measurement.reference) = _
    rw [lintegral_const_mul _ (A.measurement.born_measurable (P.projector.flat hP)).ennreal_ofReal,
      hmean, mul_one]
  have hrepresentation : (∫⁻ U, A.successProbability loss U.density ε ∂μ) =
      ∫⁻ U, ∫⁻ y, f (U, y) ∂A.measurement.reference ∂μ := by
    apply lintegral_congr
    intro U
    have hmap : Measurable (fun y : Ω => (U, y)) := measurable_const.prodMk measurable_id
    have hs : MeasurableSet (A.successSet loss U.density ε) := by
      change MeasurableSet ((fun y : Ω => (U, y)) ⁻¹' G)
      exact hgood.preimage hmap
    rw [Learner.successProbability, A.outcomeMeasure_apply U.density hs]
    simpa only [f, G, Learner.successSet] using
      (lintegral_indicator hs (fun y => ENNReal.ofReal (A.born U.density y))).symm
  calc
    _ = ∫⁻ y, ∫⁻ U, f (U, y) ∂μ ∂A.measurement.reference := by
      rw [hrepresentation]
      exact lintegral_lintegral_swap (f := fun U y => f (U, y)) hf.aemeasurable
    _ ≤ ∫⁻ y, c y * v ∂A.measurement.reference := lintegral_mono_ae hinner
    _ = (∫⁻ y, c y ∂A.measurement.reference) * v :=
      lintegral_mul_const'' v hc.aemeasurable
    _ = ((n + Fintype.card ι - 1).choose n : ℝ≥0∞) * v := by
      rw [hcIntegral, P.dimension]

end Paper26.PureTensorSuccess
