import Paper38.ExternalStatisticalInputs
import Paper38.ModelBridges
import Paper38.TransportGluing
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! The paper's standardization argument is proved from raw Gaussian matching
and raw covariance moments. The statistical inputs contain no standardized
shape or particle-flow conclusion. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace Paper38.StandardizedShape
open Model Sampling ExternalStatisticalInputs

variable {d N : ℕ}

lemma empirical_coupling_cost (hN : 0 < N) (x y : Fin N → E d) :
    Transport.w2sq (empiricalLaw x) (empiricalLaw y) ≤
      ENNReal.ofReal ((N : ℝ)⁻¹ * ∑ i, ‖x i - y i‖ ^ 2) := by
  rw [GaussianCoupling.empiricalLaw_eq_transport_empirical hN,
    GaussianCoupling.empiricalLaw_eq_transport_empirical hN]
  have h := Transport.indexed_coupling_upper x y
  have hNr : 0 ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg N)
  rw [ENNReal.ofReal_mul hNr,
    ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg ‖x i - y i‖)]
  rw [ENNReal.ofReal_inv_of_pos (by exact_mod_cast hN), ENNReal.ofReal_natCast]
  simpa only [Fintype.card_fin, edist_dist, dist_eq_norm,
    ENNReal.ofReal_pow (norm_nonneg _)] using h

/-- The pathwise, distribution-free part of Lemma6.2. -/
theorem shape_bound (hN : 0 < N) (x : Fin N → E d)
    (hS : (empiricalCovariance x).PosDef) :
    let z := standardizedCloud x (covarianceRoot (empiricalCovariance x))⁻¹
    Transport.w2sq (empiricalLaw z) (standardGaussian d) ≤
      2 * ENNReal.ofReal (frobSq (1 - empiricalCovariance x) + ‖empiricalMean x‖ ^ 2) +
        2 * Transport.w2sq (empiricalLaw x) (standardGaussian d) := by
  dsimp only
  let z := standardizedCloud x (covarianceRoot (empiricalCovariance x))⁻¹
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  letI : IsProbabilityMeasure (standardGaussian d) := GaussianCoupling.standardGaussian_probability d
  letI : IsProbabilityMeasure (empiricalLaw x) := by
    rw [GaussianCoupling.empiricalLaw_eq_transport_empirical hN]; infer_instance
  letI : IsProbabilityMeasure (empiricalLaw z) := by
    rw [GaussianCoupling.empiricalLaw_eq_transport_empirical hN]; infer_instance
  have hc := empirical_coupling_cost hN z x
  have hs := (ModelBridges.principal_standardized_identity_and_bound hN x hS).2
  have hcost : Transport.w2sq (empiricalLaw z) (empiricalLaw x) ≤
      ENNReal.ofReal (frobSq (1 - empiricalCovariance x) + ‖empiricalMean x‖ ^ 2) :=
    hc.trans (ENNReal.ofReal_le_ofReal hs)
  exact (Transport.w2sq_triangle (empiricalLaw z) (empiricalLaw x) (standardGaussian d)).trans
    (add_le_add (mul_le_mul_left' hcost 2) le_rfl)

lemma mean_eq_sampleMean (ω : Sample d N) :
    mean d N ω = GaussianStatistics.sampleMean ω := by
  ext j
  simp [mean, cloud, empiricalMean, vec, GaussianStatistics.sampleMean,
    GaussianStatistics.sampleMeanCoord, Finset.mul_sum]
  change (N : ℝ)⁻¹ * ((WithLp.linearEquiv 2 ℝ (Fin d → ℝ))
    (∑ i : Fin N, WithLp.toLp 2 (fun j => ω (i,j)))) j = _
  rw [map_sum]
  simp [Finset.sum_apply, Finset.mul_sum]

lemma mean_norm_sq_integrable : Integrable (fun ω : Sample d N => ‖mean d N ω‖ ^ 2) (law d N) := by
  simp_rw [mean_eq_sampleMean, EuclideanSpace.norm_sq_eq,
    GaussianStatistics.sampleMean, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]
  exact integrable_finset_sum _ (fun j _ =>
    (GaussianStatistics.sampleMeanCoord_memLp j).integrable_sq)

lemma expected_defect (hd : 1 ≤ d) (hN : d + 1 ≤ N) (mom : CovarianceMoments d) :
    (∫⁻ ω, ENNReal.ofReal (defect d N ω) ∂law d N) ≤
      ENNReal.ofReal (((d : ℝ) * (d + 2)) / N) := by
  have hNpos : 0 < N := lt_of_lt_of_le (Nat.succ_pos d) hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hcov := mom.integrable N hN
  have hm := mean_norm_sq_integrable (d := d) (N := N)
  have hdef : Integrable (defect d N) (law d N) := hcov.add hm
  rw [← ofReal_integral_eq_lintegral_ofReal hdef
    (Filter.Eventually.of_forall (defect_nonneg d N))]
  apply ENNReal.ofReal_le_ofReal
  rw [show (defect d N) = (fun ω => frobSq (1 - covariance d N ω) + ‖mean d N ω‖ ^ 2) from rfl,
    integral_add hcov hm, mom.exact_secondMoment N hN]
  have hmval : (∫ ω, ‖mean d N ω‖ ^ 2 ∂law d N) = (d : ℝ) / N := by
    simp_rw [mean_eq_sampleMean]
    exact GaussianStatistics.sampleMean_secondMoment hNpos.ne'
  rw [hmval]
  apply (le_div_iff₀ hNr).2
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hN0 : (N : ℝ) ≠ 0 := hNr.ne'
  field_simp
  nlinarith [sq_nonneg (d : ℝ)]

/-- Equation (6.10), with a constant chosen before N, under the explicitly
retained raw external matching and Wishart-moment inputs. -/
theorem expected_standardized_shape (hd : 1 ≤ d)
    (matching : Matching d) (mom : CovarianceMoments d) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, d + 1 ≤ N →
      (∫⁻ ω, shapeError d N ω ∂law d N) ≤ ENNReal.ofReal (C * rate d N) := by
  let D : ℝ := (d : ℝ) * (d + 2)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hu := matching.upper_pos
  refine ⟨2 * D + 2 * matching.upperConstant, by nlinarith, ?_⟩
  intro N hN
  have hNpos : 0 < N := lt_of_lt_of_le (Nat.succ_pos d) hN
  have hdefI : Integrable (defect d N) (law d N) :=
    (mom.integrable N hN).add mean_norm_sq_integrable
  have hbound : (∫⁻ ω, shapeError d N ω ∂law d N) ≤
      ∫⁻ ω, 2 * ENNReal.ofReal (defect d N ω) + 2 * rawError d N ω ∂law d N := by
    apply lintegral_mono_ae
    filter_upwards [mom.full_rank N hN] with ω hω
    exact shape_bound hNpos (cloud d N ω) hω
  have hdefMeas := hdefI.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  calc
    _ ≤ _ := hbound
    _ = 2 * (∫⁻ ω, ENNReal.ofReal (defect d N ω) ∂law d N) +
        2 * (∫⁻ ω, rawError d N ω ∂law d N) := by
      rw [lintegral_add_left' (hdefMeas.const_mul 2),
        lintegral_const_mul' 2 _ (by simp), lintegral_const_mul' 2 _ (by simp)]
    _ ≤ 2 * ENNReal.ofReal (D / N) +
        2 * ENNReal.ofReal (matching.upperConstant * rate d N) :=
      add_le_add (mul_le_mul_left' (expected_defect hd hN mom) 2)
        (mul_le_mul_left' (matching.expected_upper N hN) 2)
    _ ≤ ENNReal.ofReal ((2 * D + 2 * matching.upperConstant) * rate d N) := by
      have hrate := Model.inv_sampleSize_le_rate d N hd hNpos
      have hpart : D / N ≤ D * rate d N := by
        simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hrate hD
      calc
        _ ≤ 2 * ENNReal.ofReal (D * rate d N) +
            2 * ENNReal.ofReal (matching.upperConstant * rate d N) :=
          add_le_add (mul_le_mul_left' (ENNReal.ofReal_le_ofReal hpart) 2) le_rfl
        _ = _ := by
          have hr := Model.rate_pos d N hd hNpos
          rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num]
          rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
            ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring

end Paper38.StandardizedShape
