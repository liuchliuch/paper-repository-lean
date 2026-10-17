import Paper38.ExternalStatisticalInputs
import Paper38.ProbabilityAssembly
import Paper38.ModelBridges

/-! Own logarithmic-energy localization: combine three separate raw Gaussian
moments into (7.16) and apply genuine exceptional-event Cauchy--Schwarz.
The source trajectory energy envelope is a distinct analytic prerequisite. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Paper38.LogEnergyLocalization
open Model Sampling ExternalStatisticalInputs

lemma initialEnvelope_one_le {d N : ℕ} (μ0 : E d) (S0 : Mat d) (ω : Sample d N) :
    1 ≤ initialEnvelope μ0 S0 N ω := by
  have ht := (ModelBridges.empiricalCovariance_posSemidef
    (Specification.gaussianCloud μ0 S0 N ω)).trace_nonneg
  have hm := sq_nonneg ‖empiricalMean (Specification.gaussianCloud μ0 S0 N ω)‖
  have hl := le_max_right (-Real.log (empiricalCovariance
    (Specification.gaussianCloud μ0 S0 N ω)).det) 0
  change 1 ≤ 1+‖empiricalMean (Specification.gaussianCloud μ0 S0 N ω)‖^2+
    (empiricalCovariance (Specification.gaussianCloud μ0 S0 N ω)).trace+
    max (-Real.log (empiricalCovariance (Specification.gaussianCloud μ0 S0 N ω)).det) 0
  linarith

lemma four_term_square (a b c : ℝ) :
    (1 + a + b + c) ^ 2 ≤ 4 * (1 + a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (1 - a), sq_nonneg (1 - b), sq_nonneg (1 - c),
    sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]

/-- The uniform second moment (7.16) is proved by combining the separate raw
mean/trace/logdet moment inputs. No inverse-covariance moment is used. -/
theorem initialEnvelope_secondMoment {d : ℕ} (μ0 : E d) (S0 : Mat d) (hS0 : S0.PosDef)
    (mom : InitializedMoments d μ0 S0 hS0) :
    ∃ M : ℝ, 0 < M ∧ ∀ N : ℕ, d + 1 ≤ N →
      (∫⁻ ω, ENNReal.ofReal (initialEnvelope μ0 S0 N ω ^ 2) ∂law d N) ≤
        ENNReal.ofReal M := by
  let M := 4 * (1 + mom.meanConstant + mom.traceConstant + mom.logConstant)
  have ha := mom.meanConstant_nonneg
  have hb := mom.traceConstant_nonneg
  have hc := mom.logConstant_nonneg
  refine ⟨M, by dsimp [M]; nlinarith, ?_⟩
  intro N hN
  have hm1 := ((mom.mean_measurable N).pow_const 2).ennreal_ofReal
  have hm2 := ((mom.trace_measurable N).pow_const 2).ennreal_ofReal
  have hm3 := ((mom.log_measurable N).pow_const 2).ennreal_ofReal
  have hpoint : ∀ ω : Sample d N,
      ENNReal.ofReal (initialEnvelope μ0 S0 N ω ^ 2) ≤
        4 * (1 + ENNReal.ofReal (initializedMeanSq μ0 S0 N ω ^ 2) +
          ENNReal.ofReal (initializedTrace μ0 S0 N ω ^ 2) +
          ENNReal.ofReal (initializedLog μ0 S0 N ω ^ 2)) := by
    intro ω
    have h := ENNReal.ofReal_le_ofReal (four_term_square
      (initializedMeanSq μ0 S0 N ω) (initializedTrace μ0 S0 N ω) (initializedLog μ0 S0 N ω))
    have hadd : ENNReal.ofReal (1 + initializedMeanSq μ0 S0 N ω ^ 2 +
        initializedTrace μ0 S0 N ω ^ 2 + initializedLog μ0 S0 N ω ^ 2) =
        1 + ENNReal.ofReal (initializedMeanSq μ0 S0 N ω ^ 2) +
        ENNReal.ofReal (initializedTrace μ0 S0 N ω ^ 2) +
        ENNReal.ofReal (initializedLog μ0 S0 N ω ^ 2) := by
      rw [ENNReal.ofReal_add (by positivity) (sq_nonneg _),
        ENNReal.ofReal_add (by positivity) (sq_nonneg _),
        ENNReal.ofReal_add (by norm_num) (sq_nonneg _), ENNReal.ofReal_one]
    simpa only [initialEnvelope, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
      hadd, ENNReal.ofReal_ofNat] using h
  calc
    _ ≤ ∫⁻ ω, 4 * (1 + ENNReal.ofReal (initializedMeanSq μ0 S0 N ω ^ 2) +
          ENNReal.ofReal (initializedTrace μ0 S0 N ω ^ 2) +
          ENNReal.ofReal (initializedLog μ0 S0 N ω ^ 2)) ∂law d N := lintegral_mono hpoint
    _ = 4 * (1 + (∫⁻ ω, ENNReal.ofReal (initializedMeanSq μ0 S0 N ω ^ 2) ∂law d N) +
          (∫⁻ ω, ENNReal.ofReal (initializedTrace μ0 S0 N ω ^ 2) ∂law d N) +
          (∫⁻ ω, ENNReal.ofReal (initializedLog μ0 S0 N ω ^ 2) ∂law d N)) := by
      rw [lintegral_const_mul' 4 _ (by simp), lintegral_add_right _ hm3,
        lintegral_add_right _ hm2, lintegral_add_right _ hm1]
      simp
    _ ≤ 4 * (1 + ENNReal.ofReal mom.meanConstant + ENNReal.ofReal mom.traceConstant +
        ENNReal.ofReal mom.logConstant) := by
      exact mul_le_mul_left' (add_le_add
        (add_le_add (add_le_add_left (mom.mean_fourth N hN) 1) (mom.trace_second N hN))
        (mom.log_second N hN)) 4
    _ = _ := by
      dsimp [M]
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (by positivity) hc,
        ENNReal.ofReal_add (by positivity) hb, ENNReal.ofReal_add (by positivity) ha]
      norm_num

/-- Exceptional-event weighting before the final real exponential simplification.
The measurable envelope is the actual initial sample-energy quantity (7.15). -/
theorem weighted_bad_event {d N : ℕ} (μ0 : E d) (S0 : Mat d)
    (P : Measure (Sample d N)) (G : Set (Sample d N)) (hG : MeasurableSet G)
    (f : Sample d N → ℝ≥0∞) (K : ℝ≥0∞)
    (hZ : Measurable (fun ω => ENNReal.ofReal (initialEnvelope μ0 S0 N ω)))
    (hpath : ∀ ω ∈ Gᶜ, f ω ≤ K * ENNReal.ofReal (initialEnvelope μ0 S0 N ω)) :
    (∫⁻ ω in Gᶜ, f ω ∂P) ≤
      K * ((P Gᶜ) ^ (1 / 2 : ℝ) *
        (∫⁻ ω, ENNReal.ofReal (initialEnvelope μ0 S0 N ω) ^ 2 ∂P) ^ (1 / 2 : ℝ)) :=
  ProbabilityAssembly.exceptional_event_envelope P Gᶜ hG.compl f _ hZ K hpath

/-- The exponentially weighted bad-event estimate (7.11), derived from the
raw concentration and log-Wishart moments and the actual pathwise envelope. -/
theorem weighted_bad_event_exponential {d : ℕ} (μ0 : E d) (S0 : Mat d)
    (hS0 : S0.PosDef) (mom : InitializedMoments d μ0 S0 hS0)
    (conc : Concentration d) (K : ℝ) (hK : 0 ≤ K) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ N : ℕ, d+1 ≤ N →
      ∀ f : Sample d N → ℝ≥0∞,
      (∀ ω ∈ (good d N)ᶜ, f ω ≤
        ENNReal.ofReal K * ENNReal.ofReal (initialEnvelope μ0 S0 N ω)) →
      (∫⁻ ω in (good d N)ᶜ, f ω ∂law d N) ≤
        ENNReal.ofReal (L * Real.exp (-(conc.c/2) * N)) := by
  obtain ⟨M, hM, hmoment⟩ := initialEnvelope_secondMoment μ0 S0 hS0 mom
  let L := K * (conc.C ^ (1/2 : ℝ) * M ^ (1/2 : ℝ))
  refine ⟨L, by dsimp [L]; exact mul_nonneg hK (mul_nonneg (Real.rpow_nonneg conc.C_pos.le _) (Real.rpow_nonneg hM.le _)), ?_⟩
  intro N hN f hpath
  have hZ : Measurable (fun ω => ENNReal.ofReal (initialEnvelope μ0 S0 N ω)) :=
    (((measurable_const.add (mom.mean_measurable N)).add
      (mom.trace_measurable N)).add (mom.log_measurable N)).ennreal_ofReal
  have hZpow : (∫⁻ ω, ENNReal.ofReal (initialEnvelope μ0 S0 N ω) ^ 2 ∂law d N) ≤
      ENNReal.ofReal M := by
    convert hmoment N hN using 1
    congr 1
    funext ω
    exact (ENNReal.ofReal_pow (by linarith [initialEnvelope_one_le μ0 S0 ω]) 2).symm
  have htail := ENNReal.rpow_le_rpow (conc.good_tail N hN) (by norm_num : (0 : ℝ) ≤ 1/2)
  have hmp := ENNReal.rpow_le_rpow hZpow (by norm_num : (0 : ℝ) ≤ 1/2)
  calc
    _ ≤ ENNReal.ofReal K * ((law d N (good d N)ᶜ) ^ (1/2 : ℝ) *
        (∫⁻ ω, ENNReal.ofReal (initialEnvelope μ0 S0 N ω)^2 ∂law d N) ^ (1/2 : ℝ)) :=
      weighted_bad_event μ0 S0 (law d N) (good d N) (conc.good_measurable N)
        f (ENNReal.ofReal K) hZ hpath
    _ ≤ ENNReal.ofReal K * ((ENNReal.ofReal (conc.C*Real.exp (-conc.c*N))) ^ (1/2 : ℝ) *
        (ENNReal.ofReal M) ^ (1/2 : ℝ)) :=
      mul_le_mul_left' (mul_le_mul' htail hmp) _
    _ = _ := by
      rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg conc.C_pos.le (Real.exp_pos _).le) (by norm_num),
        ENNReal.ofReal_rpow_of_nonneg hM.le (by norm_num),
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (mul_nonneg conc.C_pos.le (Real.exp_pos _).le) _), ← ENNReal.ofReal_mul hK]
      congr 1
      rw [Real.mul_rpow conc.C_pos.le (Real.exp_pos _).le, ← Real.exp_mul]
      have he : (-conc.c * (N : ℝ)) * (1/2) = -(conc.c/2)*N := by ring
      rw [he]
      dsimp [L]
      ring

end Paper38.LogEnergyLocalization
