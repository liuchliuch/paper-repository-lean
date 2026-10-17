import Paper38.PathEnergyEnvelope
import Paper38.GaussianMomentMismatch
import Paper38.SamplingMeasurability
import Paper38.ExpectedRates
import Paper38.MomentEnergy
import Paper38.ExternalAnalyticInputs

/-! Source expectation assembly from the proved deterministic oracle, actual
energy trapping, and explicit raw statistical baselines. These inputs are
separate from the final source theorem, which supplies the analytic proofs. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Matrix MatrixOrder
namespace Paper38.ExpectedMain
open Model Specification Sampling ExternalStatisticalInputs

variable {d : ℕ}
set_option maxHeartbeats 800000

lemma gaussian_initial_cov_posDef {N : ℕ} (hN : 0 < N) (μ : E d) (S0 : Mat d)
    (hS0 : S0.PosDef) (ω : Sampling.Sample d N) (hS : (covariance d N ω).PosDef) :
    (empiricalCovariance (gaussianCloud μ S0 N ω)).PosDef := by
  change (empiricalCovariance (GaussianLocalization.initialCloud μ (covarianceRoot S0) ω)).PosDef
  rw [(GaussianLocalization.initial_moments hN μ (covarianceRoot S0) ω).2]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hS.mul_mul_conjTranspose_same
      (Matrix.vecMul_injective_iff_isUnit.mpr hS0.posDef_sqrt.isUnit)

/-- The full expectation estimate for every a.e. actual solution family. The
oracle and energy-trapping premises are own analytic theorems, discharged by
the final assembly; only raw matching/concentration/moments are external. -/
theorem expected_pathSup (oracle : Specification.Theorem21)
    {V : E d → ℝ} {α β : ℝ} (hV : AdmissiblePotential V α β)
    (z : HilbertCoordinates.Tangent d) (hz : z ∈ HilbertCoordinates.Domain d)
    (hcrit : gradient (HilbertCoordinates.energy V) z = 0)
    (hstar : IsUniqueMinimizer V (HilbertCoordinates.toModel d z))
    (trapping : ∀ p : MomentPath d, momentSolution V p.mean p.cov →
      ∀ t : ℝ, 0 ≤ t → energy V (p.q t) ≤ energy V (p.q 0))
    (matching : Matching d) (mom : CovarianceMoments d) (conc : Concentration d)
    (μ0 : E d) (S0 : Mat d) (hS0 : S0.PosDef)
    (logs : InitializedMoments d μ0 S0 hS0) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, d+1 ≤ N →
      ∀ (p : MomentPath d) (X : Sampling.Sample d N → ParticlePath d N),
      IsMomentPathFrom V μ0 S0 p →
      (∀ᵐ ω ∂law d N, IsParticlePathFrom V (gaussianCloud μ0 S0 N ω) (X ω)) →
      (∫⁻ ω, pathSup (X ω) p ∂law d N) ≤ ENNReal.ofReal (C*rate d N) := by
  classical
  letI : NeZero d := ⟨by have := hV.dimension; omega⟩
  have hd : 1 ≤ d := hV.dimension
  obtain ⟨R, hR, hpop, hgoodR⟩ := GaussianLocalization.gaussian_good_common_sublevel
    hV μ0 S0 hS0 (HilbertCoordinates.toModel d z)
  obtain ⟨S,b,hS,hb,horacle⟩ := oracle d V α β hV
    (HilbertCoordinates.toModel d z) hstar R hR
  obtain ⟨Kshape,hKshape,hshape⟩ := StandardizedShape.expected_standardized_shape hd matching mom
  obtain ⟨Kenv,hKenv,henv⟩ := PathEnergyEnvelope.energy_trapped_paths_envelope hV z hz hcrit μ0 S0
  obtain ⟨L,hL,hbad⟩ := LogEnergyLocalization.weighted_bad_event_exponential
    μ0 S0 hS0 logs conc Kenv hKenv.le
  let M : ℝ := (d : ℝ)*(d+2)
  let a : ℝ := 2*S^2*GaussianMomentMismatch.mismatchConstant (covarianceRoot S0)
  let b' : ℝ := 2*b^2
  let C0 := a*M+b'*Kshape+L*(conc.c/2)⁻¹
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have ha : 0 ≤ a := by
    exact mul_nonneg (by positivity) (GaussianMomentMismatch.mismatchConstant_pos _).le
  have hb' : 0 ≤ b' := by dsimp [b']; positivity
  have hc : 0 < conc.c/2 := by linarith [conc.c_pos]
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  refine ⟨C0+1, by linarith, ?_⟩
  intro N hN p X hp hX
  have hNp : 0 < N := by omega
  have hpq : p.q 0 = (μ0,covarianceRoot S0) := by
    simp only [MomentPath.q, hp.2.1, hp.2.2]
  obtain ⟨H,hHm,hHz,hH⟩ := ExpectedRates.measurable_core (law d N)
    (fun ω => (covariance d N ω).PosDef ∧ IsParticlePathFrom V (gaussianCloud μ0 S0 N ω) (X ω))
    (by filter_upwards [mom.full_rank N hN, hX] with ω hr hx; exact ⟨hr,hx⟩)
  let f : Sampling.Sample d N → ℝ≥0∞ := fun ω => if ω ∈ H then pathSup (X ω) p else 0
  have hfae : f =ᵐ[law d N] (fun ω => pathSup (X ω) p) := by
    filter_upwards [show ∀ᵐ ω ∂law d N, ω ∈ H from hHz] with ω hω
    simp only [f, if_pos hω]
  have hgood : ∀ ω ∈ good d N, f ω ≤
      ENNReal.ofReal a * ENNReal.ofReal (defect d N ω) +
        ENNReal.ofReal b' * shapeError d N ω := by
    intro ω hω
    by_cases hωH : ω ∈ H
    · rcases hH ω hωH with ⟨hr,hx⟩
      have hSx := gaussian_initial_cov_posDef hNp μ0 S0 hS0 ω hr
      obtain ⟨_,_,hbound⟩ := horacle N μ0 S0 (gaussianCloud μ0 S0 N ω)
        hNp hS0 hSx hpop (hgoodR N hNp ω hω)
      have hw := GaussianLocalization.gaussianCloud_whitening hNp μ0 S0 hS0 ω hr
      let W := (covarianceRoot (covariance d N ω))⁻¹ * (covarianceRoot S0)⁻¹
      have h := hbound p (X ω) hp hx W hw.1
      rw [hpq, hw.2] at h
      have hm := GaussianMomentMismatch.good_moment_mismatch hNp μ0 (covarianceRoot S0)
        hS0.posDef_sqrt ω hω
      have hfirst : ENNReal.ofReal (2*S^2*coordinateSqDist
          (cloudQ (gaussianCloud μ0 S0 N ω)) (μ0,covarianceRoot S0)) ≤
          ENNReal.ofReal a * ENNReal.ofReal (defect d N ω) := by
        rw [← ENNReal.ofReal_mul ha]
        apply ENNReal.ofReal_le_ofReal
        exact (mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 2*S^2)).trans_eq (by dsimp [a]; ring)
      simpa only [f, if_pos hωH, b', shapeError, shapeLaw] using
        h.trans (add_le_add_right hfirst _)
    · simp only [f, if_neg hωH]; exact zero_le _
  have hbad' : (∫⁻ ω in (good d N)ᶜ, f ω ∂law d N) ≤
      ENNReal.ofReal (L*Real.exp (-(conc.c/2)*N)) := by
    apply hbad N hN f
    intro ω hω
    by_cases hωH : ω ∈ H
    · rcases hH ω hωH with ⟨hr,hx⟩
      let px : MomentPath d := ⟨fun t => empiricalMean (X ω t), fun t => empiricalCovariance (X ω t)⟩
      have hpx : momentSolution V px.mean px.cov :=
        ModelBridges.particleSolution_momentSolution V hV.regularity hNp (X ω) hx.1
      have htP : ∀ t, 0 ≤ t → energy V (p.q t) ≤ energy V (μ0,covarianceRoot S0) := by
        intro t ht
        simpa only [hpq] using trapping p hp.1 t ht
      have htX : ∀ t, 0 ≤ t → energy V (cloudQ (X ω t)) ≤
          energy V (cloudQ (gaussianCloud μ0 S0 N ω)) := by
        intro t ht
        have h := trapping px hpx t ht
        change energy V (cloudQ (X ω t)) ≤ energy V (cloudQ (X ω 0)) at h
        simpa only [hx.2] using h
      have h := henv N hNp ω p (X ω) hp.1.1 hx.1.1
        (gaussian_initial_cov_posDef hNp μ0 S0 hS0 ω hr) htP htX
      simpa only [f, if_pos hωH, ENNReal.ofReal_mul hKenv.le] using h
    · simp only [f, if_neg hωH]; exact zero_le _
  have hraw := ExpectedRates.good_bad_rate (law d N) (good d N) (conc.good_measurable N)
    f (fun ω => ENNReal.ofReal (defect d N ω)) (shapeError d N)
    (defect_measurable d N).ennreal_ofReal d N hd (by omega)
    a b' M Kshape L (conc.c/2) ha hb' hM hKshape.le hL hc hgood
    ((setLIntegral_le_lintegral _ _).trans (StandardizedShape.expected_defect hd hN mom))
    (hshape N hN) hbad'
  rw [lintegral_congr_ae hfae] at hraw
  exact hraw.trans (ENNReal.ofReal_le_ofReal (by
    change C0*rate d N ≤ (C0+1)*rate d N
    nlinarith [rate_pos d N hd (by omega)]))

/-- The general analytic prerequisites of the expectation assembly are all
discharged for the source Gaussian SVGD energy; the sole remaining analytic
argument here is the already proved complete source oracle. -/
theorem expected_pathSup_from_analysis (oracle : Specification.Theorem21)
    (extern : ExternalAnalyticInputs.Baselines d)
    {V : E d → ℝ} {α β : ℝ} (hV : AdmissiblePotential V α β)
    (matching : Matching d) (mom : CovarianceMoments d) (conc : Concentration d)
    (μ0 : E d) (S0 : Mat d) (hS0 : S0.PosDef)
    (logs : InitializedMoments d μ0 S0 hS0) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, d+1 ≤ N →
      ∀ (p : MomentPath d) (X : Sampling.Sample d N → ParticlePath d N),
      IsMomentPathFrom V μ0 S0 p →
      (∀ᵐ ω ∂law d N, IsParticlePathFrom V (gaussianCloud μ0 S0 N ω) (X ω)) →
      (∫⁻ ω, pathSup (X ω) p ∂law d N) ≤ ENNReal.ofReal (C*rate d N) := by
  obtain ⟨z,hz,hcrit,hstar⟩ := GaussianGradientFlow.exists_unique_minimizer hV
  exact expected_pathSup oracle hV z hz hcrit hstar
    (fun p hp t ht => MomentEnergy.energy_nonincreasing extern.stein extern.sqrt hV p hp t ht)
    matching mom conc μ0 S0 hS0 logs

end Paper38.ExpectedMain
