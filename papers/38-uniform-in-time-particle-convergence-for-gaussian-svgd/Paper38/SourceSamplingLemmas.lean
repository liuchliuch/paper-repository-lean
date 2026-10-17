import Paper38.HighProbabilityMain
import Paper38.PathEnergyEnvelope

/-!
# Complete source contracts for Lemmas 6.2, 7.1 and 7.2

These wrappers keep the original sample space, actual Gaussian initialization,
physical-time supremum and all uniformity quantifiers. The weighted exceptional
event estimate derives actual trajectory trapping from the proved moment ODE
geometry; no trajectory envelope or final particle error is an external input.
-/
noncomputable section
open MeasureTheory Set
open scoped BigOperators Matrix MatrixOrder ENNReal
namespace Paper38.SourceSamplingLemmas
open Model Specification ExternalStatisticalInputs

variable {d : ℕ}

/-- Complete Lemma 6.2: the exact standardized-cloud identity and inequality
hold on the almost-sure full-rank event, and one C_d precedes all N≥d+1. -/
theorem lemma62 (hd : 1 ≤ d) (matching : Matching d) (mom : CovarianceMoments d) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, d+1 ≤ N →
      (∀ᵐ ω ∂Sampling.law d N,
        ((N:ℝ)⁻¹*∑ i, ‖Sampling.standardized d N ω i-Sampling.cloud d N ω i‖^2 =
          frobSq (1-covarianceRoot (Sampling.covariance d N ω))+‖Sampling.mean d N ω‖^2) ∧
        ((N:ℝ)⁻¹*∑ i, ‖Sampling.standardized d N ω i-Sampling.cloud d N ω i‖^2 ≤
          frobSq (1-Sampling.covariance d N ω)+‖Sampling.mean d N ω‖^2)) ∧
      (∫⁻ ω, Sampling.shapeError d N ω ∂Sampling.law d N) ≤
        ENNReal.ofReal (C*rate d N) := by
  obtain ⟨C,hC,hshape⟩ := StandardizedShape.expected_standardized_shape hd matching mom
  refine ⟨C,hC,?_⟩
  intro N hN
  refine ⟨?_,hshape N hN⟩
  filter_upwards [mom.full_rank N hN] with ω hω
  exact ModelBridges.principal_standardized_identity_and_bound
    (lt_of_lt_of_le (Nat.succ_pos d) hN) (Sampling.cloud d N ω) hω

/-- Complete Lemma 7.1: tail constants depend only on the raw dimension input;
one deterministic R and one moment constant precede every sample count. The
restricted integral is exactly expectation weighted by the good-event indicator. -/
theorem lemma71 {V : E d → ℝ} {α β : ℝ} (hV : AdmissiblePotential V α β)
    (mom : CovarianceMoments d) (conc : Concentration d)
    (μ0 : E d) (S0 : Mat d) (hS0 : S0.PosDef)
    (qstar : Coordinates d) (_hstar : IsUniqueMinimizer V qstar) :
    ∃ Cd cd R C : ℝ, 0 < Cd ∧ 0 < cd ∧ 0 ≤ R ∧ 0 < C ∧
      ∀ N : ℕ, d+1 ≤ N →
        Sampling.law d N (Sampling.good d N)ᶜ ≤ ENNReal.ofReal (Cd*Real.exp (-cd*N)) ∧
        (μ0,covarianceRoot S0) ∈ sublevel V qstar R ∧
        (∀ ω ∈ Sampling.good d N,
          cloudQ (gaussianCloud μ0 S0 N ω) ∈ sublevel V qstar R) ∧
        (∫⁻ ω in Sampling.good d N,
          ENNReal.ofReal (coordinateSqDist (cloudQ (gaussianCloud μ0 S0 N ω))
            (μ0,covarianceRoot S0)) ∂Sampling.law d N) ≤ ENNReal.ofReal (C/N) := by
  letI : NeZero d := ⟨by have := hV.dimension; omega⟩
  obtain ⟨R,hR,hpop,hcloud⟩ := GaussianLocalization.gaussian_good_common_sublevel
    hV μ0 S0 hS0 qstar
  obtain ⟨C,hC,hmoment⟩ := GaussianMomentMismatch.expected_good_gaussian_moment_mismatch
    hV.dimension mom conc μ0 S0 hS0
  refine ⟨conc.C,conc.c,R,C,conc.C_pos,conc.c_pos,hR,hC,?_⟩
  intro N hN
  exact ⟨conc.good_tail N hN,hpop,
    hcloud N (lt_of_lt_of_le (Nat.succ_pos d) hN),hmoment N hN⟩

/-- Complete Lemma 7.2 for every a.e. actual particle family and every actual
population path. Constants precede N, the supplied trajectories and all times.
Only the named standard analysis and raw covariance/concentration/log moments
are supplied as external baseline inputs. -/
theorem lemma72 (extern : ExternalAnalyticInputs.Baselines d)
    (stats : ExternalStatisticalInputs.Baselines d)
    {V : E d → ℝ} {α β : ℝ} (hV : AdmissiblePotential V α β)
    (μ0 : E d) (S0 : Mat d) (hS0 : S0.PosDef) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ N : ℕ, d+1 ≤ N →
      ∀ (p : MomentPath d) (X : Specification.Sample d N → ParticlePath d N),
        IsMomentPathFrom V μ0 S0 p →
        (∀ᵐ ω ∂sampleLaw d N, IsParticlePathFrom V (gaussianCloud μ0 S0 N ω) (X ω)) →
        (∫⁻ ω in (Sampling.good d N)ᶜ, pathSup (X ω) p ∂sampleLaw d N) ≤
          ENNReal.ofReal (C*Real.exp (-c*N)) := by
  classical
  obtain ⟨z,hz,hcrit,hstar⟩ := GaussianGradientFlow.exists_unique_minimizer hV
  obtain ⟨K,hK,henv⟩ := PathEnergyEnvelope.energy_trapped_paths_envelope hV z hz hcrit μ0 S0
  obtain ⟨L,hL,hbad⟩ := LogEnergyLocalization.weighted_bad_event_exponential
    μ0 S0 hS0 (stats.initialized μ0 S0 hS0) stats.concentration K hK.le
  refine ⟨L+1,stats.concentration.c/2,by linarith,by linarith [stats.concentration.c_pos],?_⟩
  intro N hN p X hp hX
  have hNp : 0 < N := lt_of_lt_of_le (Nat.succ_pos d) hN
  have hpq : p.q 0 = (μ0,covarianceRoot S0) := by simp only [MomentPath.q,hp.2.1,hp.2.2]
  obtain ⟨H,hH,hHz,hpath⟩ := ExpectedRates.measurable_core (Sampling.law d N)
    (fun ω => (Sampling.covariance d N ω).PosDef ∧
      IsParticlePathFrom V (gaussianCloud μ0 S0 N ω) (X ω))
    (by filter_upwards [stats.covariance.full_rank N hN,hX] with ω hω hωX; exact ⟨hω,hωX⟩)
  let f : Specification.Sample d N → ℝ≥0∞ := fun ω => if ω ∈ H then pathSup (X ω) p else 0
  have hfae : f =ᵐ[Sampling.law d N] (fun ω => pathSup (X ω) p) := by
    filter_upwards [show ∀ᵐ ω ∂Sampling.law d N, ω ∈ H from hHz] with ω hω
    simp only [f,if_pos hω]
  have hweighted := hbad N hN f (by
    intro ω hω
    by_cases hωH : ω ∈ H
    · rcases hpath ω hωH with ⟨hr,hx⟩
      let px : MomentPath d := ⟨fun t => empiricalMean (X ω t),fun t => empiricalCovariance (X ω t)⟩
      have hpx : momentSolution V px.mean px.cov :=
        ModelBridges.particleSolution_momentSolution V hV.regularity hNp (X ω) hx.1
      have hpE : ∀ t, 0 ≤ t → energy V (p.q t) ≤ energy V (μ0,covarianceRoot S0) := by
        intro t ht
        simpa only [hpq] using MomentEnergy.energy_nonincreasing extern.stein extern.sqrt hV p hp.1 t ht
      have hxE : ∀ t, 0 ≤ t → energy V (cloudQ (X ω t)) ≤
          energy V (cloudQ (gaussianCloud μ0 S0 N ω)) := by
        intro t ht
        have h := MomentEnergy.energy_nonincreasing extern.stein extern.sqrt hV px hpx t ht
        change energy V (cloudQ (X ω t)) ≤ energy V (cloudQ (X ω 0)) at h
        simpa only [hx.2] using h
      have hcov := HighProbabilityMain.gaussianCloud_covariance_posDef hNp μ0 S0 hS0 ω hr
      have h := henv N hNp ω p (X ω) hp.1.1 hx.1.1 hcov hpE hxE
      simpa only [f,if_pos hωH,ENNReal.ofReal_mul hK.le] using h
    · simp only [f,if_neg hωH]; exact zero_le _)
  rw [lintegral_congr_ae (ae_restrict_of_ae hfae)] at hweighted
  exact hweighted.trans (ENNReal.ofReal_le_ofReal (by
    have h := Real.exp_pos (-(stats.concentration.c/2)*(N:ℝ))
    nlinarith))

end Paper38.SourceSamplingLemmas
