import Paper38.ExpectedMain
import Paper38.SourceMomentFlow
import Paper38.SourceFlowMeasurability

/-! The literal source expectation and physical-time last-iterate contracts.
The analytic and statistical baseline statements are ordinary explicit inputs;
every Gaussian SVGD, localization and probability-assembly step is supplied by
the own theorems imported above. -/
noncomputable section
open MeasureTheory
open scoped ENNReal Matrix MatrixOrder
namespace Paper38.SourceExpected
open Model Specification

/-- The physical balancing time stated after (2.16), with the exact log-plus
threshold and the source rate, including small sample sizes. -/
theorem exp_le_rate_at_balancing_time {r c t : ℝ} (hr : 0 < r) (hc : 0 < c)
    (ht : (2*c)⁻¹ * max (Real.log (1/r)) 0 ≤ t) : Real.exp (-2*c*t) ≤ r := by
  have h2c : 0 < 2*c := by positivity
  have hm := mul_le_mul_of_nonneg_left ht h2c.le
  have he : (2*c)*((2*c)⁻¹*max (Real.log (1/r)) 0) = max (Real.log (1/r)) 0 := by
    rw [← mul_assoc, mul_inv_cancel₀ h2c.ne', one_mul]
  rw [he] at hm
  have hl : -Real.log r ≤ max (Real.log (1/r)) 0 := by
    simpa only [one_div, Real.log_inv] using le_max_left (Real.log (1/r)) 0
  calc
    Real.exp (-2*c*t) ≤ Real.exp (Real.log r) := Real.exp_le_exp.mpr (by nlinarith)
    _ = r := Real.exp_log hr

/-- Theorem2.2, including a genuinely measurable all-time error and global
actual particle trajectories on the full-rank probability-one event. -/
theorem theorem22 (oracle : Specification.Theorem21)
    (extern : ∀ d : ℕ, ExternalAnalyticInputs.Baselines d)
    (stats : ∀ d : ℕ, 1 ≤ d → ExternalStatisticalInputs.Baselines d) : Specification.Theorem22 := by
  intro d V α β hV μ0 S0 hS0
  obtain ⟨p,hp,_⟩ := SourceMomentFlow.momentWellPosed (extern d) hV μ0 S0 hS0
  obtain ⟨C,hC,hbound⟩ := ExpectedMain.expected_pathSup_from_analysis oracle (extern d) hV
    (stats d hV.dimension).matching (stats d hV.dimension).covariance (stats d hV.dimension).concentration μ0 S0 hS0
    ((stats d hV.dimension).initialized μ0 S0 hS0)
  refine ⟨p,C,hC,hp,?_⟩
  intro N hN
  have hNp : 0 < N := by omega
  have hfull : ∀ᵐ ω ∂sampleLaw d N,
      (empiricalCovariance (gaussianCloud μ0 S0 N ω)).PosDef := by
    filter_upwards [(stats d hV.dimension).covariance.full_rank N hN] with ω hω
    exact ExpectedMain.gaussian_initial_cov_posDef hNp μ0 S0 hS0 ω hω
  obtain ⟨X,hX,hmeas⟩ := SourceFlowMeasurability.exists_measurable_particle_family
    (extern d) hV hNp μ0 S0 p hp.1
  have hXae : ∀ᵐ ω ∂sampleLaw d N,
      IsParticlePathFrom V (gaussianCloud μ0 S0 N ω) (X ω) := by
    filter_upwards [hfull] with ω hω
    exact hX ω hω
  exact ⟨hfull,X,hXae,hmeas,hbound N hN p X hp hXae⟩

/-- Corollary2.5 for every a.e. actual source particle family, with one pair of
constants fixed before N and physical time. -/
theorem corollary25 (oracle : Specification.Theorem21)
    (extern : ∀ d : ℕ, ExternalAnalyticInputs.Baselines d)
    (stats : ∀ d : ℕ, 1 ≤ d → ExternalStatisticalInputs.Baselines d) : Specification.Corollary25 := by
  intro d V α β hV qstar hstar μ0 S0 hS0
  obtain ⟨p,hp,_⟩ := SourceMomentFlow.momentWellPosed (extern d) hV μ0 S0 hS0
  obtain ⟨C,hC,hbound⟩ := ExpectedMain.expected_pathSup_from_analysis oracle (extern d) hV
    (stats d hV.dimension).matching (stats d hV.dimension).covariance (stats d hV.dimension).concentration μ0 S0 hS0
    ((stats d hV.dimension).initialized μ0 S0 hS0)
  let R := max 0 (energy V (μ0,covarianceRoot S0)-energy V qstar)
  have hR : 0 ≤ R := le_max_left _ _
  have hpR : p.q 0 ∈ sublevel V qstar R := by
    constructor
    · exact (hp.1.1 0 le_rfl).posDef_sqrt
    · simp only [MomentPath.q, hp.2.1, hp.2.2]
      exact le_max_right _ _
  obtain ⟨Q,hQ,c,hc,hdecay⟩ := MomentEnergy.uniform_decay (extern d).stein (extern d).sqrt
    hV qstar hstar.1 R hR
  let C' := 2*C+2*Q+1
  have hC' : 0 < C' := by dsimp [C']; positivity
  refine ⟨C',c,hC',hc,?_⟩
  intro N hN X hX t ht
  have hNp : 0 < N := by omega
  letI := Sampling.law_probability d N
  letI := GaussianAffine.gaussianLaw_probability qstar.1 qstar.2
  have hmean : Transport.w2sq (p.law t) (gaussianLaw qstar.1 qstar.2) ≤
      ENNReal.ofReal (Q*Real.exp (-2*c*t)) :=
    (GaussianCoupling.gaussian_w2sq_le (p.mean t) qstar.1 (covarianceRoot (p.cov t)) qstar.2).trans
      (ENNReal.ofReal_le_ofReal ((hdecay p hp.1 hpR t ht).2))
  have h := ExpectedRates.last_iterate (sampleLaw d N) hNp X p
    (gaussianLaw qstar.1 qstar.2) t ht (ENNReal.ofReal (C*rate d N))
    (ENNReal.ofReal (Q*Real.exp (-2*c*t))) (hbound N hN p X hp hX) hmean
  have htwo (v : ℝ) : (2 : ℝ≥0∞)*ENNReal.ofReal v = ENNReal.ofReal (2*v) := by
    simpa only [ENNReal.ofReal_ofNat] using
      (ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2) (q := v)).symm
  have hr := rate_pos d N hV.dimension (by omega)
  have he : 0 < Real.exp (-2*c*t) := Real.exp_pos _
  rw [htwo,htwo,← ENNReal.ofReal_add (by positivity) (by positivity)] at h
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  change 2*(C*rate d N)+2*(Q*Real.exp (-2*c*t)) ≤ C'*(rate d N+Real.exp (-2*c*t))
  dsimp only [C']
  nlinarith

/-- The 'consequently' clause of Corollary2.5 is derived from its actual
last-iterate estimate, with a single statistical constant before N and t. -/
theorem corollary25_statistical_scale (h25 : Specification.Corollary25)
    (d : ℕ) (V : E d → ℝ) (α β : ℝ) (hV : AdmissiblePotential V α β)
    (qstar : Coordinates d) (hstar : IsUniqueMinimizer V qstar)
    (μ0 : E d) (S0 : Mat d) (hS0 : S0.PosDef) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ N : ℕ, d+1 ≤ N →
      ∀ X : Sample d N → ParticlePath d N,
      (∀ᵐ ω ∂sampleLaw d N, IsParticlePathFrom V (gaussianCloud μ0 S0 N ω) (X ω)) →
      ∀ t : ℝ, 0 ≤ t → (2*c)⁻¹*max (Real.log (1/rate d N)) 0 ≤ t →
      (∫⁻ ω, Transport.w2sq (empiricalLaw (X ω t)) (gaussianLaw qstar.1 qstar.2)
        ∂sampleLaw d N) ≤ ENNReal.ofReal (C*rate d N) := by
  obtain ⟨C,c,hC,hc,hbound⟩ := h25 d V α β hV qstar hstar μ0 S0 hS0
  refine ⟨2*C,c,by positivity,hc,?_⟩
  intro N hN X hX t ht hbalance
  have hr := rate_pos d N hV.dimension (by omega)
  have he := exp_le_rate_at_balancing_time hr hc hbalance
  exact (hbound N hN X hX t ht).trans (ENNReal.ofReal_le_ofReal (by
    nlinarith [mul_le_mul_of_nonneg_left he hC.le]))

end Paper38.SourceExpected
