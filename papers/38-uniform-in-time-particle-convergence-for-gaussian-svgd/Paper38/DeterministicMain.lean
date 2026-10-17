import Paper38.SourceMomentFlow
import Paper38.SourceFlowMeasurability
import Paper38.DeterministicOracle
import Paper38.MomentEnergy

/-! The literal deterministic source theorem, from the original potential
hypotheses and ordinary named standard analysis theorem arguments. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace Paper38.DeterministicMain
open Set MeasureTheory
open Model HilbertCoordinates Specification
open scoped Matrix MatrixOrder Matrix.Norms.Frobenius ENNReal

private theorem source_norm_sq {d : ℕ} (q : Tangent d) :
    ‖q‖^2 = ‖(toModel d q).1‖^2 + frobSq (toModel d q).2 := by
  simpa only [ambient_toModel, Submodule.norm_coe] using norm_ambient_sq (toModel d q)

/-- A fixed actual Gaussian energy sublevel has a uniform covariance-root bound. -/
theorem sublevel_frob_bound {d : ℕ} {V : E d → ℝ} {α β : ℝ}
    (hV : AdmissiblePotential V α β) (qstar : Coordinates d) (R : ℝ) :
    ∃ b > 0, ∀ q ∈ sublevel V qstar R, frobSq q.2 ≤ b^2 := by
  let K : Set (Tangent d) := {q | q ∈ Domain d ∧
    HilbertCoordinates.energy V q ≤ Model.energy V qstar+R}
  have hK : IsCompact K := GaussianGradientFlow.sublevel_isCompact hV _
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn continuous_norm.continuousOn
  refine ⟨max M 0+1, by positivity, ?_⟩
  intro q hq
  let z := SourceCoordinates.lift q hq.1
  have hzraw : toModel d z = q := SourceCoordinates.toModel_lift q hq.1
  have hzK : z ∈ K := ⟨SourceCoordinates.lift_mem_Domain q hq.1, by
    change Model.energy V (toModel d z) ≤ Model.energy V qstar+R
    rw [hzraw]
    linarith [hq.2]⟩
  have hzbound := hM z hzK
  simp only [Real.norm_of_nonneg (norm_nonneg _)] at hzbound
  have hsq : ‖z‖^2 ≤ (max M 0+1)^2 := by
    have hh : ‖z‖ ≤ max M 0+1 := by linarith [le_max_left M 0]
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hh
  have hid := source_norm_sq z
  rw [hzraw] at hid
  exact (by linarith [sq_nonneg ‖q.1‖] : frobSq q.2 ≤ ‖z‖^2).trans hsq

/-- Actual source particle well-posedness, without a particle-flow premise. -/
theorem particleWellPosed {d N : ℕ} (extern : ExternalAnalyticInputs.Baselines d)
    {V : E d → ℝ} {α β : ℝ} (hV : AdmissiblePotential V α β)
    (hN : 0 < N) (x : Fin N → E d) (hx : (empiricalCovariance x).PosDef) :
    Specification.ParticleWellPosed V x := by
  apply SourceParticleFlow.particle_wellPosed_of_moment hN V hV.regularity x
    (SourceMomentFlow.momentWellPosed extern hV _ _ hx) extern.fundamental
  intro p hp
  exact SourceFlowMeasurability.momentCoefficient_continuousOn_path extern.stein extern.sqrt hV p hp.1

/-- The literal source Lemma 4.2 minimizer conclusion, proved from the original
potential assumptions alone, without an external analysis baseline. -/
theorem lemma42_minimizer : Specification.Lemma42_minimizer := by
  intro d V α β hV
  obtain ⟨z,hz,hcrit,hunique⟩ := GaussianGradientFlow.exists_unique_minimizer hV
  exact ⟨toModel d z,hunique⟩

/-- The full literal Theorem 2.1: constants precede the sample size, initial
moments, particle cloud, every actual solution and every whitening matrix. -/
theorem theorem21 (extern : ∀ d : ℕ, ExternalAnalyticInputs.Baselines d) :
    Specification.Theorem21 := by
  intro d V α β hV qstar hstar R hR
  obtain ⟨S,hS,hstable⟩ := SourceMomentFlow.lemma51_at (extern d).stein (extern d).sqrt
    hV qstar hstar R hR
  obtain ⟨b,hb,hbound⟩ := sublevel_frob_bound hV qstar R
  refine ⟨S,b,hS,hb,?_⟩
  intro N μ₀ C₀ x hN hC₀ hx hqi hxi
  refine ⟨SourceMomentFlow.momentWellPosed (extern d) hV μ₀ C₀ hC₀,
    particleWellPosed (extern d) hV hN x hx, ?_⟩
  intro p X hp hX W hW
  have hdim := hV.dimension
  letI : NeZero d := ⟨by omega⟩
  let pX : MomentPath d := ⟨fun t => empiricalMean (X t), fun t => empiricalCovariance (X t)⟩
  have hpX : momentSolution V pX.mean pX.cov :=
    ModelBridges.particleSolution_momentSolution V hV.regularity hN X hX.1
  have hpX0 : pX.q 0 = cloudQ x := by
    change cloudQ (X 0) = cloudQ x
    rw [hX.2]
  have hq0 : p.q 0 = (μ₀,covarianceRoot C₀) := by
    simp only [MomentPath.q,hp.2.1,hp.2.2]
  have hXsub : ∀ t, 0 ≤ t → pX.q t ∈ sublevel V qstar R := by
    intro t ht
    have he := MomentEnergy.energy_nonincreasing (extern d).stein (extern d).sqrt hV pX hpX t ht
    rw [hpX0] at he
    exact ⟨(hpX.1 t ht).posDef_sqrt, by linarith [hxi.2]⟩
  have hC0 := SourceFlowMeasurability.momentCoefficient_continuousOn_path
    (extern d).stein (extern d).sqrt hV pX hpX
  have hcoeff : ∀ t, SourceParticleFlow.momentCoefficient V (pX.mean t) (pX.cov t) =
      particleCoefficient V (X t) := by intro t; rfl
  have hC : ContinuousOn (fun t => particleCoefficient V (X t)) (Ici 0) := by
    simpa only [hcoeff] using hC0
  obtain ⟨L,hL0,hL,hLunit⟩ := (extern d).fundamental _ hC
  have hstableX : ∀ t, 0 ≤ t → coordinateSqDist (cloudQ (X t)) (p.q t) ≤
      S^2*coordinateSqDist (cloudQ (X 0)) (p.q 0) := by
    intro t ht
    have hh := hstable pX p hpX hp.1 (by rw [hpX0]; exact hxi)
      (by rw [hq0]; exact hqi) t ht
    exact hh
  have hspectral : ∀ t, 0 ≤ t → (AffineLifting.covarianceMax (L t * W⁻¹) : ℝ) ≤ b^2 := by
    intro t ht
    have hfactor := (TransportParticleAffine.standardized_affine_lift (X 0) W (L t)
      (by simpa only [hX.2] using hW) (empiricalMean (X t))).2
    have hcov := TransportParticleAffine.particle_affine_covariance hN V X hX.1 hC L hL0 hL t ht
    have hroot := CFC.sqrt_mul_sqrt_self (empiricalCovariance (X t)) (hpX.1 t ht).posSemidef.nonneg
    have hsym := (hpX.1 t ht).posDef_sqrt.isHermitian.eq
    have hbb : (L t * W⁻¹)*(L t * W⁻¹).transpose =
        covarianceRoot (empiricalCovariance (X t)) *
          (covarianceRoot (empiricalCovariance (X t))).transpose := by
      rw [hfactor, ← hcov]
      change empiricalCovariance (X t) = CFC.sqrt (empiricalCovariance (X t)) *
        (CFC.sqrt (empiricalCovariance (X t))).transpose
      have hs : (CFC.sqrt (empiricalCovariance (X t))).transpose =
          CFC.sqrt (empiricalCovariance (X t)) := by
        simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hsym
      rw [hs]
      exact hroot.symm
    have hbX : frobSq (covarianceRoot (empiricalCovariance (X t))) ≤ b^2 :=
      hbound (pX.q t) (hXsub t ht)
    have hmax : (AffineLifting.covarianceMax (L t * W⁻¹) : ℝ) ≤
        frobSq (covarianceRoot (empiricalCovariance (X t))) :=
      AffineLifting.covarianceMax_le_frobSq (L t * W⁻¹)
        (covarianceRoot (empiricalCovariance (X t))) hbb
    exact hmax.trans hbX
  have hh := DeterministicOracle.all_time_oracle_from_fundamental hN V X hX.1 p hC
    L hL0 hL hLunit W (by simpa only [hX.2] using hW) S b hstableX hspectral
  simpa only [hX.2] using hh

end Paper38.DeterministicMain
