import Paper38.ParticleLimitFromODE
import Paper38.TransportDistance
import Paper38.MomentEnergy
import Paper38.SourceFlowMeasurability
import Paper38.GaussianLocalization

/-! Proposition 2.6's actual source hypotheses and constants uniform before the
cloud and particle count. Generic standard linear ODE/Stein/root inputs contain
no Gaussian dynamical conclusions. All shape and transport conclusions below
are obtained from the own affine construction. -/

noncomputable section
namespace Paper38.SourceParticleLimit

open Paper38.Model Paper38.Transport Paper38.AffineLifting Paper38.ParticleLimit
open Paper38.HilbertCoordinates MeasureTheory Set Filter
open scoped BigOperators Matrix MatrixOrder ENNReal NNReal Topology

variable {d : ℕ}

/-- Every actual moment path from the specified source sublevel converges to
the actual Gaussian energy minimizer. -/
theorem moment_path_tendsto
    (stein : ExternalGaussianAnalysis.GaussianSteinTheorem d)
    (sqrt : ExternalMatrixAnalysis.PrincipalRootDifferentiation d)
    {V : E d → ℝ} {α β : ℝ} (hV : AdmissiblePotential V α β)
    (qstar : Coordinates d) (hstar : Specification.IsMinimizer V qstar)
    (R : ℝ) (hR : 0 ≤ R) (p : Specification.MomentPath d)
    (hp : momentSolution V p.mean p.cov) (hi : p.q 0 ∈ sublevel V qstar R) :
    Tendsto p.q atTop (𝓝 qstar) := by
  obtain ⟨Q, hQ, decay, hd, hbound⟩ := MomentEnergy.uniform_decay stein sqrt hV qstar hstar R hR
  apply coordinate_tendsto_of_exp_bound p.q qstar (Real.sqrt Q) decay hd
  intro t ht
  simpa only [Real.sq_sqrt hQ] using (hbound p hp hi t ht).2

/-- Source Proposition 2.6, equations (2.17)--(2.20), in genuine squared
quadratic transport. C and decay are chosen before N, the cloud and whitening.
The last error limit is stated for every moment path converging to qstar;
`moment_path_tendsto` discharges this for the source mean-field initialization. -/
theorem proposition26_at [NeZero d]
    (stein : ExternalGaussianAnalysis.GaussianSteinTheorem d)
    (sqrt : ExternalMatrixAnalysis.PrincipalRootDifferentiation d)
    (linear : LinearMatrixODE.StandardDecayingFundamentalMatrixTheorem d)
    {V : E d → ℝ} {α β : ℝ} (hV : AdmissiblePotential V α β)
    (qstar : Coordinates d) (hstar : Specification.IsMinimizer V qstar)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∃ decay : ℝ, 0 < decay ∧ ∀ (N : ℕ) (hN : 0 < N)
      (X : ℝ → Fin N → E d) (hX : particleSolution V X),
      Specification.cloudQ (X 0) ∈ sublevel V qstar R →
      ∀ (W : Mat d), IsWhitening (X 0) W →
      ∃ Linf : Mat d, IsUnit Linf ∧
    ∃ (Binf : Mat d) (xinf : Fin N → E d),
      IsUnit Binf ∧ Binf * Binf.transpose = qstar.2 * qstar.2.transpose ∧
      (∀ i, xinf i = qstar.1 + matVec Linf (X 0 i - empiricalMean (X 0))) ∧
      (∀ i, xinf i = qstar.1 + matVec Binf (standardizedCloud (X 0) W i)) ∧
      (∀ t, 0 ≤ t → w2sq (empiricalLaw (X t)) (empiricalLaw xinf) ≤
        ENNReal.ofReal (C *
          Real.exp (-2 * decay * t))) ∧
      (∀ i, Tendsto (fun t => X t i) atTop (𝓝 (xinf i))) ∧
      (∀ p : Specification.MomentPath d, momentSolution V p.mean p.cov →
        p.q 0 ∈ sublevel V qstar R →
        Tendsto (fun t => w2sq (empiricalLaw (X t)) (p.law t)) atTop
          (𝓝 (w2sq (empiricalLaw xinf) (gaussianLaw qstar.1 qstar.2)))) ∧
      ((covarianceMin Binf : ℝ≥0∞) * w2sq
          (empiricalLaw (standardizedCloud (X 0) W)) (standardGaussian d) ≤
        w2sq (empiricalLaw xinf) (gaussianLaw qstar.1 qstar.2) ∧
       w2sq (empiricalLaw xinf) (gaussianLaw qstar.1 qstar.2) ≤
        (covarianceMax Binf : ℝ≥0∞) * w2sq
          (empiricalLaw (standardizedCloud (X 0) W)) (standardGaussian d)) ∧
      0 < w2sq (empiricalLaw xinf) (gaussianLaw qstar.1 qstar.2) := by
  obtain ⟨z, hzraw, hz, hmin⟩ := SourceCoordinates.lift_source_minimizer hstar
  let H : Set (Tangent d) := {q | q ∈ Domain d ∧
    HilbertCoordinates.energy V q ≤ Model.energy V qstar + R}
  let Kset : Set (Coordinates d) := toModel d '' H
  have hKraw (q : Coordinates d) (hq : q ∈ sublevel V qstar R) : q ∈ Kset := by
    refine ⟨SourceCoordinates.lift q hq.1, ⟨SourceCoordinates.lift_mem_Domain q hq.1, ?_⟩,
      SourceCoordinates.toModel_lift q hq.1⟩
    change Model.energy V (toModel d (SourceCoordinates.lift q hq.1)) ≤ _
    rw [SourceCoordinates.toModel_lift]
    linarith [hq.2]
  have hstarK : qstar ∈ Kset := hKraw qstar ⟨hstar.1, by simpa using hR⟩
  obtain ⟨K, hLip⟩ := CoefficientRegularity.coefficient_lipschitzOn_ambient_energy_sublevel
    stein hV (Model.energy V qstar + R)
  have hzero : ParticleLimit.gaussianCoefficient V qstar = 0 := by
    rw [← hzraw]
    exact CoefficientRegularity.gaussianCoefficient_zero_of_minimizer stein hV hz hmin
  obtain ⟨Q, hQ, decay, hd, hdecay⟩ := MomentEnergy.uniform_decay stein sqrt hV qstar hstar R hR
  obtain ⟨M, hM, hlimit⟩ := uniform_limit_from_lipschitz_moment_decay linear V qstar hstar.1
    Kset K (Real.sqrt Q) decay hd hLip hstarK hzero
  have hcompact : IsCompact H := GaussianGradientFlow.sublevel_isCompact hV _
  have hcont : ContinuousOn (fun q : Tangent d => frobSq (matrixProjection d q)) H := by
    unfold frobSq
    fun_prop
  obtain ⟨T, hT⟩ := hcompact.exists_bound_of_continuousOn hcont
  let C : ℝ := 1 + Q + M ^ 2 * max 0 T
  refine ⟨C, by dsimp [C]; positivity, decay, hd, ?_⟩
  intro N hN X hX hi W hW
  let p : Specification.MomentPath d :=
    ⟨fun t => empiricalMean (X t), fun t => empiricalCovariance (X t)⟩
  have hp : momentSolution V p.mean p.cov :=
    ModelBridges.particleSolution_momentSolution V hV.regularity hN X hX
  have hip : p.q 0 ∈ sublevel V qstar R := hi
  have hC : ContinuousOn (fun t => particleCoefficient V (X t)) (Ici 0) := by
    have hc := SourceFlowMeasurability.momentCoefficient_continuousOn_path stein sqrt hV p hp
    apply hc.congr
    intro t ht
    rfl
  have hmem (t : ℝ) (ht : 0 ≤ t) : Specification.cloudQ (X t) ∈ Kset :=
    hKraw _ (hdecay p hp hip t ht).1
  have hqbound (t : ℝ) (ht : 0 ≤ t) :
      coordinateSqDist (Specification.cloudQ (X t)) qstar ≤
        (Real.sqrt Q) ^ 2 * Real.exp (-2 * decay * t) := by
    simpa only [Real.sq_sqrt hQ] using (hdecay p hp hip t ht).2
  obtain ⟨Linf, hLinf, Binf, xinf, hunitB, hcov, hcenter, haffine, hcost,
    hXlim, herror, hfloor, hpositive⟩ := hlimit N hN X hX hC W hW hmem hqbound
  have htrace : (empiricalCovariance (X 0)).trace ≤ max 0 T := by
    let q0 := HilbertGradientFlow.principalLift p.mean p.cov 0
    have hq0 : q0 ∈ H := by
      refine ⟨HilbertGradientFlow.principalLift_mem_Domain _ _ _ (hp.1 0 le_rfl), ?_⟩
      rw [HilbertCoordinates.energy, HilbertGradientFlow.toModel_principalLift _ _ _ (hp.1 0 le_rfl)]
      have he : Model.energy V (p.mean 0, CFC.sqrt (p.cov 0)) - Model.energy V qstar ≤ R := hi.2
      linarith [he]
    have heq : frobSq (matrixProjection d q0) = (empiricalCovariance (X 0)).trace := by
      change frobSq (toModel d q0).2 = _
      rw [HilbertGradientFlow.toModel_principalLift _ _ _ (hp.1 0 le_rfl)]
      exact GaussianLocalization.frobSq_sqrt_trace _ (hX.1 0 le_rfl)
    rw [← heq]
    exact (le_abs_self _).trans ((hT q0 hq0).trans (le_max_right _ _))
  refine ⟨Linf, hLinf, Binf, xinf, hunitB, hcov, hcenter, haffine, ?_, hXlim, ?_, hfloor, hpositive⟩
  · intro t ht
    apply (hcost t ht).trans
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    rw [Real.sq_sqrt hQ]
    dsimp [C]
    nlinarith [mul_le_mul_of_nonneg_left htrace (sq_nonneg M)]
  · intro r hr hir
    exact herror r (moment_path_tendsto stein sqrt hV qstar hstar R hR r hr hir)

end Paper38.SourceParticleLimit

namespace Paper38.Production
open Paper38.Model Paper38.Transport Paper38.AffineLifting MeasureTheory Set Filter
open scoped ENNReal Topology

/-- Literal finite-particle source contract, including the unsquared (2.19),
actual moment convergence and invariance of the limiting law under whitening. -/
def Specification26 : Prop :=
  ∀ (d : ℕ) [NeZero d] (V : E d → ℝ) (α β : ℝ), AdmissiblePotential V α β →
  ∀ qstar, Specification.IsUniqueMinimizer V qstar → ∀ R : ℝ, 0 < R →
  ∃ C : ℝ, 0 < C ∧ ∃ decay : ℝ, 0 < decay ∧
  ∀ (N : ℕ) (hN : 0 < N) (x : Fin N → E d), (empiricalCovariance x).PosDef →
    Specification.cloudQ x ∈ sublevel V qstar R →
    Specification.ParticleWellPosed V x ∧
    ∀ X : Specification.ParticlePath d N, Specification.IsParticlePathFrom V x X →
    ∀ W : Mat d, IsWhitening x W → ∃ (Binf : Mat d) (xinf : Fin N → E d),
      IsUnit Binf ∧ Binf * Binf.transpose = qstar.2 * qstar.2.transpose ∧
      empiricalLaw xinf = (empiricalLaw (standardizedCloud x W)).map
        (fun z => qstar.1 + matVec Binf z) ∧
      (∀ t, 0 ≤ t → w2sq (empiricalLaw (X t)) (empiricalLaw xinf) ≤
        ENNReal.ofReal (C * Real.exp (-2 * decay * t))) ∧
      (∀ p : Specification.MomentPath d, momentSolution V p.mean p.cov →
        p.q 0 ∈ sublevel V qstar R →
        Tendsto (fun t => w2 (empiricalLaw (X t)) (p.law t)) atTop
          (𝓝 (w2 (empiricalLaw xinf) (gaussianLaw qstar.1 qstar.2)))) ∧
      Tendsto (fun t => empiricalMean (X t)) atTop (𝓝 qstar.1) ∧
      Tendsto (fun t => empiricalCovariance (X t)) atTop (𝓝 (qstar.2 * qstar.2)) ∧
      ((covarianceMin Binf : ℝ≥0∞) * w2sq (empiricalLaw (standardizedCloud x W))
        (standardGaussian d) ≤ w2sq (empiricalLaw xinf) (gaussianLaw qstar.1 qstar.2) ∧
       w2sq (empiricalLaw xinf) (gaussianLaw qstar.1 qstar.2) ≤
        (covarianceMax Binf : ℝ≥0∞) * w2sq (empiricalLaw (standardizedCloud x W)) (standardGaussian d)) ∧
      0 < w2sq (empiricalLaw xinf) (gaussianLaw qstar.1 qstar.2) ∧
      (∀ W' : Mat d, IsWhitening x W' → ∃ B' : Mat d,
        IsUnit B' ∧ B' * B'.transpose = qstar.2 * qstar.2.transpose ∧
        empiricalLaw xinf = (empiricalLaw (standardizedCloud x W')).map
          (fun z => qstar.1 + matVec B' z))

end Paper38.Production

namespace Paper38.SourceParticleLimit
open Paper38.Model Paper38.Transport Paper38.AffineLifting Paper38.ParticleLimit
open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- Complete source Proposition 2.6, with no source dynamical conclusion in
its external baseline fields. -/
theorem proposition26 (extern : ∀ d : ℕ, ExternalAnalyticInputs.Baselines d) :
    Production.Specification26 := by
  intro d inst V α β hV qstar hstar R hR
  obtain ⟨C, hC, decay, hd, hmain⟩ := proposition26_at
    (extern d).stein (extern d).sqrt (extern d).decayingFundamental hV qstar hstar.1 R hR.le
  refine ⟨C, hC, decay, hd, ?_⟩
  intro N hN x hS hi
  refine ⟨SourceFlowMeasurability.particleWellPosed (extern d) hV hN x hS, ?_⟩
  intro X hX W hW
  have hiX : Specification.cloudQ (X 0) ∈ sublevel V qstar R := by rwa [hX.2]
  have hWX : IsWhitening (X 0) W := by rwa [hX.2]
  obtain ⟨Linf, hLinf, Binf, xinf, hunit, hcov, hcenter, haffine, hrate,
    hXlim, herror, hfloor, hpositive⟩ := hmain N hN X hX.1 hiX W hWX
  have hpush : empiricalLaw xinf = (empiricalLaw (standardizedCloud x W)).map
      (fun z => qstar.1 + matVec Binf z) := by
    rw [empiricalLaw_map hN _ _ (continuous_const.add (GaussianAffine.continuous_matVec Binf)).measurable]
    congr 1
    funext i
    simpa only [hX.2] using haffine i
  let pX : Specification.MomentPath d :=
    ⟨fun t => empiricalMean (X t), fun t => empiricalCovariance (X t)⟩
  have hpX : momentSolution V pX.mean pX.cov :=
    ModelBridges.particleSolution_momentSolution V hV.regularity hN X hX.1
  have hqlim := moment_path_tendsto (extern d).stein (extern d).sqrt hV qstar hstar.1
    R hR.le pX hpX hiX
  have hmean : Tendsto (fun t => empiricalMean (X t)) atTop (𝓝 qstar.1) :=
    (continuous_fst.tendsto qstar).comp hqlim
  have hSigma := particle_covariance_tendsto X hX.1 qstar hqlim
  refine ⟨Binf, xinf, hunit, hcov, hpush, hrate, ?_, hmean, hSigma, ?_, hpositive, ?_⟩
  · intro p hp hip
    exact w2_tendsto_of_w2sq_tendsto _ _ _ _ (herror p hp hip)
  · simpa only [hX.2] using hfloor
  · intro W' hW'
    have hWX' : IsWhitening (X 0) W' := by rwa [hX.2]
    obtain ⟨Linf', hLinf', B', yinf, hunit', hcov', hcenter', haffine', hrate',
      hYlim, herror', hfloor', hpositive'⟩ := hmain N hN X hX.1 hiX W' hWX'
    have heq := limiting_cloud_unique X xinf yinf hXlim hYlim
    refine ⟨B', hunit', hcov', ?_⟩
    rw [empiricalLaw_map hN _ _ (continuous_const.add (GaussianAffine.continuous_matVec B')).measurable,
      heq]
    congr 1
    funext i
    simpa only [hX.2] using haffine' i

end Paper38.SourceParticleLimit
