import Paper38.CoefficientRegularity
import Paper38.ExternalAnalyticInputs
import Paper38.SourceParticleFlow
import Paper38.SourceMomentFlow
import Paper38.TransportContinuity
import Paper38.StandardizedShape

/-!
# Measurable actual particle solution families

The finite-particle field is locally Lipschitz on its actual covariance-positive
open domain. We select already proved global solutions there, extend by the
zero path outside, and use the explicitly supplied ordinary ODE continuous-
dependence theorem. Countable rational times then give measurability of the
actual all-time quadratic transport error.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.Frobenius InnerProductSpace
  Topology ENNReal NNReal

namespace Paper38.SourceFlowMeasurability
open Paper38.Model Paper38.HilbertCoordinates Paper38.Specification

variable {d N : ℕ} {V : E d → ℝ} {α β : ℝ}
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

/-- The textbook principal-root derivative, with its already proved smooth
inverse Sylvester family, yields actual C¹ regularity on the SPD domain. -/
theorem principalRoot_contDiffOn
    (sqrt : ExternalMatrixAnalysis.PrincipalRootDifferentiation d) :
    ContDiffOn ℝ 1 (ExternalMatrixAnalysis.principalRoot (d := d)) (Domain d) := by
  have hc : ContinuousOn (ExternalMatrixAnalysis.principalRoot (d := d)) (Domain d) :=
    fun q hq => (sqrt q hq).continuousAt.continuousWithinAt
  have hder : ContinuousOn
      (fun q : Tangent d => HilbertMobility.inverseJ (ExternalMatrixAnalysis.principalRoot q))
      (Domain d) := by
    intro q hq
    exact (HilbertMobility.inverseJ_contDiffAt 0 _
      (ExternalMatrixAnalysis.principalRoot_mem_Domain q hq)).continuousAt.comp_continuousWithinAt
        (hc q hq)
  apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
    (n := (0 : WithTop ℕ∞)) (Domain_isOpen d).uniqueDiffOn).mpr
  refine ⟨by norm_num, _, ?_, fun q hq => (sqrt q hq).hasFDerivWithinAt⟩
  exact contDiffOn_zero.mpr hder

/-- Empirical mean is a polynomial in the actual finite particle cloud. -/
theorem empiricalMean_contDiff (n : WithTop ℕ∞) :
    ContDiff ℝ n (empiricalMean (d := d) (N := N)) := by
  unfold empiricalMean
  exact (ContDiff.sum fun i _ => (ContinuousLinearMap.proj i :
    (Fin N → E d) →L[ℝ] E d).contDiff).const_smul (N : ℝ)⁻¹

/-- Empirical covariance is an actual quadratic polynomial. -/
theorem empiricalCovariance_contDiff (n : WithTop ℕ∞) :
    ContDiff ℝ n (empiricalCovariance (d := d) (N := N)) := by
  unfold empiricalCovariance
  have hs : ContDiff ℝ n (fun x : Fin N → E d =>
      ∑ i, outer (x i - empiricalMean x) (x i - empiricalMean x)) := by
    apply ContDiff.sum
    intro i _
    have hi := (ContinuousLinearMap.proj i : (Fin N → E d) →L[ℝ] E d).contDiff (n := n)
    have hc := hi.sub (empiricalMean_contDiff (d := d) (N := N) n)
    exact ((CoefficientRegularity.outerBilinear d).contDiff.comp hc).clm_apply hc
  exact hs.const_smul (N : ℝ)⁻¹

/-- Every empirical covariance is symmetric, without an invertibility premise. -/
theorem empiricalCovariance_symmetric (x : Fin N → E d) :
    (empiricalCovariance x)ᵀ = empiricalCovariance x := by
  ext i j
  simp [empiricalCovariance, outer, Matrix.sum_apply, mul_comm]


/-- Actual empirical mean/covariance, represented in the symmetric Hilbert
space; the encoding acts identically because covariance is symmetric. -/
def empiricalMoment (x : Fin N → E d) : Tangent d :=
  HilbertMobility.encode d (empiricalMean x, empiricalCovariance x)

@[simp] theorem toModel_empiricalMoment (x : Fin N → E d) :
    toModel d (empiricalMoment x) = (empiricalMean x, empiricalCovariance x) :=
  HilbertMobility.toModel_encode _ (empiricalCovariance_symmetric x)

theorem empiricalMoment_contDiff (n : WithTop ℕ∞) :
    ContDiff ℝ n (empiricalMoment (d := d) (N := N)) :=
  (HilbertMobility.encode d).contDiff.comp
    ((empiricalMean_contDiff n).prodMk (empiricalCovariance_contDiff n))

/-- The literal open domain of the source finite-particle equation. -/
def particleDomain (d N : ℕ) : Set (Fin N → E d) :=
  {x | (empiricalCovariance x).PosDef}

theorem particleDomain_isOpen : IsOpen (particleDomain d N) := by
  have h := (Domain_isOpen d).preimage (empiricalMoment_contDiff (d := d) (N := N) 0).continuous
  simpa only [Domain, Set.preimage_setOf_eq, toModel_empiricalMoment, particleDomain] using h

/-- The actual principal-root empirical state. -/
def empiricalRoot (x : Fin N → E d) : Tangent d :=
  ExternalMatrixAnalysis.principalRoot (empiricalMoment x)

@[simp] theorem toModel_empiricalRoot (x : Fin N → E d) :
    toModel d (empiricalRoot x) = cloudQ x := by
  simp only [empiricalRoot, ExternalMatrixAnalysis.toModel_principalRoot,
    meanProjection_apply, matrixProjection_apply, toModel_empiricalMoment, cloudQ, covarianceRoot]

theorem empiricalRoot_mem_Domain {x : Fin N → E d} (hx : x ∈ particleDomain d N) :
    empiricalRoot x ∈ Domain d := by
  apply ExternalMatrixAnalysis.principalRoot_mem_Domain
  change (toModel d (empiricalMoment x)).2.PosDef
  simpa only [toModel_empiricalMoment] using hx

theorem empiricalRoot_contDiffOn
    (sqrt : ExternalMatrixAnalysis.PrincipalRootDifferentiation d) :
    ContDiffOn ℝ 1 (empiricalRoot (d := d) (N := N)) (particleDomain d N) := by
  apply (principalRoot_contDiffOn sqrt).comp (empiricalMoment_contDiff 1).contDiffOn
  intro x hx
  change (toModel d (empiricalMoment x)).2.PosDef
  simpa only [toModel_empiricalMoment] using hx

/-- On the actual particle domain, the literal particle coefficient is the
same C¹ Gaussian coefficient at its empirical principal-root state. -/
theorem particleCoefficient_contDiffOn
    (stein : ExternalGaussianAnalysis.GaussianSteinTheorem d)
    (sqrt : ExternalMatrixAnalysis.PrincipalRootDifferentiation d)
    (hV : AdmissiblePotential V α β) :
    ContDiffOn ℝ 1 (particleCoefficient V (N := N)) (particleDomain d N) := by
  have h := (CoefficientRegularity.gaussianCoefficient_contDiffOn stein hV).comp
    (empiricalRoot_contDiffOn (N := N) sqrt) (fun x hx => empiricalRoot_mem_Domain hx)
  apply h.congr
  intro x hx
  simp only [Function.comp_apply, toModel_empiricalRoot]
  exact SourceParticleFlow.momentCoefficient_eq_gaussianCoefficient V
    (empiricalMean x) (empiricalCovariance x) hx

/-- The actual mean-gradient term in the particle ODE is C¹ as well. -/
theorem particleMeanGradient_contDiffOn
    (stein : ExternalGaussianAnalysis.GaussianSteinTheorem d)
    (sqrt : ExternalMatrixAnalysis.PrincipalRootDifferentiation d)
    (hV : AdmissiblePotential V α β) :
    ContDiffOn ℝ 1
      (fun x : Fin N → E d => meanGradient V (empiricalMean x) (empiricalCovariance x))
      (particleDomain d N) := by
  have h := (CoefficientRegularity.meanGradient_contDiffOn stein hV).comp
    (empiricalRoot_contDiffOn (N := N) sqrt) (fun x hx => empiricalRoot_mem_Domain hx)
  apply h.congr
  intro x hx
  simp only [Function.comp_apply, meanProjection_apply, matrixProjection_apply, toModel_empiricalRoot, cloudQ, covarianceRoot]
  rw [CFC.sqrt_mul_sqrt_self _ hx.posSemidef.nonneg]

/-- The true projected-particle vector field is C¹ under the original C²
potential hypotheses; no coefficient regularity is supplied as an input. -/
theorem particleField_contDiffOn
    (stein : ExternalGaussianAnalysis.GaussianSteinTheorem d)
    (sqrt : ExternalMatrixAnalysis.PrincipalRootDifferentiation d)
    (hV : AdmissiblePotential V α β) :
    ContDiffOn ℝ 1 (particleField V (N := N)) (particleDomain d N) := by
  apply contDiffOn_pi.mpr
  intro i
  exact (((GaussianDifferentiation.matrixAction d).contDiff.comp_contDiffOn
    (particleCoefficient_contDiffOn stein sqrt hV)).clm_apply
      (ContinuousLinearMap.proj i : (Fin N → E d) →L[ℝ] E d).contDiff.contDiffOn).sub
        (particleMeanGradient_contDiffOn stein sqrt hV)

theorem particleField_locallyLipschitzOn
    (stein : ExternalGaussianAnalysis.GaussianSteinTheorem d)
    (sqrt : ExternalMatrixAnalysis.PrincipalRootDifferentiation d)
    (hV : AdmissiblePotential V α β) :
    LocallyLipschitzOn (particleDomain d N) (particleField V (N := N)) := by
  intro x hx
  obtain ⟨L, U, hU, hL⟩ := ((particleField_contDiffOn stein sqrt hV).contDiffAt
    (particleDomain_isOpen.mem_nhds hx)).exists_lipschitzOnWith
  exact ⟨L, U, nhdsWithin_le_nhds hU, hL⟩

/-- Coefficient continuity along every actual raw moment solution. -/
theorem momentCoefficient_continuousOn_path
    (stein : ExternalGaussianAnalysis.GaussianSteinTheorem d)
    (sqrt : ExternalMatrixAnalysis.PrincipalRootDifferentiation d)
    (hV : AdmissiblePotential V α β) (p : MomentPath d)
    (hp : momentSolution V p.mean p.cov) :
    ContinuousOn (fun t => SourceParticleFlow.momentCoefficient V (p.mean t) (p.cov t)) (Ici 0) := by
  have hpath := HilbertGradientFlow.momentSolution_gradientPath stein sqrt hV p.mean p.cov hp
  have hc : ContinuousOn (HilbertGradientFlow.principalLift p.mean p.cov) (Ici 0) :=
    fun t ht => (hpath.2 t ht).continuousWithinAt
  have h := (CoefficientRegularity.gaussianCoefficient_contDiffOn stein hV).continuousOn.comp hc
    (fun t ht => hpath.1 t ht)
  apply h.congr
  intro t ht
  simp only [Function.comp_apply, HilbertGradientFlow.toModel_principalLift _ _ t (hp.1 t ht)]
  exact SourceParticleFlow.momentCoefficient_eq_gaussianCoefficient V (p.mean t) (p.cov t) (hp.1 t ht)

/-- Common-index empirical couplings give transport convergence for arbitrary
filters, not only large-time sequences. -/
theorem empirical_w2sq_tendsto_zero {ι : Type*} {l : Filter ι} (hN : 0 < N)
    (X : ι → Fin N → E d) (x : Fin N → E d) (hX : Tendsto X l (𝓝 x)) :
    Tendsto (fun i => Transport.w2sq (empiricalLaw (X i)) (empiricalLaw x)) l (𝓝 0) := by
  have hs : Tendsto (fun k => ∑ i, ‖X k i - x i‖ ^ 2) l (𝓝 0) := by
    have h := tendsto_finset_sum Finset.univ (fun i _ =>
      (((continuous_apply i).tendsto x |>.comp hX).sub
        (tendsto_const_nhds (x := x i))).norm.pow 2)
    simpa only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      Finset.sum_const_zero] using h
  have hr : Tendsto (fun k => (N : ℝ)⁻¹ * ∑ i, ‖X k i - x i‖ ^ 2) l (𝓝 0) := by
    simpa only [mul_zero] using hs.const_mul (N : ℝ)⁻¹
  have he : Tendsto (fun k => ENNReal.ofReal ((N : ℝ)⁻¹ * ∑ i, ‖X k i - x i‖ ^ 2)) l (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hr
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds he
    (fun _ => zero_le _) (fun k => StandardizedShape.empirical_coupling_cost hN (X k) x)

/-- The exact synchronous Gaussian coupling gives parameter-continuity in
quadratic transport, for arbitrary filters and arbitrary affine matrices. -/
theorem gaussian_w2sq_tendsto_zero {ι : Type*} {l : Filter ι}
    (Q : ι → Coordinates d) (q : Coordinates d) (hQ : Tendsto Q l (𝓝 q)) :
    Tendsto (fun i => Transport.w2sq (gaussianLaw (Q i).1 (Q i).2)
      (gaussianLaw q.1 q.2)) l (𝓝 0) := by
  have hc : Tendsto (fun i => coordinateSqDist (Q i) q) l (𝓝 0) := by
    simp_rw [coordinateSqDist_eq_norm_ambient]
    have h := (((ambientEquiv d).continuous.tendsto q |>.comp hQ).sub
      (tendsto_const_nhds (x := ambientEquiv d q))).norm.pow 2
    simpa only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using h
  have he : Tendsto (fun i => ENNReal.ofReal (coordinateSqDist (Q i) q)) l (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hc
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds he
    (fun _ => zero_le _) (fun i => GaussianCoupling.gaussian_w2sq_le (Q i).1 q.1 (Q i).2 q.2)

/-- Joint continuity of the actual empirical-to-Gaussian quadratic transport
cost. This is derived from the proved transport infimum and explicit couplings. -/
theorem empirical_gaussian_cost_continuous (hN : 0 < N) :
    Continuous (fun y : (Fin N → E d) × Coordinates d =>
      Transport.w2sq (empiricalLaw y.1) (gaussianLaw y.2.1 y.2.2)) := by
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have he (x : Fin N → E d) : IsProbabilityMeasure (empiricalLaw x) := by
    rw [GaussianCoupling.empiricalLaw_eq_transport_empirical hN]
    infer_instance
  letI (x : Fin N → E d) : IsProbabilityMeasure (empiricalLaw x) := he x
  letI (q : Coordinates d) : IsProbabilityMeasure (gaussianLaw q.1 q.2) :=
    GaussianCoupling.gaussianLaw_probability _ _
  apply continuous_iff_continuousAt.mpr
  intro y
  exact Transport.w2sq_tendsto_of_perturbations
    (empiricalLaw y.1) (gaussianLaw y.2.1 y.2.2)
    (fun z : (Fin N → E d) × Coordinates d => empiricalLaw z.1)
    (fun z : (Fin N → E d) × Coordinates d => gaussianLaw z.2.1 z.2.2)
    (empirical_w2sq_tendsto_zero hN Prod.fst y.1 continuous_fst.continuousAt)
    (gaussian_w2sq_tendsto_zero Prod.snd y.2 continuous_snd.continuousAt)

/-- Fixed-Gaussian specialization, avoiding any measurable-space convention
for raw matrix coordinates. -/
theorem empirical_gaussian_fixed_cost_continuous (hN : 0 < N) (q : Coordinates d) :
    Continuous (fun x : Fin N → E d =>
      Transport.w2sq (empiricalLaw x) (gaussianLaw q.1 q.2)) := by
  exact (empirical_gaussian_cost_continuous (d := d) (N := N) hN).comp
    (f := fun x : Fin N → E d => (x, q))
    ((continuous_id : Continuous (fun x : Fin N → E d => x)).prodMk
      (continuous_const (y := q)))

/-- Select a proved actual global particle solution on the covariance-positive
open domain, and use the zero path at all other initial states. -/
def selectedFlow (V : E d → ℝ)
    (hwell : ∀ x ∈ particleDomain d N, ParticleWellPosed V x)
    (x : Fin N → E d) : ParticlePath d N := by
  classical
  exact if hx : x ∈ particleDomain d N then Classical.choose (hwell x hx) else 0

theorem selectedFlow_isParticlePathFrom
    (hwell : ∀ x ∈ particleDomain d N, ParticleWellPosed V x)
    {x : Fin N → E d} (hx : x ∈ particleDomain d N) :
    IsParticlePathFrom V x (selectedFlow V hwell x) := by
  simp only [selectedFlow, dif_pos hx]
  exact (Classical.choose_spec (hwell x hx)).1

@[simp] theorem selectedFlow_eq_zero
    (hwell : ∀ x ∈ particleDomain d N, ParticleWellPosed V x)
    {x : Fin N → E d} (hx : x ∉ particleDomain d N) :
    selectedFlow V hwell x = 0 := by simp only [selectedFlow, dif_neg hx]

/-- Fixed-time continuity on the valid initial-state domain is the ordinary
ODE continuous-dependence theorem applied to the actual, already constructed
particle solution family and its proved locally Lipschitz field. -/
theorem selectedFlow_continuousOn_fixedTime
    (dependence : ExternalODEAnalysis.GlobalFlowContinuousDependence (Fin N → E d))
    (stein : ExternalGaussianAnalysis.GaussianSteinTheorem d)
    (sqrt : ExternalMatrixAnalysis.PrincipalRootDifferentiation d)
    (hV : AdmissiblePotential V α β)
    (hwell : ∀ x ∈ particleDomain d N, ParticleWellPosed V x)
    (t : ℝ) (ht : 0 ≤ t) :
    ContinuousOn (fun x => selectedFlow V hwell x t) (particleDomain d N) := by
  apply dependence (particleDomain d N) (particleField V) particleDomain_isOpen
    (particleField_locallyLipschitzOn stein sqrt hV) (selectedFlow V hwell)
  · intro x hx
    exact (selectedFlow_isParticlePathFrom hwell hx).2
  · intro x hx s hs
    have hp := selectedFlow_isParticlePathFrom hwell hx
    exact ⟨hp.1.1 s hs, hasDerivWithinAt_pi.mpr (hp.1.2 s hs)⟩
  · exact ht

/-- Extension by the zero path is measurable at each physical time, since its
valid initial-state domain is open. -/
theorem selectedFlow_measurable_fixedTime
    (dependence : ExternalODEAnalysis.GlobalFlowContinuousDependence (Fin N → E d))
    (stein : ExternalGaussianAnalysis.GaussianSteinTheorem d)
    (sqrt : ExternalMatrixAnalysis.PrincipalRootDifferentiation d)
    (hV : AdmissiblePotential V α β)
    (hwell : ∀ x ∈ particleDomain d N, ParticleWellPosed V x)
    (t : ℝ) (ht : 0 ≤ t) : Measurable (fun x => selectedFlow V hwell x t) := by
  classical
  have h := (selectedFlow_continuousOn_fixedTime dependence stein sqrt hV hwell t ht).measurable_piecewise
    (show ContinuousOn (fun _ : Fin N → E d => (0 : Fin N → E d)) (particleDomain d N)ᶜ from continuousOn_const)
    particleDomain_isOpen.measurableSet
  convert h using 1
  funext x
  by_cases hx : x ∈ particleDomain d N
  · simp only [Set.piecewise, hx, if_pos]
  · simp [Set.piecewise, hx]

/-- Every selected path is time-continuous, including the zero paths assigned
to exceptional initial clouds outside the covariance-positive domain. -/
theorem selectedFlow_continuousOn_time
    (hwell : ∀ x ∈ particleDomain d N, ParticleWellPosed V x) (x : Fin N → E d) :
    ContinuousOn (selectedFlow V hwell x) (Ici 0) := by
  by_cases hx : x ∈ particleDomain d N
  · intro t ht
    apply continuousWithinAt_pi.mpr
    intro i
    exact ((selectedFlow_isParticlePathFrom hwell hx).1.2 t ht i).continuousWithinAt
  · rw [selectedFlow_eq_zero hwell hx]
    exact continuousOn_const

/-- Sampling the fixed Gaussian affine map is continuous in all sample entries. -/
theorem gaussianCloud_continuous (μ : E d) (S : Mat d) :
    Continuous (gaussianCloud μ S N) := by
  apply continuous_pi
  intro i
  apply continuous_const.add
  apply (GaussianCoupling.continuous_matVec _).comp
  exact (GaussianCoupling.continuous_vec (d := d)).comp
    (continuous_pi fun j => continuous_apply (i, j))

/-- The actual principal-root Gaussian parameter path is continuous for every
source moment solution, with the source right-time derivative convention. -/
theorem moment_q_continuousOn
    (stein : ExternalGaussianAnalysis.GaussianSteinTheorem d)
    (sqrt : ExternalMatrixAnalysis.PrincipalRootDifferentiation d)
    (hV : AdmissiblePotential V α β) (p : MomentPath d)
    (hp : momentSolution V p.mean p.cov) : ContinuousOn p.q (Ici 0) := by
  have hpath := HilbertGradientFlow.momentSolution_gradientPath stein sqrt hV p.mean p.cov hp
  have hc : ContinuousOn (HilbertGradientFlow.principalLift p.mean p.cov) (Ici 0) :=
    fun t ht => (hpath.2 t ht).continuousWithinAt
  apply ((toModel d).continuous.comp_continuousOn hc).congr
  intro t ht
  exact (HilbertGradientFlow.toModel_principalLift p.mean p.cov t (hp.1 t ht)).symm

/-- All-time path error continuity uses only the proved joint transport-cost
continuity and the time-continuity of the actual paths. -/
theorem selectedFlow_pathError_continuousOn (hN : 0 < N)
    (stein : ExternalGaussianAnalysis.GaussianSteinTheorem d)
    (sqrt : ExternalMatrixAnalysis.PrincipalRootDifferentiation d)
    (hV : AdmissiblePotential V α β)
    (hwell : ∀ x ∈ particleDomain d N, ParticleWellPosed V x)
    (x : Fin N → E d) (p : MomentPath d) (hp : momentSolution V p.mean p.cov) :
    ContinuousOn (pathError (selectedFlow V hwell x) p) (Ici 0) := by
  have hy : ContinuousOn (fun t => (selectedFlow V hwell x t, p.q t)) (Ici 0) :=
    (selectedFlow_continuousOn_time hwell x).prodMk
      (moment_q_continuousOn stein sqrt hV p hp)
  have h := (empirical_gaussian_cost_continuous (d := d) hN).comp_continuousOn hy
  simpa only [Function.comp_apply, pathError, MomentPath.law, MomentPath.q] using h


/-- Fixed-time sample errors are measurable, including the exceptional zero
paths. No measurability of an arbitrary choice operation is assumed. -/
theorem selectedFlow_pathError_measurable_fixedTime (hN : 0 < N)
    (dependence : ExternalODEAnalysis.GlobalFlowContinuousDependence (Fin N → E d))
    (stein : ExternalGaussianAnalysis.GaussianSteinTheorem d)
    (sqrt : ExternalMatrixAnalysis.PrincipalRootDifferentiation d)
    (hV : AdmissiblePotential V α β)
    (hwell : ∀ x ∈ particleDomain d N, ParticleWellPosed V x)
    (μ : E d) (S : Mat d) (p : MomentPath d) (t : ℝ) (ht : 0 ≤ t) :
    Measurable (fun ω : Sample d N => pathError
      (selectedFlow V hwell (gaussianCloud μ S N ω)) p t) := by
  have hX : Measurable (fun ω : Sample d N =>
      selectedFlow V hwell (gaussianCloud μ S N ω) t) :=
    (selectedFlow_measurable_fixedTime dependence stein sqrt hV hwell t ht).comp
      (gaussianCloud_continuous (N := N) μ S).measurable
  have hcost : Continuous (fun x : Fin N → E d =>
      Transport.w2sq (empiricalLaw x) (p.law t)) :=
    empirical_gaussian_fixed_cost_continuous hN (p.q t)
  exact hcost.measurable.comp hX


/-- The actual source all-time random transport supremum is measurable. The
uncountable supremum is reduced to rational times using time-continuity for
all samples, including those outside the covariance-positive domain. -/
theorem selectedFlow_pathSup_measurable (hN : 0 < N)
    (dependence : ExternalODEAnalysis.GlobalFlowContinuousDependence (Fin N → E d))
    (stein : ExternalGaussianAnalysis.GaussianSteinTheorem d)
    (sqrt : ExternalMatrixAnalysis.PrincipalRootDifferentiation d)
    (hV : AdmissiblePotential V α β)
    (hwell : ∀ x ∈ particleDomain d N, ParticleWellPosed V x)
    (μ : E d) (S : Mat d) (p : MomentPath d) (hp : momentSolution V p.mean p.cov) :
    Measurable (fun ω : Sample d N => pathSup
      (selectedFlow V hwell (gaussianCloud μ S N ω)) p) := by
  apply RandomSupremum.measurable_timeSup
  · intro ω
    exact selectedFlow_pathError_continuousOn hN stein sqrt hV hwell _ p hp
  · intro q
    apply selectedFlow_pathError_measurable_fixedTime hN dependence stein sqrt hV hwell μ S p q
    exact_mod_cast q.property

/-- Actual global particle well-posedness under the source potential hypotheses,
with moment existence and all coefficient regularity discharged by proofs. -/
theorem particleWellPosed (extern : ExternalAnalyticInputs.Baselines d)
    (hV : AdmissiblePotential V α β) (hN : 0 < N)
    (x : Fin N → E d) (hx : x ∈ particleDomain d N) : ParticleWellPosed V x :=
  SourceParticleFlow.particle_wellPosed_of_moment hN V hV.regularity x
    (SourceMomentFlow.momentWellPosed extern hV (empiricalMean x) (empiricalCovariance x) hx)
    extern.fundamental
    (fun p hp => momentCoefficient_continuousOn_path extern.stein extern.sqrt hV p hp.1)

/-- The genuine random solution family required by source Theorem 2.2 exists.
It solves the actual particle equation at every covariance-positive sample,
and its literal all-physical-time transport supremum is measurable. Rank-one
and other exceptional samples receive the explicit zero path. -/
theorem exists_measurable_particle_family (extern : ExternalAnalyticInputs.Baselines d)
    (hV : AdmissiblePotential V α β) (hN : 0 < N)
    (μ : E d) (S : Mat d) (p : MomentPath d) (hp : momentSolution V p.mean p.cov) :
    ∃ X : Sample d N → ParticlePath d N,
      (∀ ω, (empiricalCovariance (gaussianCloud μ S N ω)).PosDef →
        IsParticlePathFrom V (gaussianCloud μ S N ω) (X ω)) ∧
      Measurable (fun ω => pathSup (X ω) p) := by
  let hwell : ∀ x ∈ particleDomain d N, ParticleWellPosed V x :=
    fun x hx => particleWellPosed extern hV hN x hx
  refine ⟨fun ω => selectedFlow V hwell (gaussianCloud μ S N ω), ?_, ?_⟩
  · intro ω hω
    exact selectedFlow_isParticlePathFrom hwell hω
  · exact selectedFlow_pathSup_measurable hN (extern.continuousDependence N)
      extern.stein extern.sqrt hV hwell μ S p hp

/-- The preceding everywhere-defined measurable family is an actual solution
almost surely as soon as the initialized empirical covariance is positive
almost surely. The latter is the separately proved raw sampling fact. -/
theorem exists_ae_measurable_particle_family (extern : ExternalAnalyticInputs.Baselines d)
    (hV : AdmissiblePotential V α β) (hN : 0 < N)
    (μ : E d) (S : Mat d) (p : MomentPath d) (hp : momentSolution V p.mean p.cov)
    (hPD : ∀ᵐ ω ∂sampleLaw d N,
      (empiricalCovariance (gaussianCloud μ S N ω)).PosDef) :
    ∃ X : Sample d N → ParticlePath d N,
      (∀ᵐ ω ∂sampleLaw d N, IsParticlePathFrom V (gaussianCloud μ S N ω) (X ω)) ∧
      Measurable (fun ω => pathSup (X ω) p) := by
  obtain ⟨X, hX, hmeas⟩ := exists_measurable_particle_family extern hV hN μ S p hp
  refine ⟨X, ?_, hmeas⟩
  filter_upwards [hPD] with ω hω
  exact hX ω hω

end Paper38.SourceFlowMeasurability
