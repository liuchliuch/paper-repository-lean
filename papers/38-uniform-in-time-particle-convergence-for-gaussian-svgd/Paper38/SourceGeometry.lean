import Paper38.GeometrySpecification
import Paper38.SourceGeometryBounds
import Paper38.SourceMomentFlow
import Paper38.MomentEnergy

/-! Proofs of the literal source geometric contracts. Standard Gaussian Stein,
principal-root and maximal-ODE inputs are ordinary named theorem arguments. -/
noncomputable section
open scoped Matrix MatrixOrder Matrix.Norms.Frobenius InnerProductSpace
namespace Paper38.SourceGeometry
open Model HilbertCoordinates GeometrySpecification Set
set_option maxHeartbeats 600000
variable {d : ℕ} {V : E d → ℝ} {α β : ℝ}

private theorem root_square (q : Tangent d) (hq : q ∈ Domain d) :
    matrixProjection d (ExternalMatrixAnalysis.principalRoot q) *
      matrixProjection d (ExternalMatrixAnalysis.principalRoot q) = matrixProjection d q := by
  simp only [matrixProjection_apply, ExternalMatrixAnalysis.toModel_principalRoot]
  exact CFC.sqrt_mul_sqrt_self _ hq.posSemidef.nonneg

private theorem root_mean (q : Tangent d) :
    meanProjection d (ExternalMatrixAnalysis.principalRoot q) = meanProjection d q := by
  simp only [meanProjection_apply, ExternalMatrixAnalysis.toModel_principalRoot]

/-- The covariance-coordinate gradient is derived by differentiating the actual
principal-root energy and using the genuine self-adjoint Sylvester inverse. -/
theorem covarianceEnergy_gradient (stein : ExternalGaussianAnalysis.GaussianSteinTheorem d)
    (sqrt : ExternalMatrixAnalysis.PrincipalRootDifferentiation d)
    (hV : AdmissiblePotential V α β) (q : Tangent d) (hq : q ∈ Domain d) :
    gradient (covarianceEnergy V) q =
      HilbertGradientFlow.covarianceCotangent V hV.regularity (ExternalMatrixAnalysis.principalRoot q) := by
  let r := ExternalMatrixAnalysis.principalRoot q
  have hr : r ∈ Domain d := ExternalMatrixAnalysis.principalRoot_mem_Domain q hq
  have hd := (((GaussianEnergyGeometry.intrinsic_energy_contDiffOn hV).contDiffAt
    ((Domain_isOpen d).mem_nhds hr)).differentiableAt (by norm_num)).hasFDerivAt
  have hc := hd.comp q (sqrt q hq)
  apply ext_inner_right ℝ
  intro w
  calc
    ⟪gradient (covarianceEnergy V) q,w⟫_ℝ = fderiv ℝ (covarianceEnergy V) q w := by
      simp only [gradient, InnerProductSpace.toDual_symm_apply]
    _ = fderiv ℝ (HilbertCoordinates.energy V) r (HilbertMobility.inverseJ r w) := by
      rw [show covarianceEnergy V = HilbertCoordinates.energy V ∘ ExternalMatrixAnalysis.principalRoot from rfl,
        hc.fderiv]
      rfl
    _ = ⟪gradient (HilbertCoordinates.energy V) r,HilbertMobility.inverseJ r w⟫_ℝ := by
      simp only [gradient, InnerProductSpace.toDual_symm_apply]
    _ = ⟪HilbertMobility.J r (HilbertGradientFlow.covarianceCotangent V hV.regularity r),
        HilbertMobility.inverseJ r w⟫_ℝ := by
      rw [HilbertGradientFlow.actual_gradient stein hV r hr]
    _ = ⟪HilbertGradientFlow.covarianceCotangent V hV.regularity r,
        HilbertMobility.J r (HilbertMobility.inverseJ r w)⟫_ℝ :=
      (HilbertMobility.J_self_adjoint r _ _).symm
    _ = _ := by rw [HilbertMobility.J_inverseJ r w hr]

private theorem covarianceMobility_eq (q : Tangent d) (hq : q ∈ Domain d) :
    covarianceMobility q = HilbertMobility.mobility (ExternalMatrixAnalysis.principalRoot q) := by
  unfold covarianceMobility HilbertMobility.mobility
  rw [root_mean,root_square q hq]

/-- Equations (4.2)--(4.6) on the original Gaussian energy and matrices. -/
theorem lemma41 (extern : ∀ d : ℕ, ExternalAnalyticInputs.Baselines d) :
    GeometrySpecification.Lemma41 := by
  intro d V α β hV q hq
  have hr := ExternalMatrixAnalysis.principalRoot_mem_Domain q hq
  have hgrad := covarianceEnergy_gradient (extern d).stein (extern d).sqrt hV q hq
  have hraw : toModel d (gradient (covarianceEnergy V) q) =
      (meanGradient V (meanProjection d q) (matrixProjection d q),
        Mobility.energyCovGradient (matrixProjection d q)
          (meanHessian V (meanProjection d q) (matrixProjection d q))) := by
    rw [hgrad,HilbertGradientFlow.toModel_covarianceCotangent,root_mean,root_square q hq]
  refine ⟨hraw,?_,?_,?_,?_⟩
  · intro u v
    rw [covarianceMobility_eq q hq]
    exact HilbertMobility.mobility_symmetric _ _ _
  · intro v hv
    rw [covarianceMobility_eq q hq]
    exact HilbertMobility.mobility_quadratic_pos _ v hr hv
  · intro u v
    rw [covarianceMobility_eq q hq,inner_eq_mobility_pairing,HilbertMobility.toModel_mobility,
      HilbertMobility.rawM_apply]
    simp only [Model.vec,WithLp.ofLp_toLp,root_mean,root_square q hq]
    have hs : (matrixProjection d q)ᵀ = matrixProjection d q := toModel_symmetric q
    have hb := Mobility.bilinear_identity (WithLp.ofLp (meanProjection d q)) (matrixProjection d q)
      (WithLp.ofLp (meanProjection d u)) (WithLp.ofLp (meanProjection d v))
      (matrixProjection d u) (matrixProjection d v) hs (toModel_symmetric u) (toModel_symmetric v)
    simpa only [meanProjection_apply,matrixProjection_apply,
      EuclideanSpace.inner_eq_star_dotProduct,star_trivial,dotProduct_comm] using hb
  · rw [hgrad,covarianceMobility_eq q hq]
    have h := HilbertGradientFlow.momentField_eq_neg_mobility hV
      (ExternalMatrixAnalysis.principalRoot q) hr
    simpa only [root_mean,root_square q hq] using h

/-- Complete Lemma 4.2, with the exact trace/integral second variation,
α-strong convexity, actual compact sublevels and literal unique minimizer. -/
theorem lemma42 : GeometrySpecification.Lemma42 := by
  intro d V α β hV
  refine ⟨GaussianEnergyGeometry.intrinsic_energy_contDiffOn hV,?_,?_,
    GaussianGradientFlow.strongly_convex hV,GaussianGradientFlow.sublevel_isCompact hV,?_⟩
  · intro q hq v
    exact GaussianEnergyGeometry.intrinsic_energy_second_variation hV q v hq
  · intro q hq v
    exact GaussianEnergyGeometry.intrinsic_energy_second_fderiv_lower hV q v hq
  · obtain ⟨z,hz,hcrit,hmin⟩ := GaussianGradientFlow.exists_unique_minimizer hV
    exact ⟨toModel d z,hmin⟩

/-- Existing principal-results specification, with no external hypothesis:
minimizer existence/uniqueness follows from the proved C² geometry alone. -/
theorem lemma42_minimizer : Specification.Lemma42_minimizer := by
  intro d V α β hV
  obtain ⟨z,hz,hcrit,hmin⟩ := GaussianGradientFlow.exists_unique_minimizer hV
  exact ⟨toModel d z,hmin⟩

private theorem energy_derivative (hV : AdmissiblePotential V α β) :
    ∀ q ∈ Domain d, HasFDerivAt (HilbertCoordinates.energy V)
      (innerSL ℝ (gradient (HilbertCoordinates.energy V) q)) q := by
  intro q hq
  exact GradientGeometry.hasFDerivAt_gradient_repr
    (((GaussianEnergyGeometry.intrinsic_energy_contDiffOn hV).contDiffAt
      ((Domain_isOpen d).mem_nhds hq)).differentiableAt (by norm_num))

/-- The exact p estimate applies to every right-domain gradient trajectory;
trapping is derived from energy dissipation before ellipticity is used. -/
theorem gradient_path_decay (hV : AdmissiblePotential V α β)
    (z : Tangent d) (hz : z ∈ Domain d)
    (hmin : ∀ x ∈ Domain d, HilbertCoordinates.energy V z ≤ HilbertCoordinates.energy V x)
    (R p : ℝ) (hR : 0 ≤ R) (hp : 0 ≤ p)
    (hell : ∀ x ∈ GeometrySpecification.sublevel V z R, ∀ v : Tangent d,
      p*‖v‖^2 ≤ ⟪v,HilbertMobility.P x v⟫_ℝ)
    (q : ℝ → Tangent d) (hq : IsGradientPath V q)
    (hi : q 0 ∈ GeometrySpecification.sublevel V z R) (t : ℝ) (ht : 0 ≤ t) :
    q t ∈ GeometrySpecification.sublevel V z R ∧
    HilbertCoordinates.energy V (q t)-HilbertCoordinates.energy V z ≤
      (HilbertCoordinates.energy V (q 0)-HilbertCoordinates.energy V z) * Real.exp (-2*α*p*t) ∧
    ‖q t-z‖ ≤ Real.sqrt (2*R/α) * Real.exp (-α*p*t) ∧
    ‖q t-z‖^2 ≤ (2*R/α) * Real.exp (-2*α*p*t) ∧
    (R = 0 → q t = z) := by
  have hdom : ∀ s, 0 ≤ s → q s ∈ Domain d := hq.1
  have hode : ∀ s, 0 ≤ s → HasDerivWithinAt q
      (-(HilbertMobility.P (q s) (gradient (HilbertCoordinates.energy V) (q s)))) (Ici 0) s := hq.2
  have htrap : ∀ s, 0 ≤ s → q s ∈ GeometrySpecification.sublevel V z R := by
    intro s hs
    refine ⟨hq.1 s hs,?_⟩
    have ea := @GradientWithin.energy_nonincreasing (Tangent d) inferInstance inferInstance
    have eb := ea (F := HilbertCoordinates.energy V) (G := gradient (HilbertCoordinates.energy V))
      (P := HilbertMobility.P (d := d)) (q := q) (Ω := Domain d) (t := s)
    have ec := eb hs (energy_derivative hV)
    have ed := ec (fun x hx v => HilbertMobility.P_quadratic_nonneg (d := d) x v hx)
    have he := ed hdom hode
    exact (sub_le_sub_right he _).trans hi.2
  have ea := @WithinEnergyDecay.energy_exponential_decay (Tangent d) inferInstance inferInstance
  have eb := ea (F := HilbertCoordinates.energy V) (G := gradient (HilbertCoordinates.energy V))
    (P := HilbertMobility.P (d := d)) (q := q) (Ω := Domain d) (z := z) (α := α) (p := p) (t := t)
  have ec := eb hV.alpha_pos hp ht
  have ed := ec (GaussianGradientFlow.strongly_convex hV) hz (energy_derivative hV)
  have he := ed hode hdom (fun s hs v => hell _ (htrap s hs) v)
  have hcrit := GradientGeometry.gradient_eq_zero_of_minimizer (Domain_isOpen d) hz hmin
  have hc := EnergyDecay.distance_coercivity (GaussianGradientFlow.strongly_convex hV)
    hz (hq.1 t ht) hcrit
  have he' : HilbertCoordinates.energy V (q t)-HilbertCoordinates.energy V z ≤
      R * Real.exp (-2*α*p*t) :=
    he.trans (mul_le_mul_of_nonneg_right hi.2 (Real.exp_pos _).le)
  have hsqrt : Real.sqrt (2*R/α)^2 = 2*R/α := Real.sq_sqrt (div_nonneg (mul_nonneg (by norm_num) hR) hV.alpha_pos.le)
  have hexp : Real.exp (-2*α*p*t) = Real.exp (-α*p*t)^2 := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  have hsq : ‖q t-z‖^2 ≤ (2*R/α)*Real.exp (-2*α*p*t) := by
    apply (mul_le_mul_iff_right₀ (div_pos hV.alpha_pos (by norm_num) : 0 < α/2)).mp
    calc
      α/2 * ‖q t-z‖^2 ≤ R*Real.exp (-2*α*p*t) := hc.trans he'
      _ = α/2 * ((2*R/α)*Real.exp (-2*α*p*t)) := by field_simp [hV.alpha_pos.ne']
  have hnorm : ‖q t-z‖ ≤ Real.sqrt (2*R/α)*Real.exp (-α*p*t) := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    simpa only [mul_pow,hsqrt,← hexp] using hsq
  refine ⟨htrap t ht,he,hnorm,hsq,?_⟩
  intro hzero
  rw [hzero] at hsq
  simp only [mul_zero,zero_div,zero_mul] at hsq
  exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (q t-z)]))

/-- Proposition 4.3 with its actual explicit constant, actual global flow,
arbitrary within0 solutions, R=0 stationary case and physical moment version. -/
theorem proposition43 (extern : ∀ d : ℕ, ExternalAnalyticInputs.Baselines d) :
    GeometrySpecification.Proposition43 := by
  intro d V α β hV z hz hmin R hR
  have hK : IsCompact (GeometrySpecification.sublevel V z R) := by
    convert GaussianGradientFlow.sublevel_isCompact hV (HilbertCoordinates.energy V z+R) using 1
    ext q
    simp only [GeometrySpecification.sublevel,mem_setOf_eq]
    constructor <;> intro h <;> exact ⟨h.1,by linarith [h.2]⟩
  obtain ⟨M,a,b,hM,ha,hb,hbounds⟩ := SourceGeometryBounds.compact_spectral_bounds hK
    (fun q hq => hq.1)
  let p := MobilityEllipticity.sublevelConstant a M b
  have hp : 0 < p := MobilityEllipticity.sublevelConstant_pos a M b ha
  have hell : ∀ q ∈ GeometrySpecification.sublevel V z R, ∀ v : Tangent d,
      p*‖v‖^2 ≤ ⟪v,HilbertMobility.P q v⟫_ℝ := by
    intro q hq v
    have hh := hbounds q hq
    exact SourceGeometryBounds.P_explicit_lower q hq.1 M a b hh.1 hM.le
      (fun w => (hh.2.2 w).1) (fun w => (hh.2.2 w).2) v
  have hloewner : ∀ q ∈ GeometrySpecification.sublevel V z R,
      a • (1 : Mat d) ≤ matrixProjection d q ∧ matrixProjection d q ≤ b • (1 : Mat d) := by
    intro q hq
    exact SourceGeometryBounds.quadratic_loewner q a b (hbounds q hq).2.1
  refine ⟨M,a,b,hM,ha,hb,hbounds,hloewner,hp,hell,?_,?_,?_,?_,?_⟩
  · intro x hx
    obtain ⟨z',hz',hmin',hcrit',p',hp',q,hq0,hq,huniq⟩ :=
      GaussianGradientFlow.exists_unique_global_flow (extern d).standardMaximalODE hV hx.1
    exact ⟨q,hq0,fun t ht => (hq t ht).1,fun t ht => (hq t ht).2.1.hasDerivWithinAt⟩
  · intro x hx s
    have ma := @GlobalODE.maximal_lifetime_eq_top (Tangent d) inferInstance inferInstance
    have mb := ma (F := HilbertCoordinates.energy V) (G := gradient (HilbertCoordinates.energy V))
      (P := HilbertMobility.P (d := d)) (Ω := Domain d) (x₀ := x)
    have mc := mb s
    have md := mc (energy_derivative hV)
    have me := md (fun q hq v => HilbertMobility.P_quadratic_nonneg (d := d) q v hq)
    exact me (GaussianGradientFlow.sublevel_isCompact hV _)
  · intro q hq hi t ht
    have h := gradient_path_decay hV z hz hmin R p hR hp.le hell q hq hi t ht
    exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2⟩
  · intro μ C hC
    exact SourceMomentFlow.momentWellPosed (extern d) hV μ C hC
  · intro r hr hi t ht
    let q := HilbertGradientFlow.principalLift r.mean r.cov
    obtain ⟨hdom,hpath⟩ := HilbertGradientFlow.momentSolution_gradientPath
      (extern d).stein (extern d).sqrt hV r.mean r.cov hr
    have hq : IsGradientPath V q := ⟨hdom,hpath⟩
    have hraw (s : ℝ) (hs : 0 ≤ s) : toModel d (q s) = r.q s :=
      HilbertGradientFlow.toModel_principalLift _ _ s (hr.1 s hs)
    have henergy (s : ℝ) (hs : 0 ≤ s) : HilbertCoordinates.energy V (q s) = Model.energy V (r.q s) := by
      simp only [HilbertCoordinates.energy,hraw s hs]
    have hinit : q 0 ∈ GeometrySpecification.sublevel V z R := by
      refine ⟨hdom 0 le_rfl,?_⟩
      change HilbertCoordinates.energy V (q 0)-HilbertCoordinates.energy V z ≤ R
      rw [henergy 0 le_rfl]
      exact hi.2
    have h := gradient_path_decay hV z hz hmin R p hR hp.le hell q hq hinit t ht
    have heq : coordinateSqDist (r.q t) (toModel d z) = ‖q t-z‖^2 := by
      rw [← hraw t ht]
      exact coordinateSqDist_toModel _ _
    refine ⟨⟨?_,?_⟩,?_,?_,?_⟩
    · exact (hr.1 t ht).posDef_sqrt
    · have htrap := h.1.2
      change HilbertCoordinates.energy V (q t)-HilbertCoordinates.energy V z ≤ R at htrap
      rw [henergy t ht] at htrap
      exact htrap
    · have he := h.2.1
      rw [henergy t ht,henergy 0 le_rfl] at he
      exact he
    · rw [heq]
      exact h.2.2.2.1
    · intro hR0
      rw [← hraw t ht,h.2.2.2.2 hR0]

end Paper38.SourceGeometry
