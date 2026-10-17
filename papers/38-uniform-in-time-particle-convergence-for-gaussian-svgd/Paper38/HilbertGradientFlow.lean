import Paper38.HilbertMobility
import Paper38.ModelBridges
import Paper38.ExternalGaussianAnalysis
import Paper38.GaussianEnergyGeometry
import Paper38.ExternalMatrixAnalysis

/-! The true Hilbert gradient and the moment-field chain. The only external
analysis input is the explicitly documented Gaussian Stein integral identity. -/
noncomputable section
open MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.Frobenius InnerProductSpace

namespace Paper38.HilbertGradientFlow
open Paper38.Model Paper38.HilbertCoordinates

variable {d : ℕ}
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

private theorem covariance_symmetric (q : Tangent d) :
    (matrixProjection d q * matrixProjection d q)ᵀ = matrixProjection d q * matrixProjection d q := by
  change (((toModel d q).2 * (toModel d q).2)ᵀ = _)
  rw [Matrix.transpose_mul, toModel_symmetric q]
  rfl

private theorem covarianceGradient_symmetric (V : E d → ℝ) (hV : ContDiff ℝ 2 V) (q : Tangent d) :
    (Mobility.energyCovGradient (matrixProjection d q * matrixProjection d q)
      (meanHessian V (meanProjection d q) (matrixProjection d q * matrixProjection d q)))ᵀ =
    Mobility.energyCovGradient (matrixProjection d q * matrixProjection d q)
      (meanHessian V (meanProjection d q) (matrixProjection d q * matrixProjection d q)) := by
  simp only [Mobility.energyCovGradient, Matrix.transpose_smul, Matrix.transpose_sub,
    Matrix.transpose_nonsing_inv, ModelBridges.meanHessian_transpose V hV,
    covariance_symmetric q]

/-- The exact covariance-coordinate energy cotangent in (4.2), transported
into the intrinsic tangent encoding. No gradient assertion is built into it. -/
def covarianceCotangent (V : E d → ℝ) (hV : ContDiff ℝ 2 V) (q : Tangent d) : Tangent d :=
  ofModel (meanGradient V (meanProjection d q) (matrixProjection d q * matrixProjection d q),
    Mobility.energyCovGradient (matrixProjection d q * matrixProjection d q)
      (meanHessian V (meanProjection d q) (matrixProjection d q * matrixProjection d q)))
    (covarianceGradient_symmetric V hV q)

@[simp] theorem toModel_covarianceCotangent (V : E d → ℝ) (hV : ContDiff ℝ 2 V) (q : Tangent d) :
    toModel d (covarianceCotangent V hV q) =
      (meanGradient V (meanProjection d q) (matrixProjection d q * matrixProjection d q),
        Mobility.energyCovGradient (matrixProjection d q * matrixProjection d q)
          (meanHessian V (meanProjection d q) (matrixProjection d q * matrixProjection d q))) :=
  toModel_ofModel _ _

/-- Algebraic differentiation of A² turns the covariance cotangent into the
usual symmetrized ΓA−A⁻¹ square-root-coordinate gradient matrix. -/
theorem sylvester_covarianceGradient (A Γ : Mat d) (hA : A.PosDef) :
    MobilityEllipticity.sylvester A (Mobility.energyCovGradient (A * A) Γ) =
      (1 / 2 : ℝ) • (A * Γ + Γ * A) - A⁻¹ := by
  have hd : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  have hl : A * (A * A)⁻¹ = A⁻¹ := by
    rw [Matrix.mul_inv_rev, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]
  have hr : (A * A)⁻¹ * A = A⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.mul_one]
  simp only [MobilityEllipticity.sylvester, Mobility.energyCovGradient,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, hl, hr]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

private theorem trace_three_symmetric (A Γ H : Mat d)
    (hA : Aᵀ = A) (hΓ : Γᵀ = Γ) (hH : Hᵀ = H) :
    Matrix.trace (A * Γ * H) = Matrix.trace (Γ * A * H) := by
  calc
    Matrix.trace (A * Γ * H) = Matrix.trace (A * Γ * H)ᵀ := (Matrix.trace_transpose _).symm
    _ = Matrix.trace (H * Γ * A) := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, hA, hΓ, hH, ← Matrix.mul_assoc]
    _ = Matrix.trace (A * H * Γ) := Matrix.trace_mul_cycle _ _ _
    _ = Matrix.trace (Γ * A * H) := Matrix.trace_mul_cycle _ _ _

/-- The actual transformed cotangent has the exact source first-variation trace. -/
theorem transformed_cotangent_trace (A Γ H : Mat d) (hA : A.PosDef)
    (hΓ : Γᵀ = Γ) (hH : Hᵀ = H) :
    Mobility.frobenius (MobilityEllipticity.sylvester A
      (Mobility.energyCovGradient (A * A) Γ)) H =
      Matrix.trace (Γ * A * H) - Matrix.trace (A⁻¹ * H) := by
  have hs : Aᵀ = A := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.isHermitian.eq
  have hg : (Mobility.energyCovGradient (A * A) Γ)ᵀ =
      Mobility.energyCovGradient (A * A) Γ := by
    simp only [Mobility.energyCovGradient, Matrix.transpose_smul, Matrix.transpose_sub,
      Matrix.transpose_nonsing_inv, Matrix.transpose_mul, hs, hΓ]
  have hsy : (MobilityEllipticity.sylvester A (Mobility.energyCovGradient (A * A) Γ))ᵀ =
      MobilityEllipticity.sylvester A (Mobility.energyCovGradient (A * A) Γ) := by
    simp [MobilityEllipticity.sylvester, Matrix.transpose_add, Matrix.transpose_mul, hs, hg, add_comm]
  rw [Mobility.frobenius, hsy, sylvester_covarianceGradient A Γ hA,
    Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.add_mul, Matrix.trace_add, trace_three_symmetric A Γ H hs hΓ hH]
  simp only [smul_eq_mul]
  ring

variable {V : E d → ℝ} {α β : ℝ}

/-- Actual intrinsic first derivative, obtained by differentiation plus the
explicitly declared external Stein integral identity. -/
theorem intrinsic_first_variation (stein : ExternalGaussianAnalysis.GaussianSteinTheorem d)
    (hV : AdmissiblePotential V α β)
    (q w : Tangent d) (hq : q ∈ Domain d) :
    fderiv ℝ (HilbertCoordinates.energy V) q w =
      ⟪meanGradient V (meanProjection d q) (matrixProjection d q * matrixProjection d q),
        meanProjection d w⟫_ℝ +
      Matrix.trace (meanHessian V (meanProjection d q) (matrixProjection d q * matrixProjection d q) *
        matrixProjection d q * matrixProjection d w) -
      Matrix.trace ((matrixProjection d q)⁻¹ * matrixProjection d w) := by
  have hraw := (GaussianEnergyGeometry.model_energy_contDiffAt hV (toModel d q) hq.det_pos.ne').differentiableAt
    (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hc := hraw.hasFDerivAt.comp q (toModel d).hasFDerivAt
  change fderiv ℝ (Model.energy V ∘ (toModel d)) q w = _
  rw [hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  rw [GaussianEnergyGeometry.model_energy_first_variation hV _ _ hq.det_pos.ne']
  rw [ExternalGaussianAnalysis.gaussian_stein_first_variation stein hV
    (toModel d q).1 (toModel d w).1 (toModel d q).2 (toModel d w).2
    hq (toModel_symmetric w)]
  rfl

/-- The explicitly transformed covariance cotangent represents precisely the
actual first variation; it is not assumed to be the gradient. -/
theorem transformed_cotangent_inner (hV : AdmissiblePotential V α β)
    (q w : Tangent d) (hq : q ∈ Domain d) :
    ⟪HilbertMobility.J q (covarianceCotangent V hV.regularity q), w⟫_ℝ =
      ⟪meanGradient V (meanProjection d q) (matrixProjection d q * matrixProjection d q),
        meanProjection d w⟫_ℝ +
      Matrix.trace (meanHessian V (meanProjection d q) (matrixProjection d q * matrixProjection d q) *
        matrixProjection d q * matrixProjection d w) -
      Matrix.trace ((matrixProjection d q)⁻¹ * matrixProjection d w) := by
  simp only [inner_toModel, HilbertMobility.toModel_J, toModel_covarianceCotangent,
    matrixInner_eq_frobenius]
  simp only [← meanProjection_apply, ← matrixProjection_apply]
  rw [transformed_cotangent_trace (matrixProjection d q)
    (meanHessian V (meanProjection d q) (matrixProjection d q * matrixProjection d q))
    (matrixProjection d w) hq (ModelBridges.meanHessian_transpose V hV.regularity _ _)
    (toModel_symmetric w)]
  ring

/-- The true Riesz gradient of the actual Gaussian reverse-KL energy. The
external dependency is only the Stein integral input used above. -/
theorem actual_gradient (stein : ExternalGaussianAnalysis.GaussianSteinTheorem d)
    (hV : AdmissiblePotential V α β) (q : Tangent d) (hq : q ∈ Domain d) :
    gradient (HilbertCoordinates.energy V) q =
      HilbertMobility.J q (covarianceCotangent V hV.regularity q) := by
  apply ext_inner_right ℝ
  intro w
  calc
    ⟪gradient (HilbertCoordinates.energy V) q, w⟫_ℝ =
        fderiv ℝ (HilbertCoordinates.energy V) q w := by
      simp only [gradient, InnerProductSpace.toDual_symm_apply]
    _ = _ := intrinsic_first_variation stein hV q w hq
    _ = _ := (transformed_cotangent_inner hV q w hq).symm

private theorem covariance_posDef (q : Tangent d) (hq : q ∈ Domain d) :
    (matrixProjection d q * matrixProjection d q).PosDef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (matrixProjection d q)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  change (((toModel d q).2)ᵀ * (toModel d q).2).PosSemidef at h
  rw [toModel_symmetric q] at h
  exact h.posDef_iff_isUnit.mpr (hq.isUnit.mul hq.isUnit)

/-- The actual covariance-coordinate moment field is minus the genuine
mobility applied to the explicit covariance cotangent. -/
theorem momentField_eq_neg_mobility (hV : AdmissiblePotential V α β)
    (q : Tangent d) (hq : q ∈ Domain d) :
    toModel d (-(HilbertMobility.mobility q) (covarianceCotangent V hV.regularity q)) =
      Model.momentField V (meanProjection d q) (matrixProjection d q * matrixProjection d q) := by
  rw [map_neg, HilbertMobility.toModel_mobility, toModel_covarianceCotangent]
  apply Prod.ext
  · apply (EuclideanSpace.equiv (Fin d) ℝ).injective
    change -Mobility.mobilityMean (WithLp.ofLp (meanProjection d q))
        (matrixProjection d q * matrixProjection d q)
        (WithLp.ofLp (meanGradient V (meanProjection d q) (matrixProjection d q * matrixProjection d q)))
        (Mobility.energyCovGradient (matrixProjection d q * matrixProjection d q)
          (meanHessian V (meanProjection d q) (matrixProjection d q * matrixProjection d q))) = _
    change _ = ModelBridges.coordinates
      (Model.momentField V (meanProjection d q) (matrixProjection d q * matrixProjection d q)).1
    rw [ModelBridges.momentField_mean_coordinates]
    exact (Mobility.momentMean_eq_neg_mobility _ _ _ _ (covariance_posDef q hq)).symm
  · change -Mobility.mobilityCov (WithLp.ofLp (meanProjection d q))
        (matrixProjection d q * matrixProjection d q)
        (WithLp.ofLp (meanGradient V (meanProjection d q) (matrixProjection d q * matrixProjection d q)))
        (Mobility.energyCovGradient (matrixProjection d q * matrixProjection d q)
          (meanHessian V (meanProjection d q) (matrixProjection d q * matrixProjection d q))) = _
    rw [ModelBridges.momentField_covariance_coordinates]
    exact (Mobility.momentCov_eq_neg_mobility _ _ _ _ (covariance_posDef q hq)).symm

/-- The actual square-root-coordinate source vector field, using the true
Hilbert Riesz gradient and the true pulled-back mobility. -/
def field (V : E d → ℝ) (q : Tangent d) : Tangent d :=
  -(HilbertMobility.P q) (gradient (HilbertCoordinates.energy V) q)

/-- The transformed gradient flow pushes forward to exactly (2.3), not to an
assumed or independently supplied moment equation. -/
theorem field_moment_chain (stein : ExternalGaussianAnalysis.GaussianSteinTheorem d)
    (hV : AdmissiblePotential V α β)
    (q : Tangent d) (hq : q ∈ Domain d) :
    toModel d (HilbertMobility.J q (field V q)) =
      Model.momentField V (meanProjection d q) (matrixProjection d q * matrixProjection d q) := by
  rw [field, actual_gradient stein hV q hq]
  simp only [HilbertMobility.P, ContinuousLinearMap.comp_apply]
  rw [HilbertMobility.inverseJ_J q _ hq, map_neg, HilbertMobility.J_inverseJ q _ hq]
  exact momentField_eq_neg_mobility hV q hq

/-- The actual covariance coordinate map Φ(μ,A)=(μ,A²), intrinsically encoded. -/
def covarianceState (q : Tangent d) : Tangent d :=
  HilbertMobility.encode d (meanProjection d q, matrixProjection d q * matrixProjection d q)

@[simp] theorem toModel_covarianceState (q : Tangent d) :
    toModel d (covarianceState q) =
      (meanProjection d q, matrixProjection d q * matrixProjection d q) :=
  HilbertMobility.toModel_encode _ (covariance_symmetric q)

/-- The actual differential of Φ is the actual J, without an assumed chain formula. -/
theorem covarianceState_hasFDerivAt (q : Tangent d) :
    HasFDerivAt covarianceState (HilbertMobility.J q) q := by
  have hraw := ((meanProjection d).hasFDerivAt (x := q)).prodMk
    (((matrixProjection d).hasFDerivAt (x := q)).fun_mul'
      ((matrixProjection d).hasFDerivAt (x := q)))
  have hc := (HilbertMobility.encode d).hasFDerivAt.comp q hraw
  convert hc using 1

theorem principalRoot_covarianceState (q : Tangent d) (hq : q ∈ Domain d) :
    ExternalMatrixAnalysis.principalRoot (covarianceState q) = q := by
  apply toModel_injective d
  rw [ExternalMatrixAnalysis.toModel_principalRoot]
  change ((toModel d (covarianceState q)).1, CFC.sqrt (toModel d (covarianceState q)).2) = _
  rw [toModel_covarianceState]
  apply Prod.ext
  · rfl
  · exact (CFC.sqrt_eq_iff _ _ (covariance_posDef q hq).posSemidef.nonneg hq.posSemidef.nonneg).mpr rfl

/-- Every genuine intrinsic gradient trajectory pushes forward to a solution of
the exact source moment ODE, including its right derivative at physical time zero. -/
theorem gradientPath_momentSolution (stein : ExternalGaussianAnalysis.GaussianSteinTheorem d)
    (hV : AdmissiblePotential V α β)
    (q : ℝ → Tangent d) (hdom : ∀ t, 0 ≤ t → q t ∈ Domain d)
    (hpath : ∀ t, 0 ≤ t → HasDerivWithinAt q (field V (q t)) (Set.Ici 0) t) :
    Model.momentSolution V (fun t => meanProjection d (q t))
      (fun t => matrixProjection d (q t) * matrixProjection d (q t)) := by
  constructor
  · intro t ht
    exact covariance_posDef (q t) (hdom t ht)
  · intro t ht
    have hΦ := (covarianceState_hasFDerivAt (q t)).comp_hasDerivWithinAt t (hpath t ht)
    have hd := (toModel d).hasFDerivAt.comp_hasDerivWithinAt t hΦ
    rw [field_moment_chain stein hV (q t) (hdom t ht)] at hd
    constructor
    · simpa only [Function.comp_def, toModel_covarianceState] using
        (ContinuousLinearMap.fst ℝ (E d) (Mat d)).hasFDerivAt.comp_hasDerivWithinAt t hd
    · simpa only [Function.comp_def, toModel_covarianceState] using
        (ContinuousLinearMap.snd ℝ (E d) (Mat d)).hasFDerivAt.comp_hasDerivWithinAt t hd

/-- The actual principal-square-root lift of arbitrary raw mean/covariance paths.
Encoding is exact on symmetric states; values outside nonnegative time are immaterial. -/
def principalLift (μ : ℝ → E d) (S : ℝ → Mat d) (t : ℝ) : Tangent d :=
  ExternalMatrixAnalysis.principalRoot (HilbertMobility.encode d (μ t, S t))

theorem toModel_principalLift (μ : ℝ → E d) (S : ℝ → Mat d) (t : ℝ) (hS : (S t).PosDef) :
    toModel d (principalLift μ S t) = (μ t, CFC.sqrt (S t)) := by
  have hs : (S t)ᵀ = S t := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hS.isHermitian.eq
  rw [principalLift, ExternalMatrixAnalysis.toModel_principalRoot]
  change ((toModel d (HilbertMobility.encode d (μ t, S t))).1,
    CFC.sqrt (toModel d (HilbertMobility.encode d (μ t, S t))).2) = _
  rw [HilbertMobility.toModel_encode _ hs]

theorem principalLift_mem_Domain (μ : ℝ → E d) (S : ℝ → Mat d) (t : ℝ) (hS : (S t).PosDef) :
    principalLift μ S t ∈ Domain d := by
  change (toModel d (principalLift μ S t)).2.PosDef
  rw [toModel_principalLift μ S t hS]
  exact hS.posDef_sqrt

/-- Conversely every actual source moment trajectory lifts to the true intrinsic
−P∇F flow. The only additional baseline input is the explicitly documented
principal-matrix-square-root differential, not a trajectory or dynamics assumption. -/
theorem momentSolution_gradientPath (stein : ExternalGaussianAnalysis.GaussianSteinTheorem d)
    (sqrt : ExternalMatrixAnalysis.PrincipalRootDifferentiation d) (hV : AdmissiblePotential V α β)
    (μ : ℝ → E d) (S : ℝ → Mat d) (hsol : Model.momentSolution V μ S) :
    (∀ t, 0 ≤ t → principalLift μ S t ∈ Domain d) ∧
    ∀ t, 0 ≤ t → HasDerivWithinAt (principalLift μ S)
      (field V (principalLift μ S t)) (Set.Ici 0) t := by
  refine ⟨fun t ht => principalLift_mem_Domain μ S t (hsol.1 t ht), ?_⟩
  intro t ht
  have hS := hsol.1 t ht
  have hs : (S t)ᵀ = S t := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hS.isHermitian.eq
  have hencoded : HilbertMobility.encode d (μ t, S t) ∈ Domain d := by
    change (toModel d (HilbertMobility.encode d (μ t, S t))).2.PosDef
    rw [HilbertMobility.toModel_encode _ hs]
    exact hS
  have he := (HilbertMobility.encode d).hasFDerivAt.comp_hasDerivWithinAt t
    ((hsol.2 t ht).1.prodMk (hsol.2 t ht).2)
  have hroot := (ExternalMatrixAnalysis.principalRoot_hasFDerivAt sqrt _ hencoded).comp_hasDerivWithinAt t he
  have hdomain := principalLift_mem_Domain μ S t hS
  have hparams := toModel_principalLift μ S t hS
  have hμ : meanProjection d (principalLift μ S t) = μ t := congrArg Prod.fst hparams
  have hC : matrixProjection d (principalLift μ S t) * matrixProjection d (principalLift μ S t) = S t := by
    change (toModel d (principalLift μ S t)).2 * (toModel d (principalLift μ S t)).2 = _
    rw [hparams]
    exact CFC.sqrt_mul_sqrt_self _ hS.posSemidef.nonneg
  have hchain := field_moment_chain stein hV (principalLift μ S t) hdomain
  rw [hμ, hC] at hchain
  have heq : HilbertMobility.encode d (Model.momentField V (μ t) (S t)) =
      HilbertMobility.J (principalLift μ S t) (field V (principalLift μ S t)) := by
    calc
      _ = HilbertMobility.encode d (toModel d
          (HilbertMobility.J (principalLift μ S t) (field V (principalLift μ S t)))) :=
        congrArg (HilbertMobility.encode d) hchain.symm
      _ = _ := HilbertMobility.encode_toModel _
  change HasDerivWithinAt (principalLift μ S)
    (HilbertMobility.inverseJ (principalLift μ S t)
      (HilbertMobility.encode d (Model.momentField V (μ t) (S t)))) (Set.Ici 0) t at hroot
  rw [heq, HilbertMobility.inverseJ_J _ _ hdomain] at hroot
  exact hroot

end Paper38.HilbertGradientFlow
