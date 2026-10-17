import Paper38.GaussianCoefficientModel
import Paper38.GaussianLocalization
import Paper38.HilbertMobility
import Paper38.HilbertGradientFlow
import Paper38.GaussianEnergyGeometry
import Paper38.GradientGeometry
import Paper38.EnergyCompactness
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Regularity of the actual Gaussian particle coefficient

The original potential is only C². Its Gaussian averaged Hessian is recovered
from the actual C¹ energy gradient by the smooth inverse Sylvester map. Thus
no Lipschitz assumption on the pointwise Hessian or on the coefficient is used.
The only external classical analysis input in the specialization is the precise
Gaussian Stein identity named in `ExternalGaussianAnalysis`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.Frobenius InnerProductSpace Topology NNReal

namespace Paper38.CoefficientRegularity
open Paper38.Model Paper38.HilbertCoordinates

set_option maxHeartbeats 600000

/-- The genuine matrix inverse is smooth in the Frobenius norm at every unit. -/
theorem matrixInverse_contDiffAt {d : ℕ} {n : WithTop ℕ∞} {A : Mat d}
    (hA : IsUnit A) : ContDiffAt ℝ n (fun B : Mat d => B⁻¹) A := by
  have h : ContDiffAt ℝ n (Ring.inverse : Mat d → Mat d) A := by
    simpa only [hA.unit_spec] using (contDiffAt_ringInverse ℝ (n := n) hA.unit)
  exact h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun B => Matrix.nonsing_inv_eq_ringInverse (A := B))

/-- The two-variable outer product is an actual continuous bilinear map. -/
def outerBilinear (d : ℕ) : E d →L[ℝ] E d →L[ℝ] Mat d :=
  LinearMap.toContinuousLinearMap
    { toFun := HilbertMobility.outerLeft
      map_add' := by intro x y; ext z i j; simp [HilbertMobility.outerLeft_apply, Matrix.vecMulVec, add_mul]
      map_smul' := by intro c x; ext z i j; simp [HilbertMobility.outerLeft_apply, Matrix.vecMulVec, mul_assoc] }

@[simp] theorem outerBilinear_apply {d : ℕ} (x y : E d) :
    outerBilinear d x y = outer x y := rfl

/-- C¹ maps have one common Lipschitz constant on each compact convex subset
of their open domain. The bound is obtained from their actual derivative. -/
theorem exists_lipschitzOnWith_of_compact_convex
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {Ω K : Set E} (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ 1 f Ω)
    (hK : IsCompact K) (hconv : Convex ℝ K) (hsub : K ⊆ Ω) :
    ∃ L : ℝ≥0, LipschitzOnWith L f K := by
  have hc : ContinuousOn (fun x => ‖fderiv ℝ f x‖₊) K :=
    ((hf.continuousOn_fderiv_of_isOpen hΩ le_rfl).nnnorm).mono hsub
  obtain ⟨L, hL⟩ := hK.bddAbove_image hc
  refine ⟨L, hconv.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ) (f := f) (fun x hx => ?_) ?_⟩
  · exact (hf.contDiffAt (hΩ.mem_nhds (hsub hx))).differentiableAt le_rfl
  · intro x hx
    exact hL (Set.mem_image_of_mem _ hx)

/-- The quadratic form is linear in the matrix state. -/
def quadraticLinear (d : ℕ) (v : E d) : Tangent d →ₗ[ℝ] ℝ where
  toFun q := quadratic (matrixProjection d q) v
  map_add' q r := by
    simp [quadratic, Matrix.add_mulVec, dotProduct_add]
  map_smul' c q := by
    simp [quadratic, Matrix.smul_mulVec, dotProduct_smul]

/-- The deterministic Gaussian box is convex: both its norm bound and all its
uniform spectral lower bounds are convex constraints. -/
theorem compactBox_convex {d : ℕ} (l B : ℝ) :
    Convex ℝ (GaussianLocalization.compactBox (d := d) l B) := by
  have hn : Convex ℝ {q : Tangent d | ‖q‖ ≤ B} := by
    simpa only [Metric.closedBall, dist_zero_right] using
      (convex_closedBall (0 : Tangent d) B)
  have hs : Convex ℝ {q : Tangent d | ∀ v : E d,
      l * ‖v‖ ^ 2 ≤ quadratic (matrixProjection d q) v} := by
    rw [show {q : Tangent d | ∀ v : E d,
      l * ‖v‖ ^ 2 ≤ quadratic (matrixProjection d q) v} =
      ⋂ v : E d, (quadraticLinear d v) ⁻¹' Set.Ici (l * ‖v‖ ^ 2) by
        ext q; simp [quadraticLinear]]
    exact convex_iInter fun v => (convex_Ici _).linear_preimage (quadraticLinear d v)
  exact hn.inter hs

variable {d : ℕ} {V : E d → ℝ} {α β : ℝ}

/-- Recover the covariance cotangent from the actual Riesz gradient, using the
actual smooth inverse Sylvester differential. -/
def recoveredCotangent (V : E d → ℝ) (q : Tangent d) : Tangent d :=
  HilbertMobility.inverseJ q (gradient (HilbertCoordinates.energy V) q)

theorem recoveredCotangent_eq
    (stein : ExternalGaussianAnalysis.GaussianSteinTheorem d)
    (hV : AdmissiblePotential V α β) (q : Tangent d) (hq : q ∈ Domain d) :
    recoveredCotangent V q = HilbertGradientFlow.covarianceCotangent V hV.regularity q := by
  rw [recoveredCotangent, HilbertGradientFlow.actual_gradient stein hV q hq,
    HilbertMobility.inverseJ_J q _ hq]

/-- This recovered cotangent is C¹ under exactly the original C² potential
hypothesis; Gaussian averaging supplies the extra regularity of Γ. -/
theorem recoveredCotangent_contDiffOn (hV : AdmissiblePotential V α β) :
    ContDiffOn ℝ 1 (recoveredCotangent V) (Domain d) := by
  have hg := GradientGeometry.gradient_contDiffOn (Domain_isOpen d)
    (GaussianEnergyGeometry.intrinsic_energy_contDiffOn hV)
  intro q hq
  exact ((HilbertMobility.inverseJ_contDiffAt 1 q hq).clm_apply
    (hg.contDiffAt ((Domain_isOpen d).mem_nhds hq))).contDiffWithinAt

theorem meanGradient_recovery
    (stein : ExternalGaussianAnalysis.GaussianSteinTheorem d)
    (hV : AdmissiblePotential V α β) (q : Tangent d) (hq : q ∈ Domain d) :
    meanGradient V (meanProjection d q) (matrixProjection d q * matrixProjection d q) =
      meanProjection d (recoveredCotangent V q) := by
  rw [recoveredCotangent_eq stein hV q hq]
  simp only [meanProjection_apply, HilbertGradientFlow.toModel_covarianceCotangent]

theorem meanHessian_recovery
    (stein : ExternalGaussianAnalysis.GaussianSteinTheorem d)
    (hV : AdmissiblePotential V α β) (q : Tangent d) (hq : q ∈ Domain d) :
    meanHessian V (meanProjection d q) (matrixProjection d q * matrixProjection d q) =
      (2 : ℝ) • matrixProjection d (recoveredCotangent V q) +
        (matrixProjection d q * matrixProjection d q)⁻¹ := by
  rw [recoveredCotangent_eq stein hV q hq]
  simp only [matrixProjection_apply, HilbertGradientFlow.toModel_covarianceCotangent,
    Mobility.energyCovGradient]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring

/-- The actual Gaussian mean gradient is C¹ on the full intrinsic SPD domain. -/
theorem meanGradient_contDiffOn
    (stein : ExternalGaussianAnalysis.GaussianSteinTheorem d)
    (hV : AdmissiblePotential V α β) :
    ContDiffOn ℝ 1
      (fun q : Tangent d => meanGradient V (meanProjection d q)
        (matrixProjection d q * matrixProjection d q)) (Domain d) := by
  exact ((meanProjection d).contDiff.comp_contDiffOn
    (recoveredCotangent_contDiffOn hV)).congr
    (fun q hq => meanGradient_recovery stein hV q hq)

/-- The actual Gaussian averaged Hessian is C¹, even though the source assumes
only continuity and boundedness of the pointwise Hessian. -/
theorem meanHessian_contDiffOn
    (stein : ExternalGaussianAnalysis.GaussianSteinTheorem d)
    (hV : AdmissiblePotential V α β) :
    ContDiffOn ℝ 1
      (fun q : Tangent d => meanHessian V (meanProjection d q)
        (matrixProjection d q * matrixProjection d q)) (Domain d) := by
  have hc := (matrixProjection d).contDiff.comp_contDiffOn
    (recoveredCotangent_contDiffOn hV)
  have hi : ContDiffOn ℝ 1
      (fun q : Tangent d => (matrixProjection d q * matrixProjection d q)⁻¹) (Domain d) := by
    intro q hq
    exact ((matrixInverse_contDiffAt (hq.isUnit.mul hq.isUnit)).comp q
      ((matrixProjection d).contDiff.contDiffAt.mul
        (matrixProjection d).contDiff.contDiffAt)).contDiffWithinAt
  exact ((hc.const_smul (2 : ℝ)).add hi).congr
    (fun q hq => meanHessian_recovery stein hV q hq)

/-- C¹ regularity of the literal source coefficient I−ΓA²−mμᵀ. -/
theorem gaussianCoefficient_contDiffOn
    (stein : ExternalGaussianAnalysis.GaussianSteinTheorem d)
    (hV : AdmissiblePotential V α β) :
    ContDiffOn ℝ 1 (fun q : Tangent d =>
      ParticleLimit.gaussianCoefficient V (toModel d q)) (Domain d) := by
  have hΓ := meanHessian_contDiffOn stein hV
  have hm := meanGradient_contDiffOn stein hV
  have hμ := (meanProjection d).contDiff (n := 1) |>.contDiffOn (s := Domain d)
  have hA := (matrixProjection d).contDiff (n := 1) |>.contDiffOn (s := Domain d)
  have ho := ((outerBilinear d).contDiff.comp_contDiffOn hm).clm_apply hμ
  exact (contDiffOn_const.sub (hΓ.mul (hA.mul hA))).sub ho

/-- Flatten the actual coefficient into the same Frobenius Hilbert coordinates
used by the particle comparison. -/
def coefficient (V : E d → ℝ) (q : Tangent d) : Flat d :=
  flattenEquiv d (ParticleLimit.gaussianCoefficient V (toModel d q))

theorem coefficient_contDiffOn
    (stein : ExternalGaussianAnalysis.GaussianSteinTheorem d)
    (hV : AdmissiblePotential V α β) :
    ContDiffOn ℝ 1 (coefficient V) (Domain d) :=
  (flattenEquiv d).contDiff.comp_contDiffOn (gaussianCoefficient_contDiffOn stein hV)

theorem coefficient_lipschitzOn_compact_convex
    (stein : ExternalGaussianAnalysis.GaussianSteinTheorem d)
    (hV : AdmissiblePotential V α β) {K : Set (Tangent d)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hsub : K ⊆ Domain d) :
    ∃ L : ℝ≥0, LipschitzOnWith L (coefficient V) K :=
  exists_lipschitzOnWith_of_compact_convex (Domain_isOpen d)
    (coefficient_contDiffOn stein hV) hK hconv hsub

/-- In particular the deterministic common Gaussian localization box has one
finite coefficient Lipschitz constant, derived from the original hypotheses. -/
theorem coefficient_lipschitzOn_compactBox
    (stein : ExternalGaussianAnalysis.GaussianSteinTheorem d)
    (hV : AdmissiblePotential V α β) (l B : ℝ) (hl : 0 < l) :
    ∃ L : ℝ≥0, LipschitzOnWith L (coefficient V)
      (GaussianLocalization.compactBox (d := d) l B) :=
  coefficient_lipschitzOn_compact_convex stein hV
    (GaussianLocalization.compactBox_isCompact l B) (compactBox_convex l B)
    (GaussianLocalization.compactBox_subset_Domain l B hl)

/-- The Lipschitz estimate has exactly the ambient flattened type used in the
particle comparison; the intrinsic inclusion preserves distances. -/
theorem coefficient_lipschitzOn_ambient_image
    (stein : ExternalGaussianAnalysis.GaussianSteinTheorem d)
    (hV : AdmissiblePotential V α β) {K : Set (Tangent d)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hsub : K ⊆ Domain d) :
    ∃ L : ℝ≥0, LipschitzOnWith L
      (fun u : Ambient d => flattenEquiv d
        (ParticleLimit.gaussianCoefficient V ((ambientEquiv d).symm u)))
      (ambientEquiv d '' (toModel d '' K)) := by
  obtain ⟨L, hL⟩ := coefficient_lipschitzOn_compact_convex stein hV hK hconv hsub
  refine ⟨L, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro u hu v hv
  obtain ⟨r, ⟨q, hq, rfl⟩, rfl⟩ := hu
  obtain ⟨s, ⟨p, hp, rfl⟩, rfl⟩ := hv
  simpa only [ambient_toModel, ContinuousLinearEquiv.symm_apply_apply, coefficient,
    Subtype.dist_eq] using hL.dist_le_mul q hq p hp

/-- Literal coefficient continuity along every continuous intrinsic Gaussian
path remaining in the source SPD domain. -/
theorem gaussianCoefficient_continuousOn_path
    (stein : ExternalGaussianAnalysis.GaussianSteinTheorem d)
    (hV : AdmissiblePotential V α β) {I : Set ℝ} {q : ℝ → Tangent d}
    (hq : ContinuousOn q I) (hmem : Set.MapsTo q I (Domain d)) :
    ContinuousOn (fun t => ParticleLimit.gaussianCoefficient V (toModel d (q t))) I :=
  (gaussianCoefficient_contDiffOn stein hV).continuousOn.comp hq hmem

/-- The source stationarity identities follow from the actual energy critical
point equation; they are not additional variational hypotheses. -/
theorem stationarity_of_gradient_zero
    (stein : ExternalGaussianAnalysis.GaussianSteinTheorem d)
    (hV : AdmissiblePotential V α β) {q : Tangent d} (hq : q ∈ Domain d)
    (hcrit : gradient (HilbertCoordinates.energy V) q = 0) :
    meanGradient V (meanProjection d q) (matrixProjection d q * matrixProjection d q) = 0 ∧
    meanHessian V (meanProjection d q) (matrixProjection d q * matrixProjection d q) =
      (matrixProjection d q * matrixProjection d q)⁻¹ := by
  have hc : recoveredCotangent V q = 0 := by simp [recoveredCotangent, hcrit]
  constructor
  · rw [meanGradient_recovery stein hV q hq, hc, map_zero]
  · rw [meanHessian_recovery stein hV q hq, hc, map_zero, smul_zero, zero_add]

/-- At each actual energy critical point the genuine particle coefficient
vanishes, as required by (6.15). -/
theorem gaussianCoefficient_zero_of_gradient_zero
    (stein : ExternalGaussianAnalysis.GaussianSteinTheorem d)
    (hV : AdmissiblePotential V α β) {q : Tangent d} (hq : q ∈ Domain d)
    (hcrit : gradient (HilbertCoordinates.energy V) q = 0) :
    ParticleLimit.gaussianCoefficient V (toModel d q) = 0 := by
  obtain ⟨hm, hΓ⟩ := stationarity_of_gradient_zero stein hV hq hcrit
  have hu : IsUnit (matrixProjection d q * matrixProjection d q) := hq.isUnit.mul hq.isUnit
  have hd := (Matrix.isUnit_iff_isUnit_det (matrixProjection d q * matrixProjection d q)).mp hu
  change 1 - meanHessian V (meanProjection d q) (matrixProjection d q * matrixProjection d q) *
    (matrixProjection d q * matrixProjection d q) -
      outer (meanGradient V (meanProjection d q) (matrixProjection d q * matrixProjection d q))
        (meanProjection d q) = 0
  rw [hm, hΓ, Matrix.nonsing_inv_mul _ hd]
  ext i j
  simp [outer]

/-- The actual Gaussian energy minimizer satisfies the coefficient cancellation
without separately assuming either source stationarity identity. -/
theorem gaussianCoefficient_zero_of_minimizer
    (stein : ExternalGaussianAnalysis.GaussianSteinTheorem d)
    (hV : AdmissiblePotential V α β) {q : Tangent d} (hq : q ∈ Domain d)
    (hmin : ∀ p ∈ Domain d, HilbertCoordinates.energy V q ≤ HilbertCoordinates.energy V p) :
    ParticleLimit.gaussianCoefficient V (toModel d q) = 0 :=
  gaussianCoefficient_zero_of_gradient_zero stein hV hq
    (GradientGeometry.gradient_eq_zero_of_minimizer (Domain_isOpen d) hq hmin)

/-- Local Lipschitz regularity of the actual averaged Hessian, without any
pointwise Hessian Lipschitz assumption. -/
theorem meanHessian_locallyLipschitzOn
    (stein : ExternalGaussianAnalysis.GaussianSteinTheorem d)
    (hV : AdmissiblePotential V α β) :
    LocallyLipschitzOn (Domain d) (fun q : Tangent d =>
      meanHessian V (meanProjection d q) (matrixProjection d q * matrixProjection d q)) := by
  intro q hq
  obtain ⟨L, U, hU, hL⟩ := ((meanHessian_contDiffOn stein hV).contDiffAt
    ((Domain_isOpen d).mem_nhds hq)).exists_lipschitzOnWith
  exact ⟨L, U, nhdsWithin_le_nhds hU, hL⟩

/-- Actual Gaussian energy sublevels are convex, derived from the proven
quadratic lower bound on the actual energy Hessian. -/
theorem energy_sublevel_convex (hV : AdmissiblePotential V α β) (c : ℝ) :
    Convex ℝ {q : Tangent d | q ∈ Domain d ∧ HilbertCoordinates.energy V q ≤ c} := by
  have hs : EnergyDecay.StrongConvexGradientOn (HilbertCoordinates.energy V)
      (gradient (HilbertCoordinates.energy V)) (Domain d) α :=
    GradientGeometry.strongConvexGradientOn_of_second_fderiv_lower
      (E := Tangent d) (F := HilbertCoordinates.energy V) (Ω := Domain d) (α := α)
    (Domain_isOpen d) (Domain_convex d)
    (GaussianEnergyGeometry.intrinsic_energy_contDiffOn hV)
    (fun q hq v => GaussianEnergyGeometry.intrinsic_energy_second_fderiv_lower hV q v hq)
  have hf : ConvexOn ℝ (Domain d) (HilbertCoordinates.energy V) :=
    GradientGeometry.convexOn_of_strongConvexGradientOn
      (E := Tangent d) (F := HilbertCoordinates.energy V)
      (G := gradient (HilbertCoordinates.energy V)) (Ω := Domain d) (α := α)
      (Domain_convex d) hV.alpha_pos.le hs
  exact hf.convex_le c

/-- One common actual coefficient Lipschitz constant exists on each energy
sublevel, with compactness and convexity proved from the source hypotheses. -/
theorem coefficient_lipschitzOn_energy_sublevel
    (stein : ExternalGaussianAnalysis.GaussianSteinTheorem d)
    (hV : AdmissiblePotential V α β) (c : ℝ) :
    ∃ L : ℝ≥0, LipschitzOnWith L (coefficient V)
      {q : Tangent d | q ∈ Domain d ∧ HilbertCoordinates.energy V q ≤ c} :=
  coefficient_lipschitzOn_compact_convex stein hV
    (EnergyCompactness.gaussian_energy_sublevel_compact_from_geometry hV
      (GaussianEnergyGeometry.intrinsic_energy_contDiffOn hV)
      (fun q hq v => GaussianEnergyGeometry.intrinsic_energy_second_fderiv_lower hV q v hq) c)
    (energy_sublevel_convex hV c) (fun _ hq => hq.1)

/-- The source particle comparison may use the energy-sublevel Lipschitz
constant directly in its flattened ambient coordinates. -/
theorem coefficient_lipschitzOn_ambient_energy_sublevel
    (stein : ExternalGaussianAnalysis.GaussianSteinTheorem d)
    (hV : AdmissiblePotential V α β) (c : ℝ) :
    ∃ L : ℝ≥0, LipschitzOnWith L
      (fun u : Ambient d => flattenEquiv d
        (ParticleLimit.gaussianCoefficient V ((ambientEquiv d).symm u)))
      (ambientEquiv d '' (toModel d ''
        {q : Tangent d | q ∈ Domain d ∧ HilbertCoordinates.energy V q ≤ c})) :=
  coefficient_lipschitzOn_ambient_image stein hV
    (EnergyCompactness.gaussian_energy_sublevel_compact_from_geometry hV
      (GaussianEnergyGeometry.intrinsic_energy_contDiffOn hV)
      (fun q hq v => GaussianEnergyGeometry.intrinsic_energy_second_fderiv_lower hV q v hq) c)
    (energy_sublevel_convex hV c) (fun _ hq => hq.1)

end Paper38.CoefficientRegularity
