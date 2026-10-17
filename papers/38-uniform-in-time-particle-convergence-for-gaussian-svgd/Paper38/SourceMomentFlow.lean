import Paper38.HilbertGradientFlow
import Paper38.GaussianGradientFlow
import Paper38.SourceCoordinates
import Paper38.ExternalAnalyticInputs

/-! The actual source MomentPath contracts: uniform stability, global existence
and uniqueness for arbitrary physical-time within-domain solutions. Standard
analysis inputs are supplied as ordinary explicit baseline arguments. -/
noncomputable section
open scoped Matrix MatrixOrder Matrix.Norms.Frobenius

namespace Paper38.SourceMomentFlow
open Model HilbertCoordinates Specification
variable {d : ℕ} {V : E d → ℝ} {α β : ℝ}
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 100000

/-- Exact source squared distance in principal-root coordinates. -/
theorem distance_principalLift (p r : MomentPath d) (t : ℝ)
    (hp : (p.cov t).PosDef) (hr : (r.cov t).PosDef) :
    coordinateSqDist (p.q t) (r.q t) =
      ‖HilbertGradientFlow.principalLift p.mean p.cov t -
        HilbertGradientFlow.principalLift r.mean r.cov t‖ ^ 2 := by
  simpa only [HilbertGradientFlow.toModel_principalLift _ _ t hp,
    HilbertGradientFlow.toModel_principalLift _ _ t hr, MomentPath.q, covarianceRoot] using
    coordinateSqDist_toModel (HilbertGradientFlow.principalLift p.mean p.cov t)
      (HilbertGradientFlow.principalLift r.mean r.cov t)

/-- Lemma 5.1 with precisely the raw source quantifiers and arbitrary within0
moment trajectories. Only the standard Stein/square-root analysis is supplied. -/
theorem lemma51_at (stein : ExternalGaussianAnalysis.GaussianSteinTheorem d)
    (sqrt : ExternalMatrixAnalysis.PrincipalRootDifferentiation d)
    (hV : AdmissiblePotential V α β) (qstar : Coordinates d)
    (hstar : Specification.IsUniqueMinimizer V qstar) (R : ℝ) (hR : 0 ≤ R) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ p r : MomentPath d,
      momentSolution V p.mean p.cov → momentSolution V r.mean r.cov →
      p.q 0 ∈ sublevel V qstar R → r.q 0 ∈ sublevel V qstar R →
      ∀ t : ℝ, 0 ≤ t → coordinateSqDist (p.q t) (r.q t) ≤
        S ^ 2 * coordinateSqDist (p.q 0) (r.q 0) := by
  obtain ⟨z, hzraw, hz, hmin⟩ := SourceCoordinates.lift_source_minimizer hstar.1
  obtain ⟨S, hS, T, hT, k, hk, hstable⟩ :=
    GaussianGradientFlow.semiglobal_within hV hR hz hmin
  refine ⟨S, hS.le, ?_⟩
  intro p r hp hr hpR hrR t ht
  rcases HilbertGradientFlow.momentSolution_gradientPath stein sqrt hV p.mean p.cov hp with ⟨hpΩ, hpD⟩
  rcases HilbertGradientFlow.momentSolution_gradientPath stein sqrt hV r.mean r.cov hr with ⟨hrΩ, hrD⟩
  have hpe : HilbertCoordinates.energy V (HilbertGradientFlow.principalLift p.mean p.cov 0) -
      HilbertCoordinates.energy V z ≤ R := by
    rw [HilbertCoordinates.energy, HilbertCoordinates.energy,
      HilbertGradientFlow.toModel_principalLift _ _ 0 (hp.1 0 le_rfl), hzraw]
    exact hpR.2
  have hre : HilbertCoordinates.energy V (HilbertGradientFlow.principalLift r.mean r.cov 0) -
      HilbertCoordinates.energy V z ≤ R := by
    rw [HilbertCoordinates.energy, HilbertCoordinates.energy,
      HilbertGradientFlow.toModel_principalLift _ _ 0 (hr.1 0 le_rfl), hzraw]
    exact hrR.2
  have hbound := (hstable (HilbertGradientFlow.principalLift p.mean p.cov)
    (HilbertGradientFlow.principalLift r.mean r.cov) hpD hrD hpΩ hrΩ hpe hre).1 t ht
  rw [distance_principalLift p r t (hp.1 t ht) (hr.1 t ht),
    distance_principalLift p r 0 (hp.1 0 le_rfl) (hr.1 0 le_rfl)]
  have hsq := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg hS.le (norm_nonneg _))).mpr hbound
  simpa only [mul_pow] using hsq

/-- The complete literal Lemma 5.1 specification, conditional only on named
standard baseline analysis theorems in every dimension. -/
theorem lemma51 (extern : ∀ d : ℕ, ExternalAnalyticInputs.Baselines d) : Specification.Lemma51 := by
  intro d V α β hV qstar hstar R hR
  exact lemma51_at (extern d).stein (extern d).sqrt hV qstar hstar R hR

private theorem state_eq_of_distance_zero (p r : MomentPath d) (t : ℝ)
    (hp : (p.cov t).PosDef) (hr : (r.cov t).PosDef)
    (hzero : coordinateSqDist (p.q t) (r.q t) = 0) :
    p.mean t = r.mean t ∧ p.cov t = r.cov t := by
  rw [coordinateSqDist_eq_norm_ambient] at hzero
  have heq : p.q t = r.q t := (ambientEquiv d).injective
    (sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hzero)))
  have hmean := congrArg Prod.fst heq
  have hroot := congrArg Prod.snd heq
  change CFC.sqrt (p.cov t) = CFC.sqrt (r.cov t) at hroot
  refine ⟨hmean, ?_⟩
  calc
    p.cov t = CFC.sqrt (p.cov t) * CFC.sqrt (p.cov t) :=
      (CFC.sqrt_mul_sqrt_self _ hp.posSemidef.nonneg).symm
    _ = CFC.sqrt (r.cov t) * CFC.sqrt (r.cov t) := by rw [hroot]
    _ = r.cov t := CFC.sqrt_mul_sqrt_self _ hr.posSemidef.nonneg

/-- Any two actual source solutions with the same initial moments agree for
all nonnegative physical times, including arbitrary within-domain solutions. -/
theorem momentPath_unique (stein : ExternalGaussianAnalysis.GaussianSteinTheorem d)
    (sqrt : ExternalMatrixAnalysis.PrincipalRootDifferentiation d)
    (hV : AdmissiblePotential V α β) (μ : E d) (C : Mat d)
    (p r : MomentPath d) (hp : IsMomentPathFrom V μ C p) (hr : IsMomentPathFrom V μ C r) :
    ∀ t, 0 ≤ t → p.mean t = r.mean t ∧ p.cov t = r.cov t := by
  obtain ⟨z, hz, hcrit, hstar⟩ := GaussianGradientFlow.exists_unique_minimizer hV
  let R := max 0 (Model.energy V (μ, CFC.sqrt C) - Model.energy V (toModel d z))
  have hR : 0 ≤ R := le_max_left _ _
  have hsub (p : MomentPath d) (hp : IsMomentPathFrom V μ C p) :
      p.q 0 ∈ sublevel V (toModel d z) R := by
    constructor
    · change (CFC.sqrt (p.cov 0)).PosDef
      exact (hp.1.1 0 le_rfl).posDef_sqrt
    · change Model.energy V (p.mean 0, CFC.sqrt (p.cov 0)) - Model.energy V (toModel d z) ≤ R
      rw [hp.2.1, hp.2.2]
      exact le_max_right _ _
  obtain ⟨S, hS, hbound⟩ := lemma51_at stein sqrt hV (toModel d z) hstar R hR
  intro t ht
  have hdist := hbound p r hp.1 hr.1 (hsub p hp) (hsub r hr) t ht
  have hzero0 : coordinateSqDist (p.q 0) (r.q 0) = 0 := by
    simp [MomentPath.q, hp.2.1, hp.2.2, hr.2.1, hr.2.2, coordinateSqDist, frobSq]
  rw [hzero0, mul_zero] at hdist
  have hn : 0 ≤ coordinateSqDist (p.q t) (r.q t) := by
    rw [coordinateSqDist_eq_norm_ambient]
    exact sq_nonneg _
  exact state_eq_of_distance_zero p r t (hp.1.1 t ht) (hr.1.1 t ht) (le_antisymm hdist hn)

/-- Actual global source moment well-posedness. Existence is constructed from
the proved Gaussian geometry and the textbook maximal-ODE input; uniqueness
covers every solution in the original within0 source definition. -/
theorem momentWellPosed (extern : ExternalAnalyticInputs.Baselines d)
    (hV : AdmissiblePotential V α β) (μ : E d) (C : Mat d) (hC : C.PosDef) :
    Specification.MomentWellPosed V μ C := by
  let x := SourceCoordinates.lift (μ, C) hC
  let x₀ := ExternalMatrixAnalysis.principalRoot x
  have hx₀ : x₀ ∈ Domain d := ExternalMatrixAnalysis.principalRoot_mem_Domain x
    (SourceCoordinates.lift_mem_Domain (μ, C) hC)
  have hxraw : toModel d x₀ = (μ, CFC.sqrt C) := by
    simp only [x₀, x, ExternalMatrixAnalysis.toModel_principalRoot,
      meanProjection_apply, matrixProjection_apply, SourceCoordinates.toModel_lift]
  obtain ⟨z, hz, hmin, hcrit, p, hp, q, hq0, hq, huniq⟩ :=
    GaussianGradientFlow.exists_unique_global_flow extern.standardMaximalODE hV hx₀
  let sol : MomentPath d := {
    mean := fun t => meanProjection d (q t)
    cov := fun t => matrixProjection d (q t) * matrixProjection d (q t) }
  have hsol : momentSolution V sol.mean sol.cov := by
    apply HilbertGradientFlow.gradientPath_momentSolution extern.stein hV q
      (fun t ht => (hq t ht).1)
    intro t ht
    exact (hq t ht).2.1.hasDerivWithinAt
  have hmean : sol.mean 0 = μ := by
    change meanProjection d (q 0) = μ
    rw [hq0]
    exact congrArg Prod.fst hxraw
  have hcov : sol.cov 0 = C := by
    change matrixProjection d (q 0) * matrixProjection d (q 0) = C
    rw [hq0]
    change (toModel d x₀).2 * (toModel d x₀).2 = C
    rw [hxraw]
    exact CFC.sqrt_mul_sqrt_self _ hC.posSemidef.nonneg
  have hfrom : IsMomentPathFrom V μ C sol := ⟨hsol, hmean, hcov⟩
  refine ⟨sol, hfrom, ?_⟩
  intro r hr
  exact momentPath_unique extern.stein extern.sqrt hV μ C r sol hr hfrom

end Paper38.SourceMomentFlow
