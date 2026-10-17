import Paper38.HilbertGradientFlow
import Paper38.GaussianEnergyFacts
import Paper38.GradientWithin
import Paper38.SourceCoordinates
import Paper38.WithinEnergyDecay

/-! Actual Model energy trapping for arbitrary source within0 moment paths. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace Paper38.MomentEnergy
open Set
open Model HilbertCoordinates Specification
open scoped Matrix Matrix.Norms.Frobenius

variable {d : ℕ} {V : E d → ℝ} {α β : ℝ}

/-- The principal lift has exactly the source energy along every actual path. -/
theorem energy_principalLift (p : MomentPath d) (hp : momentSolution V p.mean p.cov)
    (t : ℝ) (ht : 0 ≤ t) :
    HilbertCoordinates.energy V (HilbertGradientFlow.principalLift p.mean p.cov t) =
      Model.energy V (p.q t) := by
  unfold HilbertCoordinates.energy
  rw [HilbertGradientFlow.toModel_principalLift _ _ t (hp.1 t ht)]
  rfl

/-- Actual raw-model energy decreases for arbitrary source moment paths,
including their physical-time-zero within derivative convention. -/
theorem energy_nonincreasing
    (stein : ExternalGaussianAnalysis.GaussianSteinTheorem d)
    (sqrt : ExternalMatrixAnalysis.PrincipalRootDifferentiation d)
    (hV : AdmissiblePotential V α β) (p : MomentPath d)
    (hp : momentSolution V p.mean p.cov) (t : ℝ) (ht : 0 ≤ t) :
    Model.energy V (p.q t) ≤ Model.energy V (p.q 0) := by
  obtain ⟨hdom,hpath⟩ := HilbertGradientFlow.momentSolution_gradientPath stein sqrt hV p.mean p.cov hp
  have hF : ∀ x ∈ Domain d, HasFDerivAt (HilbertCoordinates.energy V)
      (innerSL ℝ (gradient (HilbertCoordinates.energy V) x)) x := by
    intro x hx
    exact GradientGeometry.hasFDerivAt_gradient_repr
      (((GaussianEnergyGeometry.intrinsic_energy_contDiffOn hV).contDiffAt
        ((Domain_isOpen d).mem_nhds hx)).differentiableAt (by norm_num))
  have h := GradientWithin.energy_nonincreasing ht hF
    (fun x hx v => HilbertMobility.P_quadratic_nonneg (d := d) x v hx) hdom hpath
  simpa only [energy_principalLift p hp t ht, energy_principalLift p hp 0 (le_refl 0)] using h

/-- Source squared Euclidean--Frobenius distance to the optimal Gaussian is
controlled by the initial energy gap for every actual moment trajectory. -/
theorem coordinateSqDist_le_initial_gap
    (stein : ExternalGaussianAnalysis.GaussianSteinTheorem d)
    (sqrt : ExternalMatrixAnalysis.PrincipalRootDifferentiation d)
    (hV : AdmissiblePotential V α β) (p : MomentPath d)
    (hp : momentSolution V p.mean p.cov) (qstar : Coordinates d)
    (hstar : Specification.IsMinimizer V qstar) (t : ℝ) (ht : 0 ≤ t) :
    coordinateSqDist (p.q t) qstar ≤ (2/α) *
      (Model.energy V (p.q 0)-Model.energy V qstar) := by
  obtain ⟨z,hzraw,hz,hmin⟩ := SourceCoordinates.lift_source_minimizer hstar
  obtain ⟨hdom,hpath⟩ := HilbertGradientFlow.momentSolution_gradientPath stein sqrt hV p.mean p.cov hp
  have hcrit := GradientGeometry.gradient_eq_zero_of_minimizer (Domain_isOpen d) hz hmin
  have hc := EnergyDecay.distance_coercivity (GaussianGradientFlow.strongly_convex hV)
    hz (hdom t ht) hcrit
  have hcoord : coordinateSqDist (p.q t) qstar =
      ‖HilbertGradientFlow.principalLift p.mean p.cov t-z‖^2 := by
    have hraw : toModel d (HilbertGradientFlow.principalLift p.mean p.cov t) = p.q t :=
      HilbertGradientFlow.toModel_principalLift _ _ t (hp.1 t ht)
    rw [← hraw, ← hzraw]
    exact coordinateSqDist_toModel _ _
  have hzenergy : HilbertCoordinates.energy V z = Model.energy V qstar := by
    simp only [HilbertCoordinates.energy, hzraw]
  rw [energy_principalLift p hp t ht, hzenergy, ← hcoord] at hc
  have he := energy_nonincreasing stein sqrt hV p hp t ht
  apply (mul_le_mul_left (div_pos hV.alpha_pos (by norm_num) : 0 < α/2)).mp
  calc
    α/2 * coordinateSqDist (p.q t) qstar ≤ Model.energy V (p.q 0)-Model.energy V qstar := by linarith
    _ = α/2 * ((2/α) * (Model.energy V (p.q 0)-Model.energy V qstar)) := by
      field_simp [hV.alpha_pos.ne']

/-- Uniform source sublevel trapping and exponential attraction. The constants
are chosen before the moment trajectory and cover the degenerate radius R=0. -/
theorem uniform_decay
    (stein : ExternalGaussianAnalysis.GaussianSteinTheorem d)
    (sqrt : ExternalMatrixAnalysis.PrincipalRootDifferentiation d)
    (hV : AdmissiblePotential V α β) (qstar : Coordinates d)
    (hstar : Specification.IsMinimizer V qstar) (R : ℝ) (hR : 0 ≤ R) :
    ∃ Q ≥ 0, ∃ decay > 0, ∀ p : MomentPath d,
      momentSolution V p.mean p.cov → p.q 0 ∈ sublevel V qstar R →
      ∀ t, 0 ≤ t → p.q t ∈ sublevel V qstar R ∧
        coordinateSqDist (p.q t) qstar ≤ Q * Real.exp (-2*decay*t) := by
  obtain ⟨z,hzraw,hz,hmin⟩ := SourceCoordinates.lift_source_minimizer hstar
  let K : Set (Tangent d) := {q | q ∈ Domain d ∧
    HilbertCoordinates.energy V q ≤ Model.energy V qstar + R}
  have hK : IsCompact K := GaussianGradientFlow.sublevel_isCompact hV _
  obtain ⟨p₀,hp₀,hell⟩ := CompactEllipticity.exists_uniform_lower
    (P := HilbertMobility.P (d := d)) hK
    ((HilbertMobility.P_contDiffOn (d := d) 1).continuousOn.mono (fun _ hx => hx.1))
    (fun q hq v hv => HilbertMobility.P_quadratic_pos q v hq.1 hv)
  refine ⟨2*R/α, by exact div_nonneg (mul_nonneg (by norm_num) hR) hV.alpha_pos.le,
    α*p₀, mul_pos hV.alpha_pos hp₀, ?_⟩
  intro p hp hi t ht
  obtain ⟨hdom,hpath⟩ := HilbertGradientFlow.momentSolution_gradientPath stein sqrt hV p.mean p.cov hp
  have hetrap : ∀ s, 0 ≤ s → Model.energy V (p.q s) ≤ Model.energy V qstar + R := by
    intro s hs
    have he := energy_nonincreasing stein sqrt hV p hp s hs
    linarith [hi.2]
  have hmem : ∀ s, 0 ≤ s → HilbertGradientFlow.principalLift p.mean p.cov s ∈ K := by
    intro s hs
    exact ⟨hdom s hs, by rw [energy_principalLift p hp s hs]; exact hetrap s hs⟩
  have hF : ∀ x ∈ Domain d, HasFDerivAt (HilbertCoordinates.energy V)
      (innerSL ℝ (gradient (HilbertCoordinates.energy V) x)) x := by
    intro x hx
    exact GradientGeometry.hasFDerivAt_gradient_repr
      (((GaussianEnergyGeometry.intrinsic_energy_contDiffOn hV).contDiffAt
        ((Domain_isOpen d).mem_nhds hx)).differentiableAt (by norm_num))
  have he := WithinEnergyDecay.energy_exponential_decay hV.alpha_pos hp₀.le ht
    (GaussianGradientFlow.strongly_convex hV) hz hF hpath hdom
    (fun s hs v => hell _ (hmem s hs) v)
  have hcrit := GradientGeometry.gradient_eq_zero_of_minimizer (Domain_isOpen d) hz hmin
  have hc := EnergyDecay.distance_coercivity (GaussianGradientFlow.strongly_convex hV)
    hz (hdom t ht) hcrit
  have hcoord : coordinateSqDist (p.q t) qstar =
      ‖HilbertGradientFlow.principalLift p.mean p.cov t-z‖^2 := by
    have hraw : toModel d (HilbertGradientFlow.principalLift p.mean p.cov t) = p.q t :=
      HilbertGradientFlow.toModel_principalLift _ _ t (hp.1 t ht)
    rw [← hraw, ← hzraw]
    exact coordinateSqDist_toModel _ _
  have hzenergy : HilbertCoordinates.energy V z = Model.energy V qstar := by
    simp only [HilbertCoordinates.energy, hzraw]
  rw [energy_principalLift p hp t ht, energy_principalLift p hp 0 le_rfl, hzenergy] at he
  rw [energy_principalLift p hp t ht, hzenergy, ← hcoord] at hc
  refine ⟨⟨(hp.1 t ht).posDef_sqrt, by linarith [hetrap t ht]⟩, ?_⟩
  have he' : Model.energy V (p.q t)-Model.energy V qstar ≤
      R*Real.exp (-2*(α*p₀)*t) := by
    have he0 := mul_le_mul_of_nonneg_right hi.2 (Real.exp_pos (-2*α*p₀*t)).le
    have hexp : -2*α*p₀*t = -2*(α*p₀)*t := by ring
    rw [hexp] at he he0
    exact he.trans he0
  apply (mul_le_mul_left (div_pos hV.alpha_pos (by norm_num) : 0 < α/2)).mp
  calc
    α/2 * coordinateSqDist (p.q t) qstar ≤ R*Real.exp (-2*(α*p₀)*t) := hc.trans he'
    _ = α/2 * (2*R/α * Real.exp (-2*(α*p₀)*t)) := by
      field_simp [hV.alpha_pos.ne']


end Paper38.MomentEnergy
