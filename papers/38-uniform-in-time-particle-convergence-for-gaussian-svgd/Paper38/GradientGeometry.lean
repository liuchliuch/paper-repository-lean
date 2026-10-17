import Paper38.EnergyDecay
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Riesz-gradient geometry derived from actual C² scalar energies. -/

noncomputable section
namespace Paper38.GradientGeometry

open Set InnerProductSpace
open scoped InnerProductSpace Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The Hessian operator is the Riesz representation of the actual second derivative. -/
def hessianOperator (F : E → ℝ) (x : E) : E →L[ℝ] E :=
  continuousLinearMapOfBilin (fderiv ℝ (fderiv ℝ F) x)

/-- Actual derivative represented by the actual Riesz gradient. -/
theorem hasFDerivAt_gradient_repr {F : E → ℝ} {x : E}
    (hF : DifferentiableAt ℝ F x) : HasFDerivAt F (innerSL ℝ (gradient F x)) x :=
  hF.hasGradientAt.hasFDerivAt

/-- Differentiating the actual gradient differentiates the actual first derivative. -/
theorem gradient_hasFDerivAt {F : E → ℝ} {x : E}
    (hF : DifferentiableAt ℝ (fderiv ℝ F) x) :
    HasFDerivAt (gradient F) (hessianOperator F x) x := by
  exact ((toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt).comp x
    hF.hasFDerivAt

@[simp] theorem hessianOperator_inner (F : E → ℝ) (x v w : E) :
    ⟪hessianOperator F x v, w⟫_ℝ = (fderiv ℝ (fderiv ℝ F) x v) w :=
  continuousLinearMapOfBilin_apply _ _ _

/-- An actual C² energy has a C¹ Riesz gradient on any open domain. -/
theorem gradient_contDiffOn {F : E → ℝ} {Ω : Set E}
    (hΩ : IsOpen Ω) (hF : ContDiffOn ℝ 2 F Ω) : ContDiffOn ℝ 1 (gradient F) Ω := by
  intro x hx
  have hd : ContDiffAt ℝ 1 (fderiv ℝ F) x :=
    (hF.contDiffAt (hΩ.mem_nhds hx)).fderiv_right (by norm_num)
  exact (((toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contDiffAt).comp x hd).contDiffWithinAt

/-- The original lower bound on the second Fréchet derivative implies the
standard first-order strong-convexity inequality for the actual Riesz gradient. -/
theorem strongConvexGradientOn_of_second_fderiv_lower {F : E → ℝ} {Ω : Set E} {α : ℝ}
    (hΩ : IsOpen Ω) (hΩconv : Convex ℝ Ω) (hF : ContDiffOn ℝ 2 F Ω)
    (hlower : ∀ x ∈ Ω, ∀ v : E,
      α * ‖v‖^2 ≤ (fderiv ℝ (fderiv ℝ F) x v) v) :
    EnergyDecay.StrongConvexGradientOn F (gradient F) Ω α := by
  apply EnergyDecay.strongConvexGradientOn_of_hessian_lower (A := hessianOperator F) hΩconv
  · intro x hx
    exact hasFDerivAt_gradient_repr
      ((hF.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by norm_num))
  · intro x hx
    apply gradient_hasFDerivAt
    exact ((hF.contDiffAt (hΩ.mem_nhds hx)).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  · intro x hx v
    have hinner : ⟪v, hessianOperator F x v⟫_ℝ =
        (fderiv ℝ (fderiv ℝ F) x v) v := by
      calc
        ⟪v, hessianOperator F x v⟫_ℝ = ⟪hessianOperator F x v, v⟫_ℝ := real_inner_comm _ _
        _ = _ := hessianOperator_inner _ _ _ _
    rw [hinner]
    exact hlower x hx v

/-- The standard first-order strong-convexity inequality implies ordinary
convexity, hence convexity of every energy sublevel. -/
theorem convexOn_of_strongConvexGradientOn {F : E → ℝ} {G : E → E} {Ω : Set E} {α : ℝ}
    (hΩ : Convex ℝ Ω) (hα : 0 ≤ α)
    (hstrong : EnergyDecay.StrongConvexGradientOn F G Ω α) : ConvexOn ℝ Ω F := by
  refine ⟨hΩ, ?_⟩
  intro x hx y hy a b ha hb hab
  let z := a • x+b • y
  have hz : z ∈ Ω := hΩ hx hy ha hb hab
  have hzx := hstrong z hz x hx
  have hzy := hstrong z hz y hy
  have hqx : 0 ≤ α/2 * ‖x-z‖^2 := by positivity
  have hqy : 0 ≤ α/2 * ‖y-z‖^2 := by positivity
  have hxweak : F z+⟪G z, x-z⟫_ℝ ≤ F x := by linarith
  have hyweak : F z+⟪G z, y-z⟫_ℝ ≤ F y := by linarith
  have hax := mul_le_mul_of_nonneg_left hxweak ha
  have hby := mul_le_mul_of_nonneg_left hyweak hb
  have hvec : a • (x-z)+b • (y-z) = (0:E) := by
    calc
      a • (x-z)+b • (y-z) = a • x+b • y-(a+b) • z := by module
      _ = 0 := by rw [hab, one_smul]; exact sub_self z
  have hcancel := congrArg (fun v => ⟪G z, v⟫_ℝ) hvec
  simp only [inner_add_right, inner_smul_right, inner_zero_right] at hcancel
  change F z ≤ a * F x+b * F y
  have hsum : a*F z+b*F z = F z := by rw [← add_mul, hab, one_mul]
  nlinarith

/-- A compact nonempty energy sublevel constructs a minimizer before any
critical-point or convergence statement is used. -/
theorem exists_minimizer_of_compact_sublevel {F : E → ℝ} {Ω : Set E} {a : E}
    (ha : a ∈ Ω) (hF : ContinuousOn F Ω)
    (hcompact : IsCompact {x | x ∈ Ω ∧ F x ≤ F a}) :
    ∃ z ∈ Ω, ∀ x ∈ Ω, F z ≤ F x := by
  obtain ⟨z, hz, hzmin⟩ := hcompact.exists_isMinOn ⟨a, ha, le_refl _⟩
    (hF.mono (fun _ hx => hx.1))
  refine ⟨z, hz.1, ?_⟩
  intro x hx
  by_cases hxa : F x ≤ F a
  · exact hzmin ⟨hx, hxa⟩
  · exact hz.2.trans (lt_of_not_ge hxa).le

/-- A differentiable minimizer in the open energy domain has zero actual gradient. -/
theorem gradient_eq_zero_of_minimizer {F : E → ℝ} {Ω : Set E} {z : E}
    (hΩ : IsOpen Ω) (hz : z ∈ Ω) (hmin : ∀ x ∈ Ω, F z ≤ F x) :
    gradient F z = 0 := by
  have hlocal : IsLocalMin F z := (show IsMinOn F Ω z from hmin).isLocalMin (hΩ.mem_nhds hz)
  simp only [gradient, hlocal.fderiv_eq_zero, map_zero]

/-- Strong convexity makes a critical minimizer unique on its domain. -/
theorem unique_of_strongConvex_critical {F : E → ℝ} {Ω : Set E} {α : ℝ}
    (hα : 0 < α) (hstrong : EnergyDecay.StrongConvexGradientOn F (gradient F) Ω α)
    {z x : E} (hz : z ∈ Ω) (hx : x ∈ Ω) (hcrit : gradient F z = 0)
    (heq : F x = F z) : x = z := by
  have h := EnergyDecay.distance_coercivity hstrong hz hx hcrit
  rw [heq, sub_self] at h
  have hsq : ‖x-z‖^2 ≤ 0 :=
    (mul_le_mul_left (by positivity : 0 < α/2)).mp (by simpa only [mul_zero] using h)
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hsq (sq_nonneg _))))

end Paper38.GradientGeometry
