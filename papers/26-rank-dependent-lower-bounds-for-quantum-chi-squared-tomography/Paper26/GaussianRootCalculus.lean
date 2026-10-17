import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! Native calculus and Dirichlet energy of any scalar Gaussian root profile.
No normalization, moment, probability, weak-analysis or prior theorem is
assumed here. The integral corollary uses an explicit ordinary second moment. -/
noncomputable section
open MeasureTheory
namespace Paper26.GaussianRootCalculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def profile (c v : ℝ) (x : E) : ℝ :=
  c * Real.exp (-‖x‖^2/(4*v))

theorem hasFDerivAt_profile (c v : ℝ) (hv : 0 < v) (x : E) :
    HasFDerivAt (profile c v) ((-profile c v x/(2*v)) • innerSL ℝ x) x := by
  have ha : HasFDerivAt (fun y : E => -‖y‖^2/(4*v))
      (((4*v)⁻¹ : ℝ) • (-((2 : ℝ) • innerSL ℝ x))) x := by
    have hh := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.neg.const_smul ((4*v)⁻¹ : ℝ))
    have he : ((4*v)⁻¹ : ℝ) • (-(fun y : E => ‖y‖^2)) =
        (fun y : E => -‖y‖^2/(4*v)) := by
      funext y
      change (4*v)⁻¹ * (-‖y‖^2) = -‖y‖^2/(4*v)
      ring
    rw [he] at hh
    simpa only [two_smul] using hh
  have h := ha.exp.const_mul c
  convert h using 1
  ext y
  simp only [ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.neg_apply, smul_eq_mul, profile]
  field_simp [hv.ne']
  ring

theorem fderiv_profile (c v : ℝ) (hv : 0 < v) (x : E) :
    fderiv ℝ (profile c v) x = (-profile c v x/(2*v)) • innerSL ℝ x :=
  (hasFDerivAt_profile c v hv x).fderiv

theorem norm_fderiv_sq (c v : ℝ) (hv : 0 < v) (x : E) :
    ‖fderiv ℝ (profile c v) x‖^2 =
      ‖x‖^2 * (profile c v x)^2 / (4*v^2) := by
  rw [fderiv_profile c v hv x, norm_smul, innerSL_apply_norm, mul_pow,
    Real.norm_eq_abs, sq_abs]
  field_simp [hv.ne']
  ring

theorem integrable_energy [MeasurableSpace E] (μ : Measure E) (c v : ℝ) (hv : 0 < v)
    (hi : Integrable (fun x => ‖x‖^2*(profile c v x)^2) μ) :
    Integrable (fun x => ‖fderiv ℝ (profile c v) x‖^2) μ := by
  simpa only [norm_fderiv_sq c v hv] using hi.div_const (4*v^2)

theorem integral_energy [MeasurableSpace E] (μ : Measure E) (c v p : ℝ) (hv : 0 < v)
    (hm : (∫ x, ‖x‖^2*(profile c v x)^2 ∂μ) = p*v) :
    (∫ x, ‖fderiv ℝ (profile c v) x‖^2 ∂μ) = p/(4*v) := by
  simp_rw [norm_fderiv_sq c v hv]
  rw [integral_div, hm]
  field_simp [hv.ne']

end Paper26.GaussianRootCalculus
