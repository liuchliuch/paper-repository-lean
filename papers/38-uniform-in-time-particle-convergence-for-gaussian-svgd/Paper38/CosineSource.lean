import Paper38.CosineExample
import Paper38.Specification
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Example 9.1 as an instance of the literal source Gaussian theorem

The scalar cosine potential is transported into `Model.E 1`; its actual
Fréchet Hessian is computed, so admissibility is proved in precisely the model
used by Theorem 2.2 rather than asserted for a separate scalar abstraction.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace Paper38.CosineSource
open Paper38.Model Paper38.Specification

/-- The unique real coordinate in the one-dimensional model Euclidean space. -/
def scalarCoordinate : E 1 →L[ℝ] ℝ := EuclideanSpace.proj 0

@[simp] theorem scalarCoordinate_apply (x : E 1) : scalarCoordinate x = x 0 := rfl

/-- The literal Model potential of Example 9.1. -/
def potential (ε : ℝ) (x : E 1) : ℝ := Cosine.potential ε (scalarCoordinate x)

theorem potential_hasFDerivAt (ε : ℝ) (x : E 1) :
    HasFDerivAt (potential ε) (Cosine.force ε (scalarCoordinate x) • scalarCoordinate) x :=
  (Cosine.hasDerivAt_potential ε (scalarCoordinate x)).comp_hasFDerivAt x scalarCoordinate.hasFDerivAt

theorem potential_fderiv (ε : ℝ) (x : E 1) :
    fderiv ℝ (potential ε) x = Cosine.force ε (scalarCoordinate x) • scalarCoordinate :=
  (potential_hasFDerivAt ε x).fderiv

/-- The exact actual second Fréchet variation, before any source bounds. -/
theorem potential_second_variation (ε : ℝ) (x u v : E 1) :
    fderiv ℝ (fderiv ℝ (potential ε)) x u v =
      Cosine.curvature ε (scalarCoordinate x) * scalarCoordinate u * scalarCoordinate v := by
  have hf := (Cosine.hasDerivAt_force ε (scalarCoordinate x)).comp_hasFDerivAt x
    scalarCoordinate.hasFDerivAt
  have hd := hf.smul_const scalarCoordinate
  simp only [Function.comp_apply] at hd
  rw [show fderiv ℝ (potential ε) =
      (fun y : E 1 => Cosine.force ε (scalarCoordinate y) • scalarCoordinate) from
        funext (potential_fderiv ε)]
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

lemma coordinate_norm_sq (u : E 1) : ‖u‖ ^ 2 = scalarCoordinate u ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]

/-- Exact source admissibility with α=1−ε and β=1+ε, proved from (9.1). -/
theorem admissible {ε : ℝ} (hε : 0 < ε) (hεupper : ε ≤ 1 / 10) :
    AdmissiblePotential (potential ε) (1 - ε) (1 + ε) := by
  refine ⟨by norm_num, by linarith, by linarith, ?_, ?_, ?_⟩
  · exact ((Cosine.contDiff_potential ε).of_le (show (2 : WithTop ℕ∞) ≤ ⊤ from le_top)).comp
      scalarCoordinate.contDiff
  · intro x u
    rw [potential_second_variation, coordinate_norm_sq]
    simpa only [pow_two, mul_assoc] using
      mul_le_mul_of_nonneg_right (Cosine.curvature_bounds hε.le (scalarCoordinate x)).1
        (sq_nonneg (scalarCoordinate u))
  · intro x u
    rw [potential_second_variation, coordinate_norm_sq]
    simpa only [pow_two, mul_assoc] using
      mul_le_mul_of_nonneg_right (Cosine.curvature_bounds hε.le (scalarCoordinate x)).2
        (sq_nonneg (scalarCoordinate u))

/-- The precise Theorem 2.2 conclusion specialized to the nonquadratic cosine
model potential. The constant is chosen before all sample sizes N≥2. -/
def ExpectedConvergence (ε : ℝ) : Prop :=
  ∀ (μ0 : E 1) (S0 : Mat 1), S0.PosDef →
  ∃ (p : MomentPath 1) (C : ℝ), 0 < C ∧ IsMomentPathFrom (potential ε) μ0 S0 p ∧
  ∀ N : ℕ, 2 ≤ N →
    (∀ᵐ ω ∂sampleLaw 1 N, (empiricalCovariance (gaussianCloud μ0 S0 N ω)).PosDef) ∧
    ∃ X : Sample 1 N → ParticlePath 1 N,
      (∀ᵐ ω ∂sampleLaw 1 N, IsParticlePathFrom (potential ε) (gaussianCloud μ0 S0 N ω) (X ω)) ∧
      Measurable (fun ω => pathSup (X ω) p) ∧
      (∫⁻ ω, pathSup (X ω) p ∂sampleLaw 1 N) ≤ ENNReal.ofReal (C * rate 1 N)

/-- This is the original sentence “so Theorem 2.2 applies”, now instantiated
with the actual model Hessian bounds and all original sample-space quantifiers. -/
theorem theorem22_applies (sourceTheorem22 : Specification.Theorem22)
    {ε : ℝ} (hε : 0 < ε) (hεupper : ε ≤ 1 / 10) : ExpectedConvergence ε := by
  intro μ0 S0 hS0
  exact sourceTheorem22 1 (potential ε) (1 - ε) (1 + ε) (admissible hε hεupper) μ0 S0 hS0

end Paper38.CosineSource
