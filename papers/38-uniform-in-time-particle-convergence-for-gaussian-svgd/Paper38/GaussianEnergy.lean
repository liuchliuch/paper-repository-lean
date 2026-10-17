import Paper38.GaussianCoupling
import Paper38.PotentialBounds
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Gaussian energy: genuine second-variation integrands

This module proves integrability and the exact Gaussian lower bound for the
potential term in (4.7), from the original `AdmissiblePotential` hypotheses.
It does not identify this integral with a derivative of the energy; that
parameter-differentiation step remains a separate proof obligation.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Matrix

namespace Paper38.GaussianEnergy

open Paper38.Model Paper38.GaussianCoupling

variable {d : ℕ}

local instance standardGaussian_probability (d : ℕ) : IsProbabilityMeasure (standardGaussian d) := by
  unfold standardGaussian
  exact Measure.isProbabilityMeasure_map (continuous_vec (d := d)).measurable.aemeasurable

lemma affine_norm_sq_integrable (u : E d) (H : Mat d) :
    Integrable (fun z : E d => ‖u + matVec H z‖ ^ 2) (standardGaussian d) := by
  unfold standardGaussian
  apply (integrable_map_measure
    ((continuous_const.add (continuous_matVec H)).norm.pow 2).aestronglyMeasurable
    continuous_vec.measurable.aemeasurable).mpr
  simpa [affineGaussian, matVec, vec, Matrix.mulVec, dotProduct] using
    synchronous_cost_integrable u (0 : E d) H (0 : Mat d)

/-- The exact identity used in the first term of equation (4.7). -/
lemma affine_norm_sq_integral (u : E d) (H : Mat d) :
    (∫ z : E d, ‖u + matVec H z‖ ^ 2 ∂standardGaussian d) = ‖u‖ ^ 2 + frobSq H := by
  unfold standardGaussian
  rw [integral_map continuous_vec.measurable.aemeasurable
    ((continuous_const.add (continuous_matVec H)).norm.pow 2).aestronglyMeasurable]
  simpa [affineGaussian, matVec, vec, Matrix.mulVec, dotProduct] using
    synchronous_cost u (0 : E d) H (0 : Mat d)

/-- Actual Hessian-of-V quadratic integrand, without a free Hessian oracle. -/
def quadraticVariation (V : E d → ℝ) (μ u : E d) (A H : Mat d) (z : E d) : ℝ :=
  (fderiv ℝ (fderiv ℝ V) (μ + matVec A z) (u + matVec H z)) (u + matVec H z)

lemma quadraticVariation_continuous {V : E d → ℝ} {α β : ℝ}
    (hV : AdmissiblePotential V α β) (μ u : E d) (A H : Mat d) :
    Continuous (quadraticVariation V μ u A H) := by
  have h₁ : ContDiff ℝ 1 (fderiv ℝ V) := hV.regularity.fderiv_right (by norm_num)
  have h₂ := h₁.continuous_fderiv (by norm_num)
  have hp : Continuous (fun z : E d => μ + matVec A z) :=
    continuous_const.add (continuous_matVec A)
  have hd : Continuous (fun z : E d => u + matVec H z) :=
    continuous_const.add (continuous_matVec H)
  exact (((h₂.comp hp).clm_apply hd).clm_apply hd)

lemma quadraticVariation_nonneg {V : E d → ℝ} {α β : ℝ}
    (hV : AdmissiblePotential V α β) (μ u : E d) (A H : Mat d) (z : E d) :
    0 ≤ quadraticVariation V μ u A H z := by
  exact (mul_nonneg hV.alpha_pos.le (sq_nonneg _)).trans
    (hV.hessian_lower (μ + matVec A z) (u + matVec H z))

lemma quadraticVariation_integrable {V : E d → ℝ} {α β : ℝ}
    (hV : AdmissiblePotential V α β) (μ u : E d) (A H : Mat d) :
    Integrable (quadraticVariation V μ u A H) (standardGaussian d) := by
  apply ((affine_norm_sq_integrable u H).const_mul β).mono'
    (quadraticVariation_continuous hV μ u A H).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (quadraticVariation_nonneg hV μ u A H z)]
  exact hV.hessian_upper (μ + matVec A z) (u + matVec H z)

/-- Both bounds on the genuine Gaussian potential second-variation integral.
This proves the exact `α(|u|²+‖H‖F²)` contribution in (4.7). -/
lemma quadraticVariation_integral_bounds {V : E d → ℝ} {α β : ℝ}
    (hV : AdmissiblePotential V α β) (μ u : E d) (A H : Mat d) :
    α * (‖u‖ ^ 2 + frobSq H) ≤ ∫ z, quadraticVariation V μ u A H z ∂standardGaussian d ∧
      (∫ z, quadraticVariation V μ u A H z ∂standardGaussian d) ≤
        β * (‖u‖ ^ 2 + frobSq H) := by
  have hint := quadraticVariation_integrable hV μ u A H
  have hnorm := affine_norm_sq_integrable u H
  constructor
  · calc
      α * (‖u‖ ^ 2 + frobSq H) = ∫ z, α * ‖u + matVec H z‖ ^ 2 ∂standardGaussian d := by
        rw [integral_const_mul, affine_norm_sq_integral]
      _ ≤ ∫ z, quadraticVariation V μ u A H z ∂standardGaussian d := by
        exact integral_mono (hnorm.const_mul α) hint
          (fun z => hV.hessian_lower (μ + matVec A z) (u + matVec H z))
  · calc
      (∫ z, quadraticVariation V μ u A H z ∂standardGaussian d) ≤
          ∫ z, β * ‖u + matVec H z‖ ^ 2 ∂standardGaussian d := by
        exact integral_mono hint (hnorm.const_mul β)
          (fun z => hV.hessian_upper (μ + matVec A z) (u + matVec H z))
      _ = β * (‖u‖ ^ 2 + frobSq H) := by rw [integral_const_mul, affine_norm_sq_integral]

/-- The original C²/Hessian hypotheses suffice for integrability of the
actual potential at every affine Gaussian parameter. -/
lemma potential_integrable {V : E d → ℝ} {α β : ℝ}
    (hV : AdmissiblePotential V α β) (μ : E d) (A : Mat d) :
    Integrable (fun z : E d => V (μ + matVec A z)) (standardGaussian d) := by
  let C := |V 0| + ‖fderiv ℝ V 0‖ + 2 * β
  have hbound : Integrable (fun z : E d => C * (1 + ‖μ + matVec A z‖ ^ 2))
      (standardGaussian d) :=
    ((integrable_const 1).add (affine_norm_sq_integrable μ A)).const_mul C
  apply hbound.mono'
    ((hV.regularity.continuous.comp (continuous_const.add (continuous_matVec A))).aestronglyMeasurable)
  filter_upwards [] with z
  simpa [Real.norm_eq_abs, C] using PotentialBounds.potential_quadratic_growth hV (μ + matVec A z)

/-- Actual first-variation integrand. -/
def firstVariation (V : E d → ℝ) (μ u : E d) (A H : Mat d) (z : E d) : ℝ :=
  (fderiv ℝ V (μ + matVec A z)) (u + matVec H z)

lemma firstVariation_bound {V : E d → ℝ} {α β : ℝ}
    (hV : AdmissiblePotential V α β) (x w : E d) :
    |(fderiv ℝ V x) w| ≤
      ‖fderiv ℝ V 0‖ * (1 + ‖w‖ ^ 2) + β * (‖x‖ ^ 2 + ‖w‖ ^ 2) := by
  have hβ : 0 ≤ β := hV.alpha_pos.le.trans hV.alpha_le_beta
  have hn : ‖w‖ ≤ 1 + ‖w‖ ^ 2 := by nlinarith [sq_nonneg (‖w‖ - 1)]
  have hlin := mul_le_mul_of_nonneg_left hn (norm_nonneg (fderiv ℝ V 0))
  have hquad := mul_nonneg hβ (sq_nonneg (‖x‖ - ‖w‖))
  have hval := (fderiv ℝ V x).le_opNorm w
  have hgrowth := mul_le_mul_of_nonneg_right
    (PotentialBounds.fderiv_linear_growth hV x) (norm_nonneg w)
  simp only [Real.norm_eq_abs] at hval
  nlinarith

lemma firstVariation_continuous {V : E d → ℝ} {α β : ℝ}
    (hV : AdmissiblePotential V α β) (μ u : E d) (A H : Mat d) :
    Continuous (firstVariation V μ u A H) := by
  exact (((hV.regularity.continuous_fderiv (by norm_num)).comp
    (continuous_const.add (continuous_matVec A))).clm_apply
      (continuous_const.add (continuous_matVec H)))

/-- Integrability of the actual first-variation expression in Lemma 4.2. -/
lemma firstVariation_integrable {V : E d → ℝ} {α β : ℝ}
    (hV : AdmissiblePotential V α β) (μ u : E d) (A H : Mat d) :
    Integrable (firstVariation V μ u A H) (standardGaussian d) := by
  have hx := affine_norm_sq_integrable μ A
  have hw := affine_norm_sq_integrable u H
  have hbound : Integrable (fun z : E d =>
      ‖fderiv ℝ V 0‖ * (1 + ‖u + matVec H z‖ ^ 2) +
        β * (‖μ + matVec A z‖ ^ 2 + ‖u + matVec H z‖ ^ 2)) (standardGaussian d) :=
    (((integrable_const 1).add hw).const_mul _).add ((hx.add hw).const_mul β)
  apply hbound.mono' (firstVariation_continuous hV μ u A H).aestronglyMeasurable
  filter_upwards [] with z
  exact firstVariation_bound hV (μ + matVec A z) (u + matVec H z)

end Paper38.GaussianEnergy
