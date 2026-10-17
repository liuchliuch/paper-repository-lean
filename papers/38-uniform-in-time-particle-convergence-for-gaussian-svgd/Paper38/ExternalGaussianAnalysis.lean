import Paper38.Model

/-!
# Explicit external Gaussian analysis input

This module records one classical Gaussian integration-by-parts input, permitted
by the user's external-input scope. It is an ordinary external theorem argument, NOT a proved theorem in this project.
It is the standard Stein identity applied to the actual C² potential with bounded
Hessian, under the actual standard Gaussian measure, before differentiation of
any energy or construction of a dynamical system.

Source: Charles M. Stein, *Estimation of the Mean of a Multivariate Normal
Distribution*, Annals of Statistics 9(6), 1135–1151 (1981), Lemma 1, p. 1136,
https://doi.org/10.1214/aos/1176345632 . The P38 application is paper.txt S4.p4
(Gaussian differentiation / Price identity). C² with bounded Hessian gives the
linear-gradient growth and integrability required by the classical identity.

The hypotheses below are the actual source potential assumptions and actual
symmetric matrix directions. The conclusion is solely an integral identity;
no energy gradient, mobility, stability, ODE, or convergence result is assumed.
-/

noncomputable section
open MeasureTheory
open scoped Matrix InnerProductSpace

namespace Paper38.ExternalGaussianAnalysis
open Paper38.Model

/-- External classical Gaussian Stein integration-by-parts application, in the
exact model and normalization used by P38. See the module documentation. -/
def GaussianSteinTheorem (d : ℕ) : Prop :=
  ∀ {V : E d → ℝ} {α β : ℝ}
    (_hV : AdmissiblePotential V α β) (μ u : E d) (A H : Mat d)
    (_hA : A.PosDef) (_hH : Hᵀ = H),
    (∫ z : E d, (fderiv ℝ V (μ + matVec A z)) (u + matVec H z)
      ∂standardGaussian d) =
      ⟪meanGradient V μ (A * A), u⟫_ℝ +
        Matrix.trace (meanHessian V μ (A * A) * A * H)

/-- Use of the explicitly supplied classical analysis theorem. -/
theorem gaussian_stein_first_variation {d : ℕ} (stein : GaussianSteinTheorem d)
    {V : E d → ℝ} {α β : ℝ} (hV : AdmissiblePotential V α β)
    (μ u : E d) (A H : Mat d) (hA : A.PosDef) (hH : Hᵀ = H) :
    (∫ z : E d, (fderiv ℝ V (μ + matVec A z)) (u + matVec H z) ∂standardGaussian d) =
      ⟪meanGradient V μ (A * A), u⟫_ℝ + Matrix.trace (meanHessian V μ (A * A) * A * H) :=
  stein hV μ u A H hA hH

end Paper38.ExternalGaussianAnalysis
