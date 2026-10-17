import Paper38.GlobalODE

/-! Explicit ordinary textbook continuous-dependence input. This module neither
postulates an axiom nor assumes existence of any Gaussian or particle flow.

Source: Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems*,
AMS GSM 140 (2012), Chapter 2, continuous dependence on initial conditions:
https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf . The statement below
is its fixed-time consequence for an already constructed global solution family
on an open domain. The family is required to solve the actual ODE at every
initial state in that domain, including the right derivative at time zero. -/

namespace Paper38.ExternalODEAnalysis
open Set

/-- Standard continuous dependence for any given global solution family of a
locally Lipschitz autonomous finite-dimensional real ODE. -/
def GlobalFlowContinuousDependence (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : Prop :=
  ∀ (Ω : Set E) (f : E → E), IsOpen Ω → LocallyLipschitzOn Ω f →
    ∀ Φ : E → ℝ → E,
      (∀ x ∈ Ω, Φ x 0 = x) →
      (∀ x ∈ Ω, ∀ t : ℝ, 0 ≤ t →
        Φ x t ∈ Ω ∧ HasDerivWithinAt (Φ x) (f (Φ x t)) (Ici 0) t) →
      ∀ t : ℝ, 0 ≤ t → ContinuousOn (fun x => Φ x t) Ω

end Paper38.ExternalODEAnalysis
