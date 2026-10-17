import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.Topology.Semicontinuous
import Mathlib.Analysis.InnerProductSpace.PiL2
import Paper28.EuclideanBorel

/-! Generic published weak-measure inputs, with actual native finite Borel
measures and actual Euclidean vector densities. Reshetnyak's strict polar
continuity and the bounded upper-semicontinuous Portmanteau inequality contain
no current, polyhedron, Jacobian or mass estimate. The paper's incident
Jacobian and its exact tangent value are constructed separately.

Reshetnyak: Siberian Math. J. 9 (1968), 1039--1045,
DOI 10.1007/BF02196453; exact bounded-continuous polar formulation also in
Rindler--Shaw, Quart. J. Math. 66 (2015), Theorem 2.5, p.958,
DOI 10.1093/qmath/hav022. Portmanteau is the standard bounded upper-integral
form of weak convergence of finite Borel measures on metric spaces.
-/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
universe u

def StrictPolarMeasureContinuityInput : Prop :=
  ∀ (d : ℕ) (q : Type u) [Fintype q],
    ∀ (μi : ℕ → FiniteMeasure (EuclideanSpace ℝ (Fin d)))
      (μ : FiniteMeasure (EuclideanSpace ℝ (Fin d)))
      (θi : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ q)
      (θ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ q),
      (∀ i, Measurable (θi i)) → Measurable θ →
      (∀ i, ∀ᵐ x ∂(μi i : Measure _), ‖θi i x‖ = 1) →
      (∀ᵐ x ∂(μ : Measure _), ‖θ x‖ = 1) →
      (∀ φ : EuclideanSpace ℝ (Fin d) →ᵇ ℝ,
        Tendsto (fun i => ∫ x, φ x • θi i x ∂(μi i : Measure _)) atTop
          (𝓝 (∫ x, φ x • θ x ∂(μ : Measure _)))) →
      Tendsto (fun i => (μi i).mass) atTop (𝓝 μ.mass) →
      Tendsto (fun i => (μi i).map (fun x => (x,θi i x))) atTop
        (𝓝 (μ.map (fun x => (x,θ x))))

def UpperPortmanteauInput : Prop :=
  ∀ (X : Type u) [MetricSpace X] [MeasurableSpace X] [BorelSpace X],
    ∀ (μi : ℕ → FiniteMeasure X) (μ : FiniteMeasure X), Tendsto μi atTop (𝓝 μ) →
      ∀ (J : X → ℝ) (B : ℝ), UpperSemicontinuous J → (∀ x, 0 ≤ J x ∧ J x ≤ B) →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop,
          (∫ x, J x ∂(μi i : Measure X)) ≤ (∫ x, J x ∂(μ : Measure X))+ε

end Paper28
