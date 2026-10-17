import Paper28.EuclideanPolyhedralCurrents
import Paper28.PluckerCoordinates
import Paper28.EuclideanBorel
import Mathlib.MeasureTheory.Measure.FiniteMeasure

/-! Disclosed generic Euclidean compatibility of AK rectifiable currents:
actual mass measures, oriented unit simple exterior densities and tangent
planes. Weak vector-density convergence below is the standard current weak
convergence consequence with uniformly bounded masses and a common compact
support. No polyhedral approximation, retraction Jacobian, sharp upper mass
or transfer estimate is supplied. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
universe v

structure EuclideanCurrentTangentInput (d : ℕ)
    (I : CompactIntegralCurrentAlgebraInput.{0,v} (EuclideanAmbient d) inferInstance) where
  massMeasure : {k : ℕ} → I.Current k → FiniteMeasure (EuclideanAmbient d)
  total_mass_eq : ∀ {k} (C : I.Current k), ((massMeasure C).mass : ℝ) = I.mass C
  support_ae : ∀ {k} (C : I.Current k), ∀ᵐ x ∂(massMeasure C : Measure _), x ∈ I.support C
  polar : {k : ℕ} → I.Current k → EuclideanAmbient d → EuclideanExterior d k
  polar_measurable : ∀ {k} (C : I.Current k), Measurable (polar C)
  polar_unit : ∀ {k} (C : I.Current k), ∀ᵐ x ∂(massMeasure C : Measure _), ‖polar C x‖ = 1
  plane : {k : ℕ} → I.Current k → EuclideanAmbient d → Submodule ℝ (EuclideanAmbient d)
  dimension_ae : ∀ {k} (C : I.Current k),
    ∀ᵐ x ∂(massMeasure C : Measure _), Module.finrank ℝ (plane C x) = k
  simple_tangent_ae : ∀ {k} (C : I.Current k), 0 < k →
    ∀ᵐ x ∂(massMeasure C : Measure _), ∃ e : Fin k → EuclideanAmbient d,
      Orthonormal ℝ e ∧ polar C x = pluckerCoordinates e ∧ Submodule.span ℝ (Set.range e) = plane C x
  weak_vector_density : ∀ {k} (C : I.Current k) (Ci : ℕ → I.Current k) (Si : ℕ → I.Current (k+1)),
    (∀ i, C-Ci i = I.boundary k (Si i)) → Tendsto (fun i => I.mass (Si i)) atTop (𝓝 0) →
    (∃ M : ℝ, ∀ i, I.mass (Ci i) ≤ M) →
    (∃ K : Set (EuclideanAmbient d), IsCompact K ∧ I.support C ⊆ K ∧ ∀ i, I.support (Ci i) ⊆ K) →
    ∀ φ : EuclideanAmbient d →ᵇ ℝ,
      Tendsto (fun i => ∫ x, φ x • polar (Ci i) x ∂(massMeasure (Ci i) : Measure _)) atTop
        (𝓝 (∫ x, φ x • polar C x ∂(massMeasure C : Measure _)))

end Paper28
