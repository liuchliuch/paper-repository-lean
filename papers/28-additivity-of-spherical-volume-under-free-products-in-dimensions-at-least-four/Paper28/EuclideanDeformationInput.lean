import Paper28.EuclideanPolyhedralCurrents
import Mathlib.Topology.MetricSpace.Thickening

/-! Exact disclosed localized Federer--Fleming inputs. These are the
initial polyhedral approximation with small residual/filling and the
polyhedral-boundary Euclidean deformation theorem. Exact approximating
cycles, the mesh choice, strict convergence, and the source's sharp mass
bound after spherical retraction are not fields of this input. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
universe v

structure EuclideanDeformationInput (d : ℕ)
    (I : CompactIntegralCurrentAlgebraInput.{0,v} (EuclideanAmbient d) inferInstance)
    (S : EuclideanSimplexIntegrationInput d I) where
  constant : ℝ
  constant_pos : 0 < constant
  localized_approximation : ∀ k (T : I.Current (k+1)), I.boundary k T = 0 →
    ∀ ε ρ : ℝ, 0 < ε → 0 < ρ →
      ∃ P R : I.Current (k+1), ∃ W : I.Current (k+2),
        P ∈ euclideanPolyhedralCurrents S (k+1) ∧
        T = P+R+I.boundary (k+1) W ∧
        I.mass P ≤ I.mass T+ε ∧ I.mass R+I.mass W ≤ ε ∧
        (I.support P ∪ I.support R ∪ I.support W) ⊆ Metric.thickening ρ (I.support T)
  boundary_deformation : ∀ k (R : I.Current (k+1)),
    I.boundary k R ∈ euclideanPolyhedralCurrents S k → ∀ a : ℝ, 0 < a →
      ∃ P U : I.Current (k+1), ∃ V : I.Current (k+2),
        P ∈ euclideanPolyhedralCurrents S (k+1) ∧ U ∈ euclideanPolyhedralCurrents S (k+1) ∧
        R = P+U+I.boundary (k+1) V ∧
        I.mass P ≤ constant*I.mass R ∧
        I.mass U ≤ constant*a*I.mass (I.boundary k R) ∧
        I.mass V ≤ constant*a*I.mass R ∧
        (I.support P ∪ I.support U ∪ I.support V) ⊆ Metric.thickening (constant*a) (I.support R)

end Paper28
