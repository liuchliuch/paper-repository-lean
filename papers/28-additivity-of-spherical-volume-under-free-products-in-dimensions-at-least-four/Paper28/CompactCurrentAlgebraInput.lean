import Paper28.CompactCurrentSupportInput
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Instances.Real.Lemmas

/-! Disclosed generic AK compact integral-current boundary and mass laws.
The lower semicontinuity field is its usual epsilon formulation for flat
convergence witnessed by fillings of vanishing mass. No polyhedral
approximation, sharp upper mass estimate or transfer is supplied. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter
open scoped Topology
universe u v

structure CompactIntegralCurrentAlgebraInput (X : Type u) (metric : MetricSpace X)
    extends CompactIntegralCurrentSupportInput.{u,v} X metric where
  boundary : ∀ k, Current (k+1) →+ Current k
  boundary_squared_zero : ∀ k (C : Current (k+2)), boundary k (boundary (k+1) C) = 0
  support_boundary_subset : ∀ k (C : Current (k+1)), support (boundary k C) ⊆ support C
  mass : {k : ℕ} → Current k → ℝ
  mass_nonneg : ∀ {k} (C : Current k), 0 ≤ mass C
  mass_zero : ∀ k, mass (0 : Current k) = 0
  mass_add_le : ∀ {k} (C D : Current k), mass (C+D) ≤ mass C+mass D
  mass_neg : ∀ {k} (C : Current k), mass (-C) = mass C
  mass_lower_semicontinuity : ∀ k (C : Current k)
    (Ci : ℕ → Current k) (Si : ℕ → Current (k+1)),
    (∀ i, C-Ci i = boundary k (Si i)) → Tendsto (fun i => mass (Si i)) atTop (𝓝 0) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, mass C ≤ mass (Ci i)+ε

def CurrentHomologous {X : Type u} {metric : MetricSpace X}
    (I : CompactIntegralCurrentAlgebraInput.{u,v} X metric) (k : ℕ) (C D : I.Current k) : Prop :=
  ∃ S : I.Current (k+1), C-D = I.boundary k S

theorem current_cycle_of_homologous {X : Type u} {metric : MetricSpace X}
    (I : CompactIntegralCurrentAlgebraInput.{u,v} X metric) (k : ℕ)
    (C D : I.Current (k+1)) (hC : I.boundary k C = 0) (h : CurrentHomologous I (k+1) C D) :
    I.boundary k D = 0 := by
  obtain ⟨S,hS⟩ := h
  have hb := congrArg (I.boundary k) hS
  rw [map_sub,hC,I.boundary_squared_zero,zero_sub] at hb
  exact neg_eq_zero.mp hb

end Paper28
