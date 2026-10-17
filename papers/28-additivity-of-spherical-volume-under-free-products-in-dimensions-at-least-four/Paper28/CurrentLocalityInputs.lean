import Paper28.EuclideanCurrentTangentInput

/-! Two generic standard AK/rectifiable-current facts: zero mass detects
the zero current, and affine support forces the approximate tangent into
the affine direction space. Neither field refers to a spherical map,
projective rank, polyhedral approximation or paper-owned estimate. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open MeasureTheory Set
universe u v

structure CurrentMassFaithfulnessInput {X : Type u} {metricX : MetricSpace X}
    (I : CompactIntegralCurrentAlgebraInput.{u,v} X metricX) : Prop where
  eq_zero_of_mass_zero : ∀ {k} (C : I.Current k), I.mass C = 0 → C = 0

structure EuclideanAffineSupportTangentInput {d : ℕ}
    (I : CompactIntegralCurrentAlgebraInput.{0,v} (EuclideanAmbient d) inferInstance)
    (R : EuclideanCurrentTangentInput d I) : Prop where
  affine_support_tangent : ∀ {k} (C : I.Current k) (x₀ : EuclideanAmbient d)
    (S : Submodule ℝ (EuclideanAmbient d)),
    I.support C ⊆ {x | x-x₀ ∈ S} →
      ∀ᵐ x ∂(R.massMeasure C : Measure (EuclideanAmbient d)), R.plane C x ≤ S

end Paper28
