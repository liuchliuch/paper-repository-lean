import Mathlib.Geometry.Manifold.Complex

/-!
# Constancy of a globally glued coefficient on a compact complex curve

This is the compactness step in §3, p.10. The compatibility of the coefficients
in different charts is not built into the input: applying this result to the
paper still requires proving that those chart coefficients define a global
holomorphic function.
-/
noncomputable section
open scoped Manifold

namespace Paper27.CompactCoefficient

/-- Once the chart coefficients in (5) are a holomorphic function on the
connected compact curve, their common value is a global constant. -/
theorem exists_constant {D : Type*} [TopologicalSpace D] [ChartedSpace ℂ D]
    [IsManifold 𝓘(ℂ, ℂ) 1 D] [CompactSpace D] [ConnectedSpace D]
    (a : D → ℂ) (ha : MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) a)
    (ha₀ : ∀ p, a p ≠ 0) (ha₁ : ∀ p, a p ≠ 1) :
    ∃ c : ℂ, c ≠ 0 ∧ c ≠ 1 ∧ ∀ p, a p = c := by
  obtain ⟨c, hc⟩ := ha.exists_eq_const_of_compactSpace
  obtain ⟨p⟩ := (inferInstance : Nonempty D)
  have hp : a p = c := congrFun hc p
  exact ⟨c, hp ▸ ha₀ p, hp ▸ ha₁ p, fun q => congrFun hc q⟩

end Paper27.CompactCoefficient
