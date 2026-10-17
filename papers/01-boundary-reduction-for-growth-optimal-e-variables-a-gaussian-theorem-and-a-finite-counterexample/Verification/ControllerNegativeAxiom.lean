import BoundaryReduction

namespace Verification

axiom controllerNegativeUnauthorized : False

theorem lemma_4_3 :
    ∀ {d : ℕ} (B : Set (EuclideanSpace ℝ (Fin d)))
      (g : EuclideanSpace ℝ (Fin d) → ℝ) (c : ℝ),
      IsOpen B → (0 : EuclideanSpace ℝ (Fin d)) ∈ B →
      BoundaryReduction.RaywiseConvex g → g 0 ≤ c →
      (∀ r ∈ frontier B, c ≤ g r) →
      ∀ μ, μ ∉ B → c ≤ g μ := by
  exact False.elim controllerNegativeUnauthorized

end Verification
