import BoundaryReduction

namespace Verification

theorem lemma_4_3 (_extraPremise : False) :
    ∀ {d : ℕ} (B : Set (EuclideanSpace ℝ (Fin d)))
      (g : EuclideanSpace ℝ (Fin d) → ℝ) (c : ℝ),
      IsOpen B → (0 : EuclideanSpace ℝ (Fin d)) ∈ B →
      BoundaryReduction.RaywiseConvex g → g 0 ≤ c →
      (∀ r ∈ frontier B, c ≤ g r) →
      ∀ μ, μ ∉ B → c ≤ g μ := by
  intro d B g c hB_open hB_zero hg hg0 hboundary μ hμ
  exact BoundaryReduction.first_exit_propagation
    hB_open hB_zero hg hg0 hboundary hμ

end Verification
