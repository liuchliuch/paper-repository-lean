import K44K35Free

/-! Independent statements for the official Comparator. All mathematical
objects are concrete; the production root never imports this file. -/
noncomputable section
open scoped BigOperators
open K44K35Free K44K35Free.Geometry K44K35Free.Construction
attribute [local instance] Classical.propDecidable Classical.decEq

axiom illegalPaperLowerBound : (∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      Fintype.card V = n ∧ IsK35Free G ∧ G.IsBipartite ∧
        c * (n : ℝ)^3 ≤ numK44 G)

theorem Verification.theorem_1 :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      Fintype.card V = n ∧ IsK35Free G ∧ G.IsBipartite ∧
        c * (n : ℝ)^3 ≤ numK44 G := by
  exact illegalPaperLowerBound
