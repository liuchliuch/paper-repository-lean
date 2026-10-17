import Paper29.QueryModel

/-! Exact minimax definition (2.5), retaining random seeds, adaptive policies,
rank restriction and the worst-case response. No minimax bound is assumed. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Paper29.QueryModel

/-- A single design-aware algorithm. Its seed law can depend on the known
matrix A, but neither seed law nor policy has access to the hidden b. -/
structure DesignAlgorithm (n d : ℕ) where
  Seed : Matrix (Fin n) (Fin d) ℝ → Type
  seedMeas : ∀ A, MeasurableSpace (Seed A)
  law : ∀ A, @Measure (Seed A) (seedMeas A)
  policy : ∀ A, Policy (Seed A) n d

def DesignAlgorithm.valid {n d : ℕ} (a : DesignAlgorithm n d) (ε : ℝ) : Prop :=
  ∀ A, @IsProbabilityMeasure (a.Seed A) (a.seedMeas A) (a.law A) ∧
    @Correct (a.Seed A) (a.seedMeas A) n d (a.law A) (a.policy A) A ε

def DesignAlgorithm.cost {n d : ℕ} (a : DesignAlgorithm n d) (r : ℕ) : ℝ≥0∞ :=
  ⨆ (A : Matrix (Fin n) (Fin d) ℝ) (_ : A.rank = r) (b : Fin n → ℝ),
    @lintegral (a.Seed A) (a.seedMeas A) (a.law A)
      (fun ω => queryCount (a.policy A) ω b)

def minimaxCost (n d r : ℕ) (ε : ℝ) : ℝ≥0∞ :=
  ⨅ (a : DesignAlgorithm n d) (_ : a.valid ε), a.cost r

/-- Corollary2.3, including absolute constants before the input parameters.
This is a specification only; the main upper and lower bounds remain unproved. -/
def MinimaxBoundsStatement : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (n d r : ℕ) (ε : ℝ),
    1 ≤ r → r ≤ min n d → 0 < ε → ε ≤ 1 / 800 →
    ENNReal.ofReal (lowerBudget n r c ε) ≤ minimaxCost n d r ε ∧
    minimaxCost n d r ε ≤ ENNReal.ofReal (upperBudget n r C ε)

end Paper29.QueryModel
