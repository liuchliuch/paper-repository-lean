import Paper36.Bank

open scoped BigOperators Topology
open Set Filter Finset
open Paper36.Bank

namespace P36Contract.Bank

/-- Negative control: an additional impossible premise changes the fixed statement. -/
theorem calibration_count_bound : False → (∀ (T d : ℕ → ℝ) (Δ τ : ℝ)
    (hΔ : 0 < Δ) (hT : Monotone T) (hbase : 0 ≤ T 0 + τ)
    (hgap : ∀ n, calibrates T d n → Δ ≤ d (n + 1))
    (hcap : ∀ n, calibrates T d n → d (n + 1) ≤ τ) (K : ℕ),
    (count T d K : ℝ) ≤ min (K : ℝ) ((T K + τ) / Δ)) := by
  intro h
  exact False.elim h

end P36Contract.Bank
