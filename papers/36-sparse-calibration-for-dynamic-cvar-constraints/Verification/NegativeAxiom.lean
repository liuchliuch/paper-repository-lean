import Paper36.Bank

open scoped BigOperators Topology
open Set Filter Finset
open Paper36.Bank

namespace P36IllegalControl

/-- Intentionally forbidden axiom; this module is never imported by production. -/
axiom unauthorized : ∀ (T d : ℕ → ℝ) (Δ τ : ℝ)
    (hΔ : 0 < Δ) (hT : Monotone T) (hbase : 0 ≤ T 0 + τ)
    (hgap : ∀ n, calibrates T d n → Δ ≤ d (n + 1))
    (hcap : ∀ n, calibrates T d n → d (n + 1) ≤ τ) (K : ℕ),
    (count T d K : ℝ) ≤ min (K : ℝ) ((T K + τ) / Δ)

end P36IllegalControl

namespace P36Contract.Bank

theorem calibration_count_bound : ∀ (T d : ℕ → ℝ) (Δ τ : ℝ)
    (hΔ : 0 < Δ) (hT : Monotone T) (hbase : 0 ≤ T 0 + τ)
    (hgap : ∀ n, calibrates T d n → Δ ≤ d (n + 1))
    (hcap : ∀ n, calibrates T d n → d (n + 1) ≤ τ) (K : ℕ),
    (count T d K : ℝ) ≤ min (K : ℝ) ((T K + τ) / Δ) := P36IllegalControl.unauthorized

end P36Contract.Bank
