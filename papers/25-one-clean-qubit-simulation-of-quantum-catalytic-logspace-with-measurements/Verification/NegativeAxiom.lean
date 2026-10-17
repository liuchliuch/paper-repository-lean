import Paper25.Basic
import Paper25.Norms

/-!
# Negative control: unauthorized axiom
-/

noncomputable section

open scoped ComplexOrder ComplexConjugate

namespace Paper25.Challenge

axiom unauthorized_inv_sub_regularized :
  ∀ σ lam : ℝ, 0 < σ → 0 < lam →
    1 / σ - σ / (σ ^ 2 + lam ^ 2) = lam ^ 2 / (σ * (σ ^ 2 + lam ^ 2))

theorem inv_sub_regularized (σ lam : ℝ) (hσ : 0 < σ) (hlam : 0 < lam) :
    1 / σ - σ / (σ ^ 2 + lam ^ 2) = lam ^ 2 / (σ * (σ ^ 2 + lam ^ 2)) :=
  unauthorized_inv_sub_regularized σ lam hσ hlam

end Paper25.Challenge
