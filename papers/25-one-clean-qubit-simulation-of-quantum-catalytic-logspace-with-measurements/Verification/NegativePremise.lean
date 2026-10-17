import Paper25.Basic
import Paper25.Norms

/-!
# Negative control: extra premise (type mismatch with the challenge)
-/

noncomputable section

open scoped ComplexOrder ComplexConjugate

namespace Paper25.Challenge

theorem inv_sub_regularized (σ lam : ℝ) (hσ : 0 < σ) (hlam : 0 < lam) :
    False →
      (1 / σ - σ / (σ ^ 2 + lam ^ 2) = lam ^ 2 / (σ * (σ ^ 2 + lam ^ 2))) :=
  fun _ => Paper25.inv_sub_regularized σ lam hσ hlam

end Paper25.Challenge
