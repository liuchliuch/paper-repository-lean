import Paper10

/-!
# Negative control: extra premise (type mismatch with the challenge)
-/

noncomputable section

open Matrix

namespace Paper10.Challenge

theorem lemma_2_3_first {q : ℕ} {ι : Type*} [Fintype ι]
    (B : ι → Matrix (Fin q) (Fin q) ℝ)
    (hB : ∀ a, (B a).IsSymm) :
    False →
      (∑ a, ∑ b, |Matrix.trace (B a * B b * B a * B b)|
        ≤ Matrix.trace ((∑ a, B a * B a) * (∑ a, B a * B a))) :=
  fun _ => Paper10.lemma_2_3_first B hB

end Paper10.Challenge
