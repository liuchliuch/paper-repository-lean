import Paper10

/-!
# Negative control: unauthorized axiom
-/

noncomputable section

open Matrix

namespace Paper10.Challenge

axiom unauthorized_lemma_2_3_first :
  ∀ {q : ℕ} {ι : Type*} [Fintype ι]
    (B : ι → Matrix (Fin q) (Fin q) ℝ)
    (_hB : ∀ a, (B a).IsSymm),
    ∑ a, ∑ b, |Matrix.trace (B a * B b * B a * B b)|
      ≤ Matrix.trace ((∑ a, B a * B a) * (∑ a, B a * B a))

theorem lemma_2_3_first {q : ℕ} {ι : Type*} [Fintype ι]
    (B : ι → Matrix (Fin q) (Fin q) ℝ)
    (hB : ∀ a, (B a).IsSymm) :
    ∑ a, ∑ b, |Matrix.trace (B a * B b * B a * B b)|
      ≤ Matrix.trace ((∑ a, B a * B a) * (∑ a, B a * B a)) :=
  unauthorized_lemma_2_3_first B hB

end Paper10.Challenge
