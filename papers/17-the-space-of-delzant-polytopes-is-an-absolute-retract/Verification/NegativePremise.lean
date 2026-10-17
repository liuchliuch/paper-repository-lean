import Verification.Model

/-!
# Negative control: extra premise (type mismatch with the challenge)

The statement of `lemma_2_3` gains an extra `False` hypothesis relative to
`Verification.Challenge`, so the official Comparator must reject this
solution (`Challenge and solution theorem statement do not match`).
-/

noncomputable section

open scoped Topology BigOperators Pointwise

namespace P17Contract

/-- Extra-premise variant of Lemma 2.3: the conclusion is only demanded under
an impossible hypothesis, which changes the statement type. -/
theorem lemma_2_3 {n m : ℕ} (P : DelzantSpace n) (Ps : Fin m → DelzantSpace n)
    {η : ℝ} (hη : 0 < η) :
    False →
    ∃ Q : DelzantSpace n,
      delzantDist Q P < η ∧
      DelzantPolytope.le P Q ∧
      ∀ i, DelzantPolytope.le (Ps i) Q := by
  intro h
  exact False.elim h

end P17Contract
