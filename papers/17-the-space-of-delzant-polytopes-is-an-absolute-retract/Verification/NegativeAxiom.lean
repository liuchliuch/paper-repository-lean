import Verification.Model

/-!
# Negative control: unauthorized axiom

Uses an extra axiom `P17Contract.bad : False`, so the official Comparator must
reject this solution (`Illegal axiom detected`).
-/

noncomputable section

open scoped Topology BigOperators Pointwise

namespace P17Contract

axiom bad : False

/-- Lemma 2.3 proved from an illegal axiom. -/
theorem lemma_2_3 {n m : ℕ} (P : DelzantSpace n) (Ps : Fin m → DelzantSpace n)
    {η : ℝ} (hη : 0 < η) :
    ∃ Q : DelzantSpace n,
      delzantDist Q P < η ∧
      DelzantPolytope.le P Q ∧
      ∀ i, DelzantPolytope.le (Ps i) Q :=
  (bad).elim

end P17Contract
