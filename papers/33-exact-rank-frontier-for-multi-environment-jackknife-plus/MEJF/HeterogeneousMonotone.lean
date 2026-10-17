import MEJF.HeterogeneousFrontier

/-! The source's support-feasibility monotonicity used in section 6.1. -/
namespace MEJF.HeterogeneousFrontier
open Finset
noncomputable section
variable {N : ℕ}

/-- Every subset of a supportable label set is itself supportable, keeping
exact degrees on the subset and zero degrees on its complement. -/
theorem supported_subset (w : Fin N → ℕ) {S T : Finset (Fin N)}
    (hST : S ⊆ T) (hT : Supported w T) : Supported w S := by
  apply (supported_iff_admissible w S).mpr
  have ht := (supported_iff_admissible w T).mp hT
  intro A hA
  exact ht A (hA.trans hST)

/-- Feasible support cardinalities are downward closed, not an assumed
algorithmic monotonicity oracle. -/
theorem supported_card_downward (w : Fin N → ℕ) {r s : ℕ} (hrs : r ≤ s)
    (hs : ∃ S : Finset (Fin N), S.card=s ∧ Supported w S) :
    ∃ S : Finset (Fin N), S.card=r ∧ Supported w S := by
  obtain ⟨T,hT,hg⟩ := hs
  obtain ⟨S,hST,hS⟩ := Finset.exists_subset_card_eq (hT.symm ▸ hrs)
  exact ⟨S,hS,supported_subset w hST hg⟩

end
end MEJF.HeterogeneousFrontier
