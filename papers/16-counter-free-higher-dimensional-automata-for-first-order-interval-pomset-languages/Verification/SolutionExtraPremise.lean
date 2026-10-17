import CounterFreeHDA

universe u v w z
open CounterFreeHDA CounterFreeHDA.Cubical CounterFreeHDA.LowerSetAction
noncomputable section
namespace Verification

theorem lemma_4_1_actual {Lab : Type u} {U : Interface Lab}
    (P : EndoPom U) {k n : ℕ} (hk : U.1 ≤ k) (hn : k ≤ n) (i j : Fin U.1) :
    False → ((P.pow n).Shared i j ↔ i = j ∧ P.Shared i i) := by
  intro hf
  exact False.elim hf

end Verification
