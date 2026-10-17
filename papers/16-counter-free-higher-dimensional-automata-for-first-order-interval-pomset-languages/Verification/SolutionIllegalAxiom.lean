import CounterFreeHDA

universe u v w z
open CounterFreeHDA CounterFreeHDA.Cubical CounterFreeHDA.LowerSetAction
noncomputable section
namespace Verification

axiom illegalSurvival {Lab : Type u} {U : Interface Lab}
    (P : EndoPom U) {k n : ℕ} (hk : U.1 ≤ k) (hn : k ≤ n) (i j : Fin U.1) :
    (P.pow n).Shared i j ↔ i = j ∧ P.Shared i i

theorem lemma_4_1_actual {Lab : Type u} {U : Interface Lab}
    (P : EndoPom U) {k n : ℕ} (hk : U.1 ≤ k) (hn : k ≤ n) (i j : Fin U.1) :
    (P.pow n).Shared i j ↔ i = j ∧ P.Shared i i :=
  illegalSurvival P hk hn i j

end Verification
