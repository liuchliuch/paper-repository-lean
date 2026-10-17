import Mathlib

/-! Independent mathematical objects used by the original paper contract.
In particular, the transposition return count is not defined by the spectral
formula that is supposed to compute it. -/
namespace P20Objects

abbrev Transposition (r : ℕ) := {σ : Equiv.Perm (Fin r) // σ.IsSwap}

/-- The actual number of ordered length-`2h` transposition words in `S_r`
whose product is the identity, the source's `T_h(r)`. -/
noncomputable def transpositionReturns (r h : ℕ) : ℕ :=
  Nat.card {moves : Fin (2*h) → Transposition r //
    (List.ofFn (fun i => (moves i).val)).prod = 1}

/-- There is exactly one empty return word. -/
theorem transpositionReturns_zero (r : ℕ) : transpositionReturns r 0 = 1 := by
  unfold transpositionReturns
  haveI : Nonempty {moves : Fin (2*0) → Transposition r //
      (List.ofFn (fun i => (moves i).val)).prod = 1} :=
    ⟨⟨fun i => Fin.elim0 i, by simp⟩⟩
  haveI : Subsingleton {moves : Fin (2*0) → Transposition r //
      (List.ofFn (fun i => (moves i).val)).prod = 1} := by
    constructor
    intro a b
    apply Subtype.eq
    funext i
    exact Fin.elim0 i
  exact Nat.card_unique

end P20Objects
