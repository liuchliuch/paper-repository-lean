import CounterFreeHDA.FirstOrder

namespace CounterFreeHDA.Cubical
universe u v
variable {Lab : Type u} [Fintype Lab] {k : ℕ} {L : Set (IntervalPom Lab)}

def AperiodicallyRecognisable (L : Set (IntervalPom Lab)) : Prop :=
  ∃ h : ℕ, 1 ≤ h ∧ Nonempty (FinitePomsetRecognizer.{u,u} (k := k) L h)

def CounterFreeRecognisable (L : Set (IntervalPom Lab)) : Prop :=
  ∃ X : HDA.{u,u} Lab k, Finite (Σ U, X.Cell U) ∧ X.LangPom = L ∧ X.toPrecubical.CounterFreePom

/-- **Corollary 1.2, new direction (i) => (ii).** The two implications
requiring [4, Theorem 33 and Proposition 35] are explicitly outside scope;
no axiom is introduced to represent either external theorem. -/
theorem corollary_1_2_new_direction
    (downward : ∀ {P Q}, P ⊑ₛ Q → Q ∈ L → P ∈ L)
    (withinWidth : ∀ P ∈ L, P.val.WidthLE k)
    (hL : AperiodicallyRecognisable (k := k) L) : CounterFreeRecognisable (k := k) L := by
  obtain ⟨h,hh,⟨G⟩⟩ := hL
  exact theorem_1_1_core G downward withinWidth

end CounterFreeHDA.Cubical
