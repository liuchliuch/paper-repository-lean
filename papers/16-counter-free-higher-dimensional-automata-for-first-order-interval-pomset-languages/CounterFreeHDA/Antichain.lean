import CounterFreeHDA.GluingIso
import Mathlib.Data.Finset.Sort

/-! Event order on every precedence antichain is a genuine finite total order.
This supplies the ordered active interfaces used in ST decompositions. -/

namespace CounterFreeHDA
universe u
variable {Lab : Type u} {P : PomsetData Lab}

namespace PomsetData

def Antichain (P : PomsetData Lab) (A : Finset (Fin P.n)) : Prop :=
  ∀ e ∈ A, ∀ f ∈ A, ¬ P.prec e f

/-- Actual width bound, quantified over all precedence antichains. -/
def WidthLE (P : PomsetData Lab) (k : ℕ) : Prop :=
  ∀ A : Finset (Fin P.n), P.Antichain A → A.card ≤ k

end PomsetData

namespace IsIntervalPom

theorem eord_trans_on (hP : IsIntervalPom P) {A : Finset (Fin P.n)}
    (hA : P.Antichain A) {e f g : Fin P.n} (he : e ∈ A) (hf : f ∈ A) (hg : g ∈ A)
    (hef : P.eord e f) (hfg : P.eord f g) : P.eord e g := by
  have heg : e ≠ g := by
    intro h
    subst g
    exact hP.eord_acyclic e ((Relation.TransGen.single hef).tail hfg)
  rcases (hP.trichotomy e g heg).1 with h | h | h | h
  · exact False.elim (hA e he g hg h)
  · exact False.elim (hA g hg e he h)
  · exact h
  · exact False.elim (hP.eord_acyclic e (((Relation.TransGen.single hef).tail hfg).tail h))

end IsIntervalPom

namespace Antichain
variable (P : PomsetData Lab) (hP : IsIntervalPom P) (A : Finset (Fin P.n))
    (hA : P.Antichain A)

/-- Ordered enumeration retains event identity as well as labels. -/
structure Enumeration where
  event : Fin A.card → Fin P.n
  injective : Function.Injective event
  mem : ∀ i, event i ∈ A
  surjective : ∀ e ∈ A, ∃ i, event i = e
  ordered : ∀ i j, P.eord (event i) (event j) ↔ i < j

noncomputable def enumeration : Enumeration P A := by
  classical
  let r : {e // e ∈ A} → {e // e ∈ A} → Prop := fun e f => P.eord e.val f.val
  letI : IsStrictTotalOrder {e // e ∈ A} r := {
    irrefl := fun e => hP.eord_irrefl e.val
    trans := fun e f g hef hfg => hP.eord_trans_on hA e.property f.property g.property hef hfg
    trichotomous := by
      intro e f
      by_cases he : e = f
      · exact Or.inr (Or.inl he)
      · have hn : e.val ≠ f.val := fun h => he (Subtype.ext h)
        rcases (hP.trichotomy e.val f.val hn).1 with h | h | h | h
        · exact False.elim (hA e.val e.property f.val f.property h)
        · exact False.elim (hA f.val f.property e.val e.property h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h) }
  let ord : LinearOrder {e // e ∈ A} := linearOrderOfSTO r
  letI : LE {e // e ∈ A} := ord.toLE
  letI : LT {e // e ∈ A} := ord.toLT
  letI : LinearOrder {e // e ∈ A} := ord
  let eqv : Fin A.card ≃o {e // e ∈ A} := Fintype.orderIsoFinOfCardEq _ (Fintype.card_coe A)
  exact {
    event i := (eqv i).val
    injective := fun i j h => eqv.injective (Subtype.ext h)
    mem i := (eqv i).property
    surjective e he := ⟨eqv.symm ⟨e,he⟩,by simp⟩
    ordered i j := by
      change @LT.lt _ ord.toLT (eqv i) (eqv j) ↔ i < j
      exact @OrderIso.lt_iff_lt (Fin A.card) {e // e ∈ A} inferInstance ord.toPartialOrder.toPreorder eqv i j }

end Antichain
end CounterFreeHDA
