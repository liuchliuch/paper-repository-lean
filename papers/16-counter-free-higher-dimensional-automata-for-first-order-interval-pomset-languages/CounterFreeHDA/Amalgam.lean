import CounterFreeHDA.Pomset

/-! Acyclic event orders can be amalgamated along a common ordered interface.
A path that enters the other factor and returns to the interface can only
return at a strictly later position; compressing that segment yields a path
in the first factor. -/

namespace CounterFreeHDA
universe u

private theorem interface_path_lt {E : Type} {r : ℕ} (R : E → E → Prop)
    (acyclic : ∀ e, ¬ Relation.TransGen R e e)
    (iota : Fin r → E) (ordered : ∀ i j, R (iota i) (iota j) ↔ i < j)
    {i j : Fin r} (h : Relation.TransGen R (iota i) (iota j)) : i < j := by
  by_contra hij
  rcases lt_or_eq_of_le (le_of_not_gt hij) with hji | hji
  · exact acyclic _ (h.tail ((ordered j i).mpr hji))
  · subst j
    exact acyclic _ h

variable {Lab : Type u} {P Q : PomsetData Lab} (len : P.tgtLen = Q.srcLen)

private def LeftInvariant (x : Fin P.n) : GluedE P Q → Prop
  | .left e => Relation.TransGen P.eord x e.val
  | .mid j => Relation.TransGen P.eord x (P.tgt j)
  | .right e => ∃ i : Fin P.tgtLen,
      Relation.ReflTransGen P.eord x (P.tgt i) ∧
      Relation.TransGen Q.eord (Q.src (Fin.cast len i)) e.val

private theorem left_invariant
    (pord : ∀ i j, P.eord (P.tgt i) (P.tgt j) ↔ i < j)
    (qord : ∀ i j, Q.eord (Q.src i) (Q.src j) ↔ i < j)
    (qacyclic : ∀ e, ¬ Relation.TransGen Q.eord e e)
    {a b : GluedE P Q} {x : Fin P.n}
    (ha : GluedE.leftProjection P Q a = some x)
    (h : Relation.TransGen (glueEord len) a b) : LeftInvariant len x b := by
  induction h with
  | @single b hab =>
    cases a with
    | right e => cases ha
    | left e =>
      simp only [GluedE.leftProjection, Option.some.injEq] at ha
      subst x
      cases b with
      | left f => exact .single hab
      | mid j => exact .single hab
      | right f => exact False.elim hab
    | mid i =>
      simp only [GluedE.leftProjection, Option.some.injEq] at ha
      subst x
      cases b with
      | left f => exact .single hab
      | mid j => exact .single hab
      | right f => exact ⟨i,.refl,.single hab⟩
  | @tail b c hp hbc ih =>
    cases b with
    | left e =>
      cases c with
      | left f => exact ih.tail hbc
      | mid j => exact ih.tail hbc
      | right f => exact False.elim hbc
    | mid i =>
      cases c with
      | left f => exact ih.tail hbc
      | mid j => exact ih.tail hbc
      | right f => exact ⟨i,ih.to_reflTransGen,.single hbc⟩
    | right e =>
      obtain ⟨i,hp',hq'⟩ := ih
      cases c with
      | left f => exact False.elim hbc
      | right f => exact ⟨i,hp',hq'.tail hbc⟩
      | mid j =>
        have hlt := interface_path_lt Q.eord qacyclic Q.src qord (hq'.tail hbc)
        have hij : i < j := by simpa using hlt
        exact Relation.TransGen.tail' hp' ((pord i j).mpr hij)

/-- Reverse only the roles of interfaces. Used for symmetry of the event-order
amalgam; its precedence field is irrelevant to the graph argument. -/
private def swapInterfaces (P : PomsetData Lab) : PomsetData Lab where
  n := P.n
  lab := P.lab
  prec e f := P.prec f e
  eord := P.eord
  srcLen := P.tgtLen
  tgtLen := P.srcLen
  src := P.tgt
  tgt := P.src
  src_inj := P.tgt_inj
  tgt_inj := P.src_inj

private def swapEvent : GluedE P Q → GluedE (swapInterfaces Q) (swapInterfaces P)
  | .left e => .right e
  | .right e => .left e
  | .mid i => .mid (Fin.cast len i)

private theorem swap_event_order
    (pord : ∀ i j, P.eord (P.tgt i) (P.tgt j) ↔ i < j)
    (qord : ∀ i j, Q.eord (Q.src i) (Q.src j) ↔ i < j)
    (e f : GluedE P Q) :
    glueEord len e f ↔ glueEord (P := swapInterfaces Q) (Q := swapInterfaces P)
      len.symm (swapEvent len e) (swapEvent len f) := by
  cases e <;> cases f <;>
    simp only [swapEvent, glueEord, swapInterfaces, Fin.cast_trans, Fin.cast_refl]
  all_goals first | rfl | simpa only [pord, qord, Fin.cast_lt_cast]

/-- The inherited event order of actual interface gluing is acyclic. -/
theorem glueEord_acyclic (hP : IsIntervalPom P) (hQ : IsIntervalPom Q) :
    ∀ e : GluedE P Q, ¬ Relation.TransGen (glueEord len) e e := by
  intro e h
  cases e with
  | left e =>
    have hi := left_invariant len hP.tgt_eord hQ.src_eord hQ.eord_acyclic rfl h
    exact hP.eord_acyclic _ hi
  | mid i =>
    have hi := left_invariant len hP.tgt_eord hQ.src_eord hQ.eord_acyclic rfl h
    exact hP.eord_acyclic _ hi
  | right e =>
    have lift : ∀ {a b}, Relation.TransGen (glueEord len) a b →
        Relation.TransGen (glueEord (P := swapInterfaces Q) (Q := swapInterfaces P) len.symm)
          (swapEvent len a) (swapEvent len b) := by
      intro a b hab
      induction hab with
      | single hh => exact .single ((swap_event_order len hP.tgt_eord hQ.src_eord _ _).mp hh)
      | tail _ hh ih => exact ih.tail ((swap_event_order len hP.tgt_eord hQ.src_eord _ _).mp hh)
    have hi := left_invariant (P := swapInterfaces Q) (Q := swapInterfaces P)
      len.symm hQ.src_eord hP.tgt_eord hP.eord_acyclic rfl (lift h)
    exact hQ.eord_acyclic _ hi

end CounterFreeHDA
