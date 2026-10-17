import Paper19.Rank

namespace Paper19

/-- Kleene–Brouwer order: a proper extension precedes its prefix, while
incomparable nodes are compared at their first unequal natural entry. -/
def KB : Node → Node → Prop
  | [], _ => False
  | _ :: _, [] => True
  | a :: xs, b :: ys => a < b ∨ a = b ∧ KB xs ys

instance KB.decidable (x y : Node) : Decidable (KB x y) := by
  induction x generalizing y with
  | nil => exact isFalse (by simp [KB])
  | cons a xs ih => cases y with
    | nil => exact isTrue trivial
    | cons b ys => unfold KB; exact @instDecidableOr _ _ (inferInstance) (@instDecidableAnd _ _ (inferInstance) (ih ys))

theorem KB.irrefl (x : Node) : ¬KB x x := by
  induction x with
  | nil => simp [KB]
  | cons a xs ih => simp [KB, ih]

theorem KB.trans {x y z : Node} (hxy : KB x y) (hyz : KB y z) : KB x z := by
  induction x generalizing y z with
  | nil => exact False.elim hxy
  | cons a xs ih =>
    cases y with
    | nil => exact False.elim hyz
    | cons b ys =>
      cases z with
      | nil => trivial
      | cons c zs =>
        rcases hxy with hxy | ⟨rfl, hxy⟩
        · rcases hyz with hyz | ⟨rfl, hyz⟩
          · exact Or.inl (hxy.trans hyz)
          · exact Or.inl hxy
        · rcases hyz with hyz | ⟨rfl, hyz⟩
          · exact Or.inl hyz
          · exact Or.inr ⟨rfl, ih hxy hyz⟩

theorem KB.trichotomy (x y : Node) : KB x y ∨ x = y ∨ KB y x := by
  induction x generalizing y with
  | nil => cases y <;> simp [KB]
  | cons a xs ih =>
    cases y with
    | nil => exact Or.inl trivial
    | cons b ys =>
      rcases lt_trichotomy a b with h | rfl | h
      · exact Or.inl (Or.inl h)
      · rcases ih ys with h | h | h
        · exact Or.inl (Or.inr ⟨rfl,h⟩)
        · exact Or.inr (Or.inl (congrArg (List.cons a) h))
        · exact Or.inr (Or.inr (Or.inr ⟨rfl,h⟩))
      · exact Or.inr (Or.inr (Or.inl h))

/-- Adjoin a greatest element to any well-founded relation. -/
def TopRel {α : Type} (r : α → α → Prop) : Option α → Option α → Prop
  | some a, some b => r a b
  | some _, none => True
  | none, _ => False

theorem topRel_wf {α : Type} {r : α → α → Prop} (h : WellFounded r) : WellFounded (TopRel r) := by
  have hs (a : α) : Acc (TopRel r) (some a) := by
    induction h.apply a with
    | intro a ha ih =>
      refine Acc.intro _ ?_
      intro b hb
      cases b with
      | none => exact False.elim hb
      | some b => exact ih b hb
  refine ⟨fun a => ?_⟩
  cases a with
  | some a => exact hs a
  | none =>
    refine Acc.intro _ ?_
    intro b hb
    cases b with
    | none => exact False.elim hb
    | some b => exact hs b

/-- Well-foundedness of the KB order on any accessible subtree. This uses
a lexicographic sum of child subtrees in natural order, with the root last. -/
def TreeChild (S : Tree) (σ τ : Node) : Prop :=
  S.mem τ ∧ τ.length = σ.length + 1 ∧ τ.take σ.length = σ

theorem KB_subtree_wf {T : Tree} {σ : Node}
    (hs : Acc (fun τ σ => TreeChild T σ τ) σ) :
    WellFounded (fun x y : {t : Node // T.mem (σ ++ t)} => KB x.val y.val) := by
  induction hs with
  | intro σ hs ih =>
    let B (n : ℕ) := {t : Node // T.mem (σ ++ (n :: t))}
    have hb (n : ℕ) : WellFounded (fun x y : B n => KB x.val y.val) := by
      by_cases hn : T.mem (σ ++ [n])
      · have hc : TreeChild T σ (σ ++ [n]) := ⟨hn, by simp, by simp⟩
        let f : B n → {t : Node // T.mem ((σ ++ [n]) ++ t)} :=
          fun x => ⟨x.val, by simpa [List.append_assoc] using x.property⟩
        exact (ih _ hc).onFun (f := f)
      · refine ⟨fun x => False.elim (hn ?_)⟩
        exact T.mem_prefix x.property ⟨x.val, by simp⟩
    let R := PSigma.Lex (fun a b : ℕ => a < b) (fun n (x y : B n) => KB x.val y.val)
    have hw : WellFounded R := Nat.lt_wfRel.wf.psigma_lex hb
    let split : {t : Node // T.mem (σ ++ t)} → Option (PSigma B) := fun x =>
      match he : x.val with
      | [] => none
      | n :: t => some ⟨n, ⟨t, by rw [← he]; exact x.property⟩⟩
    apply ((topRel_wf hw).onFun (f := split)).mono
    rintro ⟨x,hx⟩ ⟨y,hy⟩ hxy
    cases x with
    | nil => exact False.elim hxy
    | cons a xs =>
      cases y with
      | nil => trivial
      | cons b ys =>
        change R ⟨a, ⟨xs,hx⟩⟩ ⟨b, ⟨ys,hy⟩⟩
        rcases hxy with h | ⟨rfl,h⟩
        · exact PSigma.Lex.left _ _ h
        · exact PSigma.Lex.right _ h

end Paper19
