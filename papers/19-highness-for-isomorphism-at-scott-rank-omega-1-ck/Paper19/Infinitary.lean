import Paper19.ActualOrbit

namespace Paper19.Infinitary
open Paper19

inductive Term where
  | var : ℕ → Term
  | zero : Term
  | named : Term
  | succ : Term → Term
  | proj : Term → Term
  | level : Term → Term

def Term.eval {T : Tree} (tag : Bool) (e : ℕ → Carrier T) : Term → Carrier T
  | .var i => e i
  | .zero => Carrier.idx 0
  | .named => namedRoot T tag
  | .succ t => Carrier.succ (t.eval tag e)
  | .proj t => Carrier.projD (t.eval tag e)
  | .level t => Carrier.levelOf (t.eval tag e)

inductive Formula where
  | top : Formula
  | eq : Term → Term → Formula
  | index : Term → Formula
  | rel : Term → Term → Term → Formula
  | neg : Formula → Formula
  | and : Formula → Formula → Formula
  | all : (ℕ → Formula) → Formula
  | ex : ℕ → Formula → Formula

def Formula.Realize {T : Tree} (tag : Bool) (e : ℕ → Carrier T) : Formula → Prop
  | .top => True
  | .eq a b => a.eval tag e = b.eval tag e
  | .index a => Carrier.isIdx (a.eval tag e)
  | .rel a b c => Carrier.D (a.eval tag e) (b.eval tag e) (c.eval tag e)
  | .neg a => ¬ a.Realize tag e
  | .and a b => a.Realize tag e ∧ b.Realize tag e
  | .all a => ∀ i, (a i).Realize tag e
  | .ex v a => ∃ y, a.Realize tag (Function.update e v y)

def childFormula (v w : ℕ) : Formula :=
  .and (.neg (.index (.var v)))
    (.and (.neg (.index (.var w)))
      (.and (.eq (.proj (.var w)) (.var v)) (.neg (.eq (.var w) (.var v)))))

theorem child_iff {T : Tree} (x y : Carrier T) :
    (¬Carrier.isIdx x ∧ ¬Carrier.isIdx y ∧ Carrier.projD y = x ∧ y ≠ x) ↔
      IsChildG x.val y.val := by
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  cases x with
  | idx k => simp [Carrier.isIdx, isIndex, IsChildG]
  | vec n F =>
    cases y with
    | idx k => simp [Carrier.isIdx, isIndex, IsChildG]
    | vec m E =>
      cases m with
      | zero =>
        constructor
        · rintro ⟨_, _, he, hn⟩
          exact False.elim (hn he)
        · rintro ⟨k, A, B, hx', hy', _⟩
          cases hy'
      | succ m =>
        constructor
        · rintro ⟨_, _, he, hn⟩
          have he' := congrArg Subtype.val he
          obtain ⟨hnm, hFE⟩ := Dom.vec.inj he'
          subst n
          exact ⟨m, F, E, rfl, rfl, hFE, hx, hy⟩
        · rintro ⟨k, A, B, hx', hy', hp, hA, hB⟩
          obtain ⟨hkn, hAF⟩ := Dom.vec.inj hx'
          obtain ⟨hkm, hBE⟩ := Dom.vec.inj hy'
          have hnm : n = m := by omega
          subst n; subst k; subst A; subst B
          refine ⟨by simp [Carrier.isIdx, isIndex], by simp [Carrier.isIdx, isIndex], Subtype.ext ?_, ?_⟩
          · exact congrArg (Dom.vec m) hp
          · intro he
            have := (Dom.vec.inj (congrArg Subtype.val he)).1
            omega

theorem childFormula_realize {T : Tree} (tag : Bool) (e : ℕ → Carrier T) (v w : ℕ) :
    (childFormula v w).Realize tag e ↔ IsChildG (e v).val (e w).val :=
  child_iff (e v) (e w)

noncomputable def rankFormula {α : Type} [Encodable α] (r : α → α → Prop) [DecidableRel r]
    (x : α) (hx : Acc r x) : ℕ → Formula :=
  Acc.recOn hx (fun x _ ih v => .all (fun k =>
    match Encodable.decode (α := α) k with
    | none => .top
    | some y => if h : r y x then
        .ex (v + 1) (.and (childFormula v (v + 1)) (ih y h (v + 1))) else .top))

theorem rankFormula_eq {α : Type} [Encodable α] (r : α → α → Prop) [DecidableRel r]
    (x : α) (hx : Acc r x) (v : ℕ) :
    rankFormula r x hx v = .all (fun k =>
      match Encodable.decode (α := α) k with
      | none => .top
      | some y => if h : r y x then
          .ex (v + 1) (.and (childFormula v (v + 1)) (rankFormula r y (hx.inv h) (v + 1))) else .top) := by
  change rankFormula r x (Acc.intro x fun y h => hx.inv h) v = _
  rfl

/-- Recursion of the real rank test along any well-founded ordinal
presentation. This is the semantic induction behind equation (6). -/
theorem heightGE_presentation {α β : Type} {r : α → α → Prop} {s : β → β → Prop}
    {x : α} (hx : Acc r x) (b : β) :
    HeightGE s b hx.rank ↔ ∀ y (hy : r y x), ∃ c, s c b ∧ HeightGE s c (hx.inv hy).rank := by
  constructor
  · intro h y hy
    have hle : Order.succ (hx.inv hy).rank ≤ hx.rank := Order.succ_le_iff.mpr (hx.rank_lt_of_rel hy)
    exact heightGE_succ.mp (heightGE_mono hle h)
  · intro h hb
    rw [hx.rank_eq]
    apply Ordinal.iSup_le
    intro y
    obtain ⟨c, hc, hr⟩ := h y.val y.property
    exact Order.succ_le_iff.mpr ((hr (hb.inv hc)).trans_lt (hb.rank_lt_of_rel hc))

theorem rankFormula_realize {α : Type} [Encodable α] (r : α → α → Prop) [DecidableRel r]
    {x : α} (hx : Acc r x) {T : Tree} (tag : Bool) (v : ℕ) (e : ℕ → Carrier T) :
    (rankFormula r x hx v).Realize tag e ↔
      HeightGE (fun y x : Dom T => IsChildG x y) (e v).val hx.rank := by
  induction hx generalizing v e with
  | intro x hx ih =>
    rw [rankFormula_eq, heightGE_presentation]
    change (∀ k, (match Encodable.decode (α := α) k with
      | none => Formula.top
      | some y => if h : r y x then
        .ex (v + 1) (.and (childFormula v (v + 1))
          (rankFormula r y (hx y h) (v + 1))) else .top).Realize tag e) ↔ _
    constructor
    · intro h y hy
      have hh := h (Encodable.encode y)
      simp only [Encodable.encodek, dif_pos hy, Formula.Realize] at hh
      obtain ⟨c, hc, hr⟩ := hh
      have hchild := (childFormula_realize tag (Function.update e (v + 1) c) v (v + 1)).mp hc
      simp only [Function.update_self, Function.update_of_ne (show v ≠ v + 1 by omega)] at hchild
      refine ⟨c.val, hchild, ?_⟩
      simpa using (ih y hy (v + 1) (Function.update e (v + 1) c)).mp hr
    · intro h k
      cases hd : Encodable.decode (α := α) k with
      | none => trivial
      | some y =>
        by_cases hy : r y x
        · simp only [dif_pos hy, Formula.Realize]
          obtain ⟨c, hc, hr⟩ := h y hy
          have hgood : GoodDom c := by
            obtain ⟨n, F, E, hx', hy', hp, hF, hE⟩ := hc
            simpa [hy', GoodDom] using hE
          let c' : Carrier T := ⟨c, hgood⟩
          refine ⟨c', ?_, ?_⟩
          · apply (childFormula_realize tag _ _ _).mpr
            simpa [c'] using hc
          · apply (ih y hy (v + 1) (Function.update e (v + 1) c')).mpr
            simpa [c'] using hr
        · simp [hy, Formula.Realize]

end Paper19.Infinitary
