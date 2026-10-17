import Paper19.EffectiveCoding
import Paper19.LocalRank

namespace Paper19

theorem _root_.ComputablePred.or' {α : Type} [Primcodable α] {p q : α → Prop}
    (hp : ComputablePred p) (hq : ComputablePred q) : ComputablePred (fun x => p x ∨ q x) := by
  classical
  exact ((Primrec.or.to_comp.comp hp.decide hq.decide).of_eq (by simp)).computablePred

theorem SChild_computable (T : Tree) (hT : ComputablePred T.mem) :
    ComputablePred (fun p : Node × Node => SChild T p.1 p.2) := by
  have hm := (STree_computable T hT).comp' (Computable.snd : Computable (fun p : Node × Node => p.2))
  have hl : PrimrecPred (fun p : Node × Node => p.2.length = p.1.length + 1) :=
    Primrec.eq.comp (Primrec.list_length.comp Primrec.snd)
      (Primrec.succ.comp (Primrec.list_length.comp Primrec.fst))
  have hp : PrimrecPred (fun p : Node × Node => Effective.takeNode (p.2, p.1.length) = p.1) :=
    Primrec.eq.comp (Effective.takeNode_primrec.comp
      (Primrec.snd.pair (Primrec.list_length.comp Primrec.fst))) Primrec.fst
  exact (hm.and' (hl.computablePred.and' hp.computablePred)).of_eq
    (by simp [SChild, Effective.takeNode_eq])

theorem deadLevel_computable (T : Tree) (hT : ComputablePred T.mem) (n : ℕ) :
    ComputablePred (fun σ : Node => σ ∈ deadLevel (STree T) n) := by
  have hm := STree_computable T hT
  have hl : PrimrecPred (fun σ : Node => σ.length = n) :=
    Primrec.eq.comp Primrec.list_length (Primrec.const n)
  have he := (lemma2_ext_primrec T n).computablePred
  exact ((hm.and' hl.computablePred).and' he.not).of_eq (by
    intro σ
    simp only [deadLevel, extLevel, Set.mem_setOf_eq]
    tauto)

/-- The relation presenting the local ordinal is itself computable. The
finite bases used here are fixed constants for this n. -/
theorem LocalRel_computable (T : Tree) (hT : ComputablePred T.mem) (n : ℕ) :
    ComputablePred (fun p : Option Node × Option Node => LocalRel T n p.1 p.2) := by
  classical
  let left : Option Node × Option Node → Node := fun p => p.1.getD []
  let right : Option Node × Option Node → Node := fun p => p.2.getD []
  have hleft : Primrec left := Primrec.option_getD.comp Primrec.fst (Primrec.const [])
  have hright : Primrec right := Primrec.option_getD.comp Primrec.snd (Primrec.const [])
  have hl : ComputablePred (fun p : Option Node × Option Node => p.1.isSome = true) :=
    ((Primrec.eq.comp (Primrec.option_isSome.comp Primrec.fst) (Primrec.const true))).computablePred
  have hr : ComputablePred (fun p : Option Node × Option Node => p.2.isSome = true) :=
    ((Primrec.eq.comp (Primrec.option_isSome.comp Primrec.snd) (Primrec.const true))).computablePred
  have hc := (SChild_computable T hT).comp' (hright.pair hleft).to_comp
  have hd := (deadLevel_computable T hT n).comp' hleft.to_comp
  apply ((hl.and' (hr.and' hc)).or' (hl.and' (hr.not.and' hd))).of_eq
  rintro ⟨x, y⟩
  cases x <;> cases y <;> simp [LocalRel, left, right]

/-- A rooted recursive well-founded relation is a recursive ordinal
presentation. Its ordinal is its actual accessibility rank. -/
structure RecursiveOrdinal (α : Type) [Primcodable α] where
  rel : α → α → Prop
  recursive : ComputablePred (fun p : α × α => rel p.1 p.2)
  root : α
  accessible : Acc rel root

noncomputable def RecursiveOrdinal.val {α : Type} [Primcodable α]
    (a : RecursiveOrdinal α) : Ordinal := a.accessible.rank

def levelOrdinal (T : Tree) (hT : ComputablePred T.mem) (n : ℕ) : RecursiveOrdinal (Option Node) :=
  ⟨LocalRel T n, LocalRel_computable T hT n, none, local_root_accessible T n⟩

/-- Lemma 3 with the effective ordinal presentation supplied, rather than
only an unspecified well-founded relation. -/
theorem lemma3_effective_bound (T : Tree) (hT : ComputablePred T.mem) (n : ℕ) :
    ∃ a : RecursiveOrdinal (Option Node),
      ∀ σ ∈ deadLevel (STree T) n,
        ∀ hs : Acc (fun τ σ => SChild T σ τ) σ, hs.rank < a.val := by
  exact ⟨levelOrdinal T hT n, fun σ hd hs => lemma3_ordinal_bound T n σ hd hs⟩

end Paper19
