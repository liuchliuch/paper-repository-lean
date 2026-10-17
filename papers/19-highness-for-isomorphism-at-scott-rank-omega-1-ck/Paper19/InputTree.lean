import Paper19.EffectiveRank

namespace Paper19

/-- The paper's input convention allows the empty prefix-closed tree. The
internal rooted Tree API is reached by a uniform root completion. -/
structure InputTree where
  mem : Node → Prop
  decMem : ∀ σ, Decidable (mem σ)
  mem_prefix : ∀ {σ τ}, mem τ → σ <+: τ → mem σ

attribute [instance] InputTree.decMem

def InputTree.IsPath (T : InputTree) (f : Stream) : Prop :=
  ∀ n, T.mem (List.ofFn (fun i : Fin n => f i))

def InputTree.rootCompletion (T : InputTree) : Tree where
  mem := fun σ => σ=[] ∨ T.mem σ
  decMem := fun _ => inferInstance
  mem_nil := Or.inl rfl
  mem_prefix := by
    intro σ τ hτ hp
    rcases hτ with rfl | hτ
    · exact Or.inl (List.eq_nil_of_length_eq_zero (by have := hp.length_le; simp_all))
    · exact Or.inr (T.mem_prefix hτ hp)

theorem InputTree.path_iff_rootCompletion (T : InputTree) (f : Stream) :
    T.IsPath f ↔ T.rootCompletion.IsPath f := by
  constructor
  · intro h n; exact Or.inr (h n)
  · intro h n
    have h1 : T.mem (List.ofFn (fun i : Fin 1 => f i)) := by
      rcases h 1 with hempty | hm
      · have hh := congrArg List.length hempty; simp at hh
      · exact hm
    cases n with
    | zero => exact T.mem_prefix h1 (List.nil_prefix)
    | succ n =>
      rcases h (n+1) with hempty | hm
      · have hh := congrArg List.length hempty; simp at hh
      · exact hm

theorem InputTree.rootCompletion_computable (T : InputTree) (hT : ComputablePred T.mem) :
    ComputablePred T.rootCompletion.mem :=
  ((Primrec.eq.comp Primrec.id (Primrec.const ([] : Node))).computablePred.or' hT)

def InputTree.empty : InputTree where
  mem := fun _ => False
  decMem := fun _ => isFalse id
  mem_prefix := fun h _ => False.elim h

theorem InputTree.empty_no_path : ¬∃ f, InputTree.empty.IsPath f := by
  rintro ⟨f,hf⟩; exact hf 0

end Paper19
