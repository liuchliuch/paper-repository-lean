/-
Copyright (c) 2026. Counter-Free Higher-Dimensional Automata formalisation.
Extension of inequalities on finite acyclic digraphs (Lemma 3.2).
-/
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.RelClasses
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Image
import Mathlib.Tactic

/-!
# Extension of inequalities (Lemma 3.2)

Let `Γ` be a finite acyclic directed graph.  Associate a complete lattice `A_v`
to each vertex and a join-preserving map to each arc.  Prescribed values at a
subset `B` of vertices extend to a colouring of all vertices satisfying every
arc inequality if and only if the path inequalities hold between prescribed
vertices.  The least extension is `â_v = ⋁ { f_p(a_b) | b ∈ B, p : b ⟶ v }`
together with `a_v` itself when `v ∈ B`.

Paths are represented by a type-valued inductive `AcyclicDigraph.Path`, because
`Relation.TransGen` is `Prop`-valued and therefore cannot be eliminated into
`Type` in order to define `pathApply`.
-/

namespace CounterFreeHDA

universe u v w

/-- Join-preserving map between complete lattices. -/
structure JoinHom (α : Type v) (β : Type w) [CompleteLattice α] [CompleteLattice β] where
  toFun : α → β
  map_bot' : toFun ⊥ = ⊥
  map_sSup' : ∀ s : Set α, toFun (sSup s) = sSup (Set.image toFun s)

namespace JoinHom

variable {α : Type v} {β : Type w} [CompleteLattice α] [CompleteLattice β]

instance : CoeFun (JoinHom α β) (fun _ => α → β) := ⟨toFun⟩

@[simp] theorem map_bot (f : JoinHom α β) : f.toFun ⊥ = ⊥ := f.map_bot'

theorem map_sSup (f : JoinHom α β) (s : Set α) :
    f.toFun (sSup s) = sSup (Set.image f.toFun s) := f.map_sSup' s

theorem map_mono (f : JoinHom α β) ⦃a b : α⦄ (h : a ≤ b) : f.toFun a ≤ f.toFun b := by
  have ha : a = sSup {x : α | x ≤ a} :=
    le_antisymm (le_sSup (le_refl a)) (sSup_le fun _ hx => hx)
  have hb : b = sSup {x : α | x ≤ b} :=
    le_antisymm (le_sSup (le_refl b)) (sSup_le fun _ hx => hx)
  have hsub : {x : α | x ≤ a} ⊆ {x : α | x ≤ b} := fun _ hx => le_trans hx h
  calc f.toFun a = f.toFun (sSup {x : α | x ≤ a}) := congrArg f.toFun ha
    _ = sSup (f.toFun '' {x : α | x ≤ a}) := f.map_sSup _
    _ ≤ sSup (f.toFun '' {x : α | x ≤ b}) := sSup_le_sSup (Set.image_mono hsub)
    _ = f.toFun (sSup {x : α | x ≤ b}) := (f.map_sSup _).symm
    _ = f.toFun b := congrArg f.toFun hb.symm

end JoinHom

/-- An acyclic digraph on `V`. -/
structure AcyclicDigraph (V : Type u) where
  arc : V → V → Prop

namespace AcyclicDigraph

variable {V : Type u} (G : AcyclicDigraph V)

/-- Nonempty path reachability. -/
def Reach (x y : V) : Prop := Relation.TransGen G.arc x y

end AcyclicDigraph

/-- Nonempty directed path in `G`.  A type-valued inductive (rather than
`Relation.TransGen`, which is `Prop`-valued) so that we can recurse into
`Type` and define `pathApply`. -/
inductive AcyclicDigraph.Path {V : Type u} (G : AcyclicDigraph V) : V → V → Type u where
  | single {x y : V} (e : G.arc x y) : Path G x y
  | snoc {x y z : V} (p : Path G x y) (e : G.arc y z) : Path G x z

/-- Composite of arc maps along a path. -/
noncomputable def pathApply {V : Type u} {A : V → Type v} [∀ v, CompleteLattice (A v)]
    {G : AcyclicDigraph V}
    (f : ∀ ⦃x y : V⦄, G.arc x y → JoinHom (A x) (A y)) :
    ∀ {x y : V}, AcyclicDigraph.Path G x y → A x → A y := by
  intro x y p
  induction p with
  | single e => exact fun a => (f e).toFun a
  | snoc q e ih => exact fun a => (f e).toFun (ih a)

theorem pathApply_single {V : Type u} {A : V → Type v} [∀ v, CompleteLattice (A v)]
    {G : AcyclicDigraph V}
    (f : ∀ ⦃x y : V⦄, G.arc x y → JoinHom (A x) (A y))
    {x y : V} (e : G.arc x y) (a : A x) :
    pathApply f (AcyclicDigraph.Path.single e) a = (f e).toFun a := rfl

theorem pathApply_snoc {V : Type u} {A : V → Type v} [∀ v, CompleteLattice (A v)]
    {G : AcyclicDigraph V}
    (f : ∀ ⦃x y : V⦄, G.arc x y → JoinHom (A x) (A y))
    {x y z : V} (q : AcyclicDigraph.Path G x y) (e : G.arc y z) (a : A x) :
    pathApply f (AcyclicDigraph.Path.snoc q e) a = (f e).toFun (pathApply f q a) := rfl

/-- `pathApply` preserves joins. -/
theorem pathApply_sSup {V : Type u} {A : V → Type v} [∀ v, CompleteLattice (A v)]
    {G : AcyclicDigraph V}
    (f : ∀ ⦃x y : V⦄, G.arc x y → JoinHom (A x) (A y))
    {x y : V} (p : AcyclicDigraph.Path G x y) (s : Set (A x)) :
    pathApply f p (sSup s) = sSup (Set.image (pathApply f p) s) := by
  induction p with
  | single e => exact (f e).map_sSup s
  | snoc q e ih =>
    rw [pathApply_snoc, ih, (f e).map_sSup, Set.image_image]
    rfl

theorem pathApply_bot {V : Type u} {A : V → Type v} [∀ v, CompleteLattice (A v)]
    {G : AcyclicDigraph V}
    (f : ∀ ⦃x y : V⦄, G.arc x y → JoinHom (A x) (A y))
    {x y : V} (p : AcyclicDigraph.Path G x y) :
    pathApply f p ⊥ = ⊥ := by
  induction p with
  | single e => exact (f e).map_bot
  | snoc q e ih =>
    rw [pathApply_snoc, ih, (f e).map_bot]

/-! ## Necessity -/

/-- Any colouring that extends the prescribed values and satisfies every arc
inequality also satisfies all path inequalities between prescribed vertices. -/
theorem lemma_3_2_necessity
    {V : Type u}
    {G : AcyclicDigraph V}
    {A : V → Type v} [∀ v, CompleteLattice (A v)]
    (f : ∀ ⦃x y : V⦄, G.arc x y → JoinHom (A x) (A y))
    (B : Set V) (aB : ∀ v, A v)
    (a : ∀ v, A v)
    (hext : ∀ v ∈ B, a v = aB v)
    (harc : ∀ ⦃x y⦄ (e : G.arc x y), (f e).toFun (a x) ≤ a y) :
    ∀ ⦃x y⦄ (p : AcyclicDigraph.Path G x y), x ∈ B → y ∈ B →
      pathApply f p (aB x) ≤ aB y := by
  intro x y p hx hy
  have hcomp : ∀ {u w} (q : AcyclicDigraph.Path G u w),
      pathApply f q (a u) ≤ a w := by
    intro u w q
    induction q with
    | single e => exact harc e
    | snoc q e ih =>
      rw [pathApply_snoc]
      exact le_trans (JoinHom.map_mono (f e) ih) (harc e)
  rw [← hext x hx, ← hext y hy]
  exact hcomp p

/-! ## Sufficiency: the least extension -/

/-- Contribution set at `v`: images of prescribed values along paths, plus the
prescribed value itself at `v ∈ B` (length-zero path). -/
def contribSet {V : Type u} {G : AcyclicDigraph V}
    {A : V → Type v} [∀ v, CompleteLattice (A v)]
    (f : ∀ ⦃x y : V⦄, G.arc x y → JoinHom (A x) (A y))
    (B : Set V) (aB : ∀ v, A v) (v : V) : Set (A v) :=
  {w | (∃ (b : V) (_ : b ∈ B) (p : AcyclicDigraph.Path G b v),
      pathApply f p (aB b) = w) ∨ (v ∈ B ∧ w = aB v)}

/-- Least extension `â_v = ⋁ contribSet ... v`. -/
noncomputable def leastColouring {V : Type u} {G : AcyclicDigraph V}
    {A : V → Type v} [∀ v, CompleteLattice (A v)]
    (f : ∀ ⦃x y : V⦄, G.arc x y → JoinHom (A x) (A y))
    (B : Set V) (aB : ∀ v, A v) (v : V) : A v :=
  sSup (contribSet f B aB v)

/-- On prescribed vertices the least extension recovers the value, under the
path inequalities. -/
theorem leastColouring_on_B {V : Type u} {G : AcyclicDigraph V}
    {A : V → Type v} [∀ v, CompleteLattice (A v)]
    (f : ∀ ⦃x y : V⦄, G.arc x y → JoinHom (A x) (A y))
    (B : Set V) (aB : ∀ v, A v)
    (hPath : ∀ ⦃x y⦄ (p : AcyclicDigraph.Path G x y), x ∈ B → y ∈ B →
      pathApply f p (aB x) ≤ aB y)
    {v : V} (hv : v ∈ B) :
    leastColouring f B aB v = aB v := by
  unfold leastColouring contribSet
  apply le_antisymm
  · refine sSup_le ?_
    intro w hw
    rcases hw with ⟨b, hb, p, rfl⟩ | ⟨_, rfl⟩
    · exact hPath p hb hv
    · exact le_refl _
  · refine le_sSup ?_
    exact Or.inr ⟨hv, rfl⟩

/-- The least colouring satisfies every arc inequality, under the path
inequalities. -/
theorem leastColouring_arcs {V : Type u} {G : AcyclicDigraph V}
    {A : V → Type v} [∀ v, CompleteLattice (A v)]
    (f : ∀ ⦃x y : V⦄, G.arc x y → JoinHom (A x) (A y))
    (B : Set V) (aB : ∀ v, A v) :
    ∀ ⦃x y⦄ (e : G.arc x y),
      (f e).toFun (leastColouring f B aB x) ≤ leastColouring f B aB y := by
  intro x y e
  have h1 : (f e).toFun (sSup (contribSet f B aB x))
      = sSup (Set.image (f e).toFun (contribSet f B aB x)) := (f e).map_sSup _
  show (f e).toFun (sSup (contribSet f B aB x)) ≤ sSup (contribSet f B aB y)
  rw [h1]
  refine sSup_le ?_
  intro w hw
  obtain ⟨s, hs, rfl⟩ := (Set.mem_image _ _ _).mp hw
  rcases hs with ⟨b, hb, p, rfl⟩ | ⟨hxb, rfl⟩
  · have heq : (f e).toFun (pathApply f p (aB b))
        = pathApply f (AcyclicDigraph.Path.snoc p e) (aB b) := rfl
    rw [heq]
    refine le_sSup ?_
    exact Or.inl ⟨b, hb, AcyclicDigraph.Path.snoc p e, rfl⟩
  · have heq : (f e).toFun (aB x)
        = pathApply f (AcyclicDigraph.Path.single e) (aB x) := rfl
    rw [heq]
    refine le_sSup ?_
    exact Or.inl ⟨x, hxb, AcyclicDigraph.Path.single e, rfl⟩

/-- **Lemma 3.2 (sufficiency).**  If the path inequalities hold, then there is a
colouring extending the prescribed values and satisfying every arc inequality. -/
theorem lemma_3_2_sufficiency {V : Type u} {G : AcyclicDigraph V}
    {A : V → Type v} [∀ v, CompleteLattice (A v)]
    (f : ∀ ⦃x y : V⦄, G.arc x y → JoinHom (A x) (A y))
    (B : Set V) (aB : ∀ v, A v)
    (hPath : ∀ ⦃x y⦄ (p : AcyclicDigraph.Path G x y), x ∈ B → y ∈ B →
      pathApply f p (aB x) ≤ aB y) :
    ∃ a : ∀ v, A v, (∀ v ∈ B, a v = aB v) ∧
      (∀ ⦃x y⦄ (e : G.arc x y), (f e).toFun (a x) ≤ a y) := by
  refine ⟨leastColouring f B aB, ?_, leastColouring_arcs f B aB⟩
  intro v hv
  exact leastColouring_on_B f B aB hPath hv

/-- **Lemma 3.2.**  A prescribed partial colouring extends to a full colouring
satisfying every arc inequality iff the path inequalities hold. -/
theorem lemma_3_2 {V : Type u} {G : AcyclicDigraph V}
    {A : V → Type v} [∀ v, CompleteLattice (A v)]
    (f : ∀ ⦃x y : V⦄, G.arc x y → JoinHom (A x) (A y))
    (B : Set V) (aB : ∀ v, A v) :
    (∃ a : ∀ v, A v, (∀ v ∈ B, a v = aB v) ∧
        (∀ ⦃x y⦄ (e : G.arc x y), (f e).toFun (a x) ≤ a y)) ↔
      (∀ ⦃x y⦄ (p : AcyclicDigraph.Path G x y), x ∈ B → y ∈ B →
        pathApply f p (aB x) ≤ aB y) := by
  constructor
  · intro ⟨a, hext, harc⟩
    exact lemma_3_2_necessity f B aB a hext harc
  · intro hPath
    exact lemma_3_2_sufficiency f B aB hPath

end CounterFreeHDA
