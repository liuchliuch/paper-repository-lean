import Paper28.TreeBranches

/-! Native graph-theoretic edge cuts. The two sides and the retained terminal
vertices are constructed from the actual original tree. No analytic estimate
or branch-factorization assumption is introduced. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open SimpleGraph
variable {V : Type*} (T : SimpleGraph V)

def cutGraph (v w : V) : SimpleGraph V := T.deleteEdges {s(v, w)}
def cutSide (v w : V) : Set V := {x | (cutGraph T v w).Reachable v x}
def retainedSide (v w : V) : Set V := cutSide T v w ∪ {w}
def retainedTree (v w : V) : SimpleGraph (retainedSide T v w) := T.induce (retainedSide T v w)

/-- Every vertex of a connected graph lies on one of the two sides after
removing a bridge. The covering part does not require acyclicity. -/
theorem cut_sides_cover (hT : T.Connected) (v w x : V) :
    x ∈ cutSide T v w ∨ x ∈ cutSide T w v := by
  classical
  have step (a b : V) (hab : T.Adj a b)
      (ha : (cutGraph T v w).Reachable v a ∨ (cutGraph T v w).Reachable w a) :
      (cutGraph T v w).Reachable v b ∨ (cutGraph T v w).Reachable w b := by
    by_cases h : s(a, b) = s(v, w)
    · rcases Sym2.eq_iff.mp h with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact Or.inr .rfl
      · exact Or.inl .rfl
    · have hd : (cutGraph T v w).Adj a b := by
        exact deleteEdges_adj.mpr ⟨hab, by simpa using h⟩
      exact ha.elim (fun hv => Or.inl (hv.trans hd.reachable))
        (fun hw => Or.inr (hw.trans hd.reachable))
  have hp := (reachable_iff_reflTransGen v x).mp (hT v x)
  have h : (cutGraph T v w).Reachable v x ∨ (cutGraph T v w).Reachable w x := by
    induction hp with
    | refl => exact Or.inl .rfl
    | @tail a b hp hab ih => exact step a b hab ih
  simpa [cutSide, cutGraph, Sym2.eq_swap] using h

/-- The sides of a tree edge are disjoint. -/
theorem cut_sides_disjoint (hT : T.IsTree) (v w : V) (hvw : T.Adj v w) :
    Disjoint (cutSide T v w) (cutSide T w v) := by
  have hb := (isBridge_iff.mp ((isAcyclic_iff_forall_adj_isBridge.mp hT.IsAcyclic) hvw)).2
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hy' : (cutGraph T v w).Reachable w x := by
    simpa [cutSide, cutGraph, Sym2.eq_swap] using hy
  exact hb (hx.trans hy'.symm)

/-- The only original edge between the two sides is the cut edge. -/
theorem cross_edge_eq_cut (hT : T.IsTree) (v w a b : V) (hvw : T.Adj v w)
    (ha : a ∈ cutSide T v w) (hb : b ∈ cutSide T w v) (hab : T.Adj a b) :
    s(a, b) = s(v, w) := by
  classical
  by_contra h
  have hd : (cutGraph T v w).Adj a b := deleteEdges_adj.mpr ⟨hab, by simpa using h⟩
  exact Set.disjoint_left.mp (cut_sides_disjoint T hT v w hvw) (ha.trans hd.reachable) hb

/-- The side itself is connected in the original graph. -/
theorem cut_side_connected (v w : V) : (T.induce (cutSide T v w)).Connected := by
  let D := cutGraph T v w
  have hset : cutSide T v w = (D.connectedComponentMk v).supp := by
    ext x
    simp only [cutSide, Set.mem_setOf_eq, ConnectedComponent.mem_supp_iff, ConnectedComponent.eq]
    exact reachable_comm
  rw [hset]
  apply SimpleGraph.Connected.mono (show D.induce _ ≤ T.induce _ from fun a b h =>
    (deleteEdges_le (G := T) {s(v,w)}) h)
  exact (D.connectedComponentMk v).connected_toSimpleGraph

/-- A singleton is connected, with the literal subtype vertex set. -/
theorem singleton_induce_connected (w : V) : (T.induce ({w} : Set V)).Connected := by
  refine { preconnected := ?_, nonempty := ⟨⟨w, Set.mem_singleton w⟩⟩ }
  intro a b
  have ha : a.val = w := a.property
  have hb : b.val = w := b.property
  have heq : a = b := Subtype.ext (ha.trans hb.symm)
  subst b
  exact .rfl

/-- Retaining the cut edge as a terminal edge gives an actual smaller tree. -/
theorem retainedTree_isTree (hT : T.IsTree) (v w : V) (hvw : T.Adj v w) :
    (retainedTree T v w).IsTree := by
  constructor
  · exact induce_connected_adj_union (cut_side_connected T v w) (singleton_induce_connected T w)
      (show v ∈ cutSide T v w from .rfl) (Set.mem_singleton w) hvw
  · exact hT.IsAcyclic.induce _

/-- The opposite terminal endpoint has no neighbor in a retained side
other than the original cut endpoint. -/
theorem retained_terminal_neighbor (hT : T.IsTree) (v w : V) (hvw : T.Adj v w)
    (x : V) (hx : x ∈ retainedSide T v w) (hwx : T.Adj w x) : x = v := by
  rcases hx with hx | hx
  · have he := cross_edge_eq_cut T hT v w x w hvw hx (show w ∈ cutSide T w v from .rfl) hwx.symm
    rcases Sym2.eq_iff.mp he with ⟨h, _⟩ | ⟨_, h⟩
    · exact h
    · exact False.elim (hvw.ne h.symm)
  · have h : x = w := hx
    exact False.elim (hwx.ne h.symm)

/-- A neighbor beyond the terminal endpoint is excluded from the retained tree. -/
theorem outside_retainedSide (hT : T.IsTree) (v w b : V)
    (hvw : T.Adj v w) (hwb : T.Adj w b) (hb : b ≠ v) :
    b ∉ retainedSide T v w := by
  intro h
  exact hb (retained_terminal_neighbor T hT v w hvw b h hwb)

/-- Native strict size decrease for an internal-edge cut, using vertex count. -/
theorem retainedTree_card_lt [Finite V] (hT : T.IsTree) (v w b : V)
    (hvw : T.Adj v w) (hwb : T.Adj w b) (hb : b ≠ v) :
    Nat.card (retainedSide T v w) < Nat.card V := by
  classical
  letI := Fintype.ofFinite V
  letI := Fintype.ofFinite (retainedSide T v w)
  have hnot : ¬ Function.Surjective (Subtype.val : retainedSide T v w → V) := by
    intro hs
    obtain ⟨x, hx⟩ := hs b
    exact outside_retainedSide T hT v w b hvw hwb hb (hx ▸ x.property)
  simpa only [Nat.card_eq_fintype_card] using
    Fintype.card_lt_of_injective_not_surjective (f := (Subtype.val : retainedSide T v w → V))
      Subtype.val_injective hnot

end Paper28
