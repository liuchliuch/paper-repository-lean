import Paper28.BranchNaturality

/-! The edge-cut folding uses the actual smaller tree: all surviving edges
are retained, and all other edges are folded into its terminal edge. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open SimpleGraph
variable {V : Type*} (T : SimpleGraph V)

def retainedEmbedding (v w : V) : retainedTree T v w ↪g T :=
  SimpleGraph.Embedding.induce (retainedSide T v w)

def retainedCutEdge (v w : V) (hvw : T.Adj v w) : (retainedTree T v w).edgeSet :=
  ⟨s(⟨v, Or.inl (.rfl : (cutGraph T v w).Reachable v v)⟩, ⟨w, Or.inr rfl⟩), hvw⟩

theorem retainedCutEdge_map (v w : V) (hvw : T.Adj v w) :
    (retainedEmbedding T v w).mapEdgeSet (retainedCutEdge T v w hvw) = ⟨s(v,w), hvw⟩ := by
  rfl

/-- An edge meeting the original side is an edge of the retained subtree. -/
theorem edge_survives_of_left_endpoint (hT : T.IsTree) (v w : V) (hvw : T.Adj v w)
    (e : T.edgeSet) (a : V) (ha : a ∈ e.val) (haL : a ∈ cutSide T v w) :
    ∃ d, (retainedEmbedding T v w).mapEdgeSet d = e := by
  let b := Sym2.Mem.other ha
  have he : s(a,b) = e.val := Sym2.other_spec ha
  have hab : T.Adj a b := (T.mem_edgeSet).mp (he.symm ▸ e.property)
  have hb : b ∈ retainedSide T v w := retained_neighbor_mem T hT v w a b hvw haL hab
  let d : (retainedTree T v w).edgeSet := ⟨s(⟨a, Or.inl haL⟩, ⟨b, hb⟩), hab⟩
  refine ⟨d, ?_⟩
  apply Subtype.ext
  exact he

/-- The actual partition of edge coordinates for one side of the cut. -/
def collapseEdge (v w : V) (hvw : T.Adj v w) (e : T.edgeSet) :
    (retainedTree T v w).edgeSet := by
  classical
  exact if h : ∃ d, (retainedEmbedding T v w).mapEdgeSet d = e then h.choose
  else retainedCutEdge T v w hvw

theorem collapseEdge_map (v w : V) (hvw : T.Adj v w)
    (d : (retainedTree T v w).edgeSet) :
    collapseEdge T v w hvw ((retainedEmbedding T v w).mapEdgeSet d) = d := by
  classical
  have h : ∃ d', (retainedEmbedding T v w).mapEdgeSet d' =
      (retainedEmbedding T v w).mapEdgeSet d := ⟨d, rfl⟩
  simp only [collapseEdge, dif_pos h]
  exact (retainedEmbedding T v w).mapEdgeSet.injective h.choose_spec

/-- Exact branch-routing factorization at each original vertex on this side.
The factorization is proved from the original tree, not supplied as an input. -/
theorem treeBranch_collapse (hT : T.IsTree) (v w : V) (hvw : T.Adj v w)
    (x : V) (hx : x ∈ cutSide T v w) (e : T.edgeSet) :
    treeBranch T hT x e =
      retainedNeighborEquiv T hT v w hvw x hx
        (treeBranch (retainedTree T v w) (retainedTree_isTree T hT v w hvw)
          ⟨x, Or.inl hx⟩ (collapseEdge T v w hvw e)) := by
  classical
  let f := retainedEmbedding T v w
  let hS := retainedTree_isTree T hT v w hvw
  let x' : retainedSide T v w := ⟨x, Or.inl hx⟩
  change treeBranch T hT x e = f.mapNeighborSet x' (treeBranch _ hS x' _)
  by_cases h : ∃ d, f.mapEdgeSet d = e
  · obtain ⟨d, rfl⟩ := h
    rw [collapseEdge_map]
    exact (treeBranch_map _ T hS hT f x' d).symm
  · have hc : collapseEdge T v w hvw e = retainedCutEdge T v w hvw := by
      exact dif_neg h
    rw [hc]
    rw [treeBranch_map _ T hS hT f x' (retainedCutEdge T v w hvw)]
    rw [retainedCutEdge_map]
    change treeBranch T hT x e = treeBranch T hT x ⟨s(v,w), hvw⟩
    let a := edgeTarget T x e
    have haR : a.val ∈ cutSide T w v := by
      rcases cut_sides_cover T hT.isConnected v w a.val with haL | haR
      · exact False.elim (h (edge_survives_of_left_endpoint T hT v w hvw e a.val a.property.1 haL))
      · exact haR
    have hwx : w ≠ x := fun he =>
      Set.disjoint_left.mp (cut_sides_disjoint T hT v w hvw) hx
        (he ▸ show w ∈ cutSide T w v from .rfl)
    rw [treeBranch_eq_firstNeighbor_endpoint T hT x e a.val a.property.1 a.property.2,
      treeBranch_eq_firstNeighbor_endpoint T hT x ⟨s(v,w), hvw⟩ w (by simp) hwx]
    exact firstNeighbor_opposite_side T hT v w x a.val hvw hx haR

end Paper28
