import Paper28.TreeCuts

/-! Naturality of the actual branch routing and neighbor sets under embedded
subtrees. This provides the graph content of the shadow edge-cut factorization. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open SimpleGraph
variable {V W : Type*} (T : SimpleGraph V) (U : SimpleGraph W)

theorem walk_snd_map (f : T →g U) {a b : V} (p : T.Walk a b) :
    (p.map f).snd = f p.snd := by
  cases p <;> simp [Walk.snd, Walk.getVert, Walk.map]

theorem treePath_map (hT : T.IsTree) (hU : U.IsTree) (f : T ↪g U) (a b : V) :
    (treePath T hT a b).map f.toHom = treePath U hU (f a) (f b) := by
  apply (hU.existsUnique_path (f a) (f b)).unique
  · exact Walk.map_isPath_of_injective f.injective (treePath_isPath T hT a b)
  · exact treePath_isPath U hU (f a) (f b)

theorem firstNeighbor_map (hT : T.IsTree) (hU : U.IsTree) (f : T ↪g U)
    (a b : V) (hb : b ≠ a) :
    f.mapNeighborSet a (firstNeighbor T hT a b hb) =
      firstNeighbor U hU (f a) (f b) (fun h => hb (f.injective h)) := by
  apply Subtype.ext
  change f (treePath T hT a b).snd = (treePath U hU (f a) (f b)).snd
  rw [← treePath_map T U hT hU f a b]
  exact (walk_snd_map T U f.toHom _).symm

/-- Branch routing commutes with embedding one tree in another. The endpoint
chosen internally need not be the endpoint chosen after embedding. -/
theorem treeBranch_map (hT : T.IsTree) (hU : U.IsTree) (f : T ↪g U)
    (a : V) (e : T.edgeSet) :
    f.mapNeighborSet a (treeBranch T hT a e) =
      treeBranch U hU (f a) (f.mapEdgeSet e) := by
  let b := edgeTarget T a e
  have hb : f b.val ∈ (f.mapEdgeSet e).val := by
    exact Sym2.mem_map.mpr ⟨b.val, b.property.1, rfl⟩
  have hne : f b.val ≠ f a := fun h => b.property.2 (f.injective h)
  rw [treeBranch_eq_firstNeighbor_endpoint U hU (f a) (f.mapEdgeSet e) (f b.val) hb hne]
  exact firstNeighbor_map T U hT hU f a b.val b.property.2

end Paper28

namespace Paper28
open SimpleGraph
variable {V : Type*} (T : SimpleGraph V)

/-- Every original neighbor of a nonterminal left vertex survives the cut. -/
theorem retained_neighbor_mem (hT : T.IsTree) (v w x y : V) (hvw : T.Adj v w)
    (hx : x ∈ cutSide T v w) (hxy : T.Adj x y) : y ∈ retainedSide T v w := by
  rcases cut_sides_cover T hT.isConnected v w y with hy | hy
  · exact Or.inl hy
  · have he := cross_edge_eq_cut T hT v w x y hvw hx hy hxy
    rcases Sym2.eq_iff.mp he with ⟨_, hyw⟩ | ⟨hxw, _⟩
    · exact Or.inr hyw
    · exact False.elim (Set.disjoint_left.mp (cut_sides_disjoint T hT v w hvw)
        hx (show x ∈ cutSide T w v from hxw.symm ▸ .rfl))

/-- The original incident edges at each left-side vertex are exactly the
incident edges of the retained subtree, canonically indexed by neighbors. -/
def retainedNeighborEquiv (hT : T.IsTree) (v w : V) (hvw : T.Adj v w)
    (x : V) (hx : x ∈ cutSide T v w) :
    (retainedTree T v w).neighborSet ⟨x, Or.inl hx⟩ ≃ T.neighborSet x :=
  Equiv.ofBijective ((SimpleGraph.Embedding.induce (retainedSide T v w)).mapNeighborSet ⟨x, Or.inl hx⟩)
    ⟨Function.Embedding.injective _, by
      intro y
      let z : retainedSide T v w := ⟨y.val, retained_neighbor_mem T hT v w x y.val hvw hx y.property⟩
      refine ⟨⟨z, y.property⟩, ?_⟩
      apply Subtype.ext
      rfl⟩

end Paper28

namespace Paper28
open SimpleGraph
variable {V : Type*} (T : SimpleGraph V)

/-- All destinations in the opposite cut component have the same first
neighbor from a fixed vertex on this side. -/
theorem firstNeighbor_opposite_side (hT : T.IsTree) (v w x a : V)
    (hvw : T.Adj v w) (hx : x ∈ cutSide T v w) (ha : a ∈ cutSide T w v) :
    firstNeighbor T hT x a
        (fun h => Set.disjoint_left.mp (cut_sides_disjoint T hT v w hvw) hx (h ▸ ha)) =
      firstNeighbor T hT x w
        (fun h => Set.disjoint_left.mp (cut_sides_disjoint T hT v w hvw) hx
          (h ▸ show w ∈ cutSide T w v from .rfl)) := by
  let hax : a ≠ x := fun h =>
    Set.disjoint_left.mp (cut_sides_disjoint T hT v w hvw) hx (h ▸ ha)
  let hwx : w ≠ x := fun h =>
    Set.disjoint_left.mp (cut_sides_disjoint T hT v w hvw) hx
      (h ▸ show w ∈ cutSide T w v from .rfl)
  have hs : cutSide T w v ⊆ {z | z ≠ x} := by
    intro z hz hzx
    exact Set.disjoint_left.mp (cut_sides_disjoint T hT v w hvw) hx (hzx ▸ hz)
  have hwa : (T.induce {z | z ≠ x}).Reachable ⟨w, hwx⟩ ⟨a, hax⟩ :=
    ((cut_side_connected T w v) ⟨w, show w ∈ cutSide T w v from .rfl⟩ ⟨a, ha⟩).map
      (T.induceHomOfLE hs).toHom
  let b := firstNeighbor T hT x w hwx
  have hbw := (firstNeighbor_eq_iff_deleted_reachable T hT x w hwx b).mp rfl
  exact (firstNeighbor_eq_iff_deleted_reachable T hT x a hax b).mpr (hbw.trans hwa)

end Paper28
