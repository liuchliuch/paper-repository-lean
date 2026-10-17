import Paper28.TreeShadows
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-! Identification of the actual unique-path routing with the connected
components of the vertex-deleted tree. No external tree result is assumed
beyond mathlib's unique-simple-path characterization. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open SimpleGraph
variable {V : Type*} (T : SimpleGraph V)

/-- The incident neighbor on the unique path from v to a distinct vertex. -/
def firstNeighbor (hT : T.IsTree) (v a : V) (ha : a ≠ v) : T.neighborSet v :=
  ⟨(treePath T hT v a).snd, Walk.adj_snd (Walk.not_nil_of_ne ha.symm)⟩

/-- Routing to a vertex is characterized by a walk which avoids v. -/
theorem firstNeighbor_eq_iff_avoiding (hT : T.IsTree) (v a : V) (ha : a ≠ v)
    (w : T.neighborSet v) :
    firstNeighbor T hT v a ha = w ↔
      ∃ p : T.Walk w.val a, v ∉ p.support := by
  classical
  constructor
  · intro heq
    have hp := treePath_isPath T hT v a
    have hne : ¬ (treePath T hT v a).Nil := Walk.not_nil_of_ne ha.symm
    have hf : (treePath T hT v a).snd = w.val := congrArg Subtype.val heq
    generalize hq : treePath T hT v a = q at hp hne hf
    cases q with
    | nil => exact False.elim (hne Walk.nil_nil)
    | @cons v b a hvb p =>
      have hw : b = w.val := by simpa [Walk.snd, Walk.getVert] using hf
      have hv : v ∉ p.support := (Walk.cons_isPath_iff hvb p).mp hp |>.2
      subst b
      exact ⟨p, hv⟩
  · rintro ⟨p, hp⟩
    let q := p.toPath
    have hq : v ∉ (q : T.Walk w.val a).support :=
      fun h => hp (p.support_toPath_subset h)
    have hc : (Walk.cons w.property (q : T.Walk w.val a)).IsPath := q.property.cons hq
    have heq : treePath T hT v a = Walk.cons w.property (q : T.Walk w.val a) :=
      (hT.existsUnique_path v a).unique (treePath_isPath T hT v a) hc
    apply Subtype.ext
    change (treePath T hT v a).snd = w.val
    rw [heq]
    simp [Walk.snd, Walk.getVert]

/-- A walk avoiding v is exactly reachability in the graph with v deleted. -/
theorem avoiding_iff_deleted_reachable (v a b : V) (ha : a ≠ v) (hb : b ≠ v) :
    (∃ p : T.Walk a b, v ∉ p.support) ↔
      (T.induce {x | x ≠ v}).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
  classical
  constructor
  · rintro ⟨p, hp⟩
    have hs : {x | x ∈ p.support} ⊆ {x | x ≠ v} := by
      intro x hx hxeq
      exact hp (hxeq ▸ hx)
    have hr := p.connected_induce_support
      ⟨a, p.start_mem_support⟩ ⟨b, p.end_mem_support⟩
    exact hr.map (T.induceHomOfLE hs).toHom
  · rintro ⟨p⟩
    let q := p.map (SimpleGraph.Embedding.induce {x | x ≠ v}).toHom
    refine ⟨q, ?_⟩
    simp only [q, Walk.support_map, List.mem_map]
    rintro ⟨x, _, hx⟩
    exact x.property hx

/-- Exact connected-component characterization of the routing function. -/
theorem firstNeighbor_eq_iff_deleted_reachable (hT : T.IsTree)
    (v a : V) (ha : a ≠ v) (w : T.neighborSet v) :
    firstNeighbor T hT v a ha = w ↔
      (T.induce {x | x ≠ v}).Reachable
        ⟨w.val, w.property.ne.symm⟩ ⟨a, ha⟩ := by
  rw [firstNeighbor_eq_iff_avoiding]
  exact avoiding_iff_deleted_reachable T v w.val a w.property.ne.symm ha

/-- Edges are assigned to the component of an endpoint away from v. This
is the branch of its midpoint after deleting v, as in Definition 2.2. -/
theorem treeBranch_eq_iff_deleted_reachable (hT : T.IsTree) (v : V)
    (e : T.edgeSet) (w : T.neighborSet v) :
    treeBranch T hT v e = w ↔
      (T.induce {x | x ≠ v}).Reachable
        ⟨w.val, w.property.ne.symm⟩
        ⟨(edgeTarget T v e).val, (edgeTarget T v e).property.2⟩ :=
  firstNeighbor_eq_iff_deleted_reachable T hT v _ _ w

/-- If two endpoints of an edge survive vertex deletion, they lie in the
same component. Thus the branch does not depend on the endpoint choice. -/
theorem deleted_adj_reachable (v a b : V) (hab : T.Adj a b)
    (ha : a ≠ v) (hb : b ≠ v) :
    (T.induce {x | x ≠ v}).Reachable ⟨a, ha⟩ ⟨b, hb⟩ :=
  SimpleGraph.Adj.reachable hab

/-- Endpoint independence in the actual unique-path routing. -/
theorem firstNeighbor_adj (hT : T.IsTree) (v a b : V)
    (hab : T.Adj a b) (ha : a ≠ v) (hb : b ≠ v) :
    firstNeighbor T hT v a ha = firstNeighbor T hT v b hb := by
  let w := firstNeighbor T hT v a ha
  have hwa := (firstNeighbor_eq_iff_deleted_reachable T hT v a ha w).mp rfl
  have hwb := hwa.trans (deleted_adj_reachable T v a b hab ha hb)
  exact ((firstNeighbor_eq_iff_deleted_reachable T hT v b hb w).mpr hwb).symm

/-- Every surviving endpoint gives the same branch, including an edge
incident with v (where the other endpoint is the only surviving one). -/
theorem treeBranch_eq_firstNeighbor_endpoint (hT : T.IsTree) (v : V)
    (e : T.edgeSet) (a : V) (hae : a ∈ e.val) (ha : a ≠ v) :
    treeBranch T hT v e = firstNeighbor T hT v a ha := by
  classical
  change firstNeighbor T hT v (edgeTarget T v e).val (edgeTarget T v e).property.2 = _
  by_cases h : (edgeTarget T v e).val = a
  · apply Subtype.ext
    change (treePath T hT v (edgeTarget T v e).val).snd = (treePath T hT v a).snd
    rw [h]
  · have hadj : T.Adj (edgeTarget T v e).val a :=
      T.adj_of_mem_incidenceSet h
        ⟨e.property, (edgeTarget T v e).property.1⟩ ⟨e.property, hae⟩
    exact firstNeighbor_adj T hT v _ a hadj (edgeTarget T v e).property.2 ha

/-- The branch formula (5) may therefore use any endpoint of an edge
other than the deleted vertex. It is exactly its component after deletion. -/
theorem treeBranch_endpoint_component (hT : T.IsTree) (v : V)
    (e : T.edgeSet) (a : V) (hae : a ∈ e.val) (ha : a ≠ v) (w : T.neighborSet v) :
    treeBranch T hT v e = w ↔
      (T.induce {x | x ≠ v}).Reachable ⟨w.val, w.property.ne.symm⟩ ⟨a, ha⟩ := by
  rw [treeBranch_eq_firstNeighbor_endpoint T hT v e a hae ha]
  exact firstNeighbor_eq_iff_deleted_reachable T hT v a ha w

variable [Fintype V] [DecidableEq V] [DecidableRel T.Adj]

/-- The actual incident edge, rather than its neighbor index. -/
def treeBranchEdge (hT : T.IsTree) (v : V) (a : T.edgeSet) : T.incidenceSet v :=
  (T.incidenceSetEquivNeighborSet v).symm (treeBranch T hT v a)

theorem treeBranchEdge_eq_iff (hT : T.IsTree) (v : V) (a : T.edgeSet)
    (e : T.incidenceSet v) :
    treeBranchEdge T hT v a = e ↔
      treeBranch T hT v a = T.incidenceSetEquivNeighborSet v e := by
  exact (T.incidenceSetEquivNeighborSet v).symm_apply_eq

/-- The finite shadow with exactly the incident-edge codomain in (5). -/
def vertexShadowOnEdges (hT : T.IsTree) (v : V)
    (u : EuclideanSpace ℝ T.edgeSet) : EuclideanSpace ℝ (T.incidenceSet v) :=
  finiteShadow (treeBranchEdge T hT v) u

theorem vertexShadowOnEdges_formula (hT : T.IsTree) (v : V)
    (u : EuclideanSpace ℝ T.edgeSet) (e : T.incidenceSet v) :
    vertexShadowOnEdges T hT v u e = Real.sqrt
      (∑ a ∈ Finset.univ.filter (fun a => treeBranchEdge T hT v a = e), u a ^ 2) := rfl

/-- The summation fibers in (5) are exactly the vertex-deleted components,
for either endpoint of the edge midpoint other than the deleted vertex. -/
theorem vertexShadow_branch_component (hT : T.IsTree) (v : V)
    (a : T.edgeSet) (x : V) (hxa : x ∈ a.val) (hx : x ≠ v) (e : T.incidenceSet v) :
    treeBranchEdge T hT v a = e ↔
      (T.induce {y | y ≠ v}).Reachable
        ⟨(T.incidenceSetEquivNeighborSet v e).val,
          (T.incidenceSetEquivNeighborSet v e).property.ne.symm⟩ ⟨x, hx⟩ := by
  rw [treeBranchEdge_eq_iff]
  exact treeBranch_endpoint_component T hT v a x hxa hx _

theorem vertexShadowOnEdges_norm (hT : T.IsTree) (v : V)
    (u : EuclideanSpace ℝ T.edgeSet) : ‖vertexShadowOnEdges T hT v u‖ = ‖u‖ :=
  finiteShadow_norm _ _

theorem vertexShadowOnEdges_angular (hT : T.IsTree) (v : V)
    (u w : EuclideanSpace ℝ T.edgeSet) :
    angular (vertexShadowOnEdges T hT v u) (vertexShadowOnEdges T hT v w) ≤ angular u w :=
  finiteShadow_angular _ _ _

/-- Definition 2.2 as a map of the actual unit spheres. -/
def sphereVertexShadow (hT : T.IsTree) (v : V)
    (u : {u : EuclideanSpace ℝ T.edgeSet // ‖u‖ = 1}) :
    {w : EuclideanSpace ℝ (T.incidenceSet v) // ‖w‖ = 1} :=
  ⟨vertexShadowOnEdges T hT v u.val, (vertexShadowOnEdges_norm T hT v u.val).trans u.property⟩

end Paper28
