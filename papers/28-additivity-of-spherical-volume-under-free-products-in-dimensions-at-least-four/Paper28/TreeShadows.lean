import Paper28.FiniteShadows
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Vertex shadows on the actual finite undirected edge set of a tree.
Incident edges at a vertex are indexed by their other endpoint. A branch is
routed by the unique simple path toward an endpoint different from the vertex.
This constructs Definition 2.2; it does not prove Lemma 2.3. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open SimpleGraph

variable {V : Type*} (T : SimpleGraph V)

/-- An endpoint of an edge different from a prescribed vertex. -/
def edgeTarget (v : V) (e : T.edgeSet) : {w : V // w ∈ e.val ∧ w ≠ v} := by
  classical
  by_cases h : v ∈ e.val
  · exact ⟨Sym2.Mem.other h, Sym2.other_mem h, T.edge_other_ne e.property h⟩
  · exact ⟨e.val.out.1, Sym2.out_fst_mem _, fun heq => h (heq ▸ Sym2.out_fst_mem _)⟩

/-- The unique simple path of a tree. -/
def treePath (hT : T.IsTree) (v w : V) : T.Walk v w :=
  Classical.choose (hT.existsUnique_path v w).exists

theorem treePath_isPath (hT : T.IsTree) (v w : V) :
    (treePath T hT v w).IsPath :=
  Classical.choose_spec (hT.existsUnique_path v w).exists

/-- The incident edge leading toward an edge midpoint, identified with its
other endpoint. The endpoint belongs to the prescribed edge and is not v. -/
def treeBranch (hT : T.IsTree) (v : V) (e : T.edgeSet) : T.neighborSet v :=
  let p := treePath T hT v (edgeTarget T v e).val
  ⟨p.snd, SimpleGraph.Walk.adj_snd
    (SimpleGraph.Walk.not_nil_of_ne (edgeTarget T v e).property.2.symm)⟩

/-- At an edge incident with v, routing chooses that same incident edge. -/
theorem treeBranch_incident (hT : T.IsTree) (v w : V) (hvw : T.Adj v w) :
    (treeBranch T hT v ⟨s(v, w), hvw⟩).val = w := by
  have ht : (edgeTarget T v ⟨s(v, w), hvw⟩).val = w := by
    have hm := (edgeTarget T v ⟨s(v, w), hvw⟩).property
    exact (Sym2.mem_iff.mp hm.1).resolve_left hm.2
  have hp : treePath T hT v w = SimpleGraph.Walk.cons hvw SimpleGraph.Walk.nil := by
    apply (hT.existsUnique_path v w).unique (treePath_isPath T hT v w)
    exact SimpleGraph.Walk.IsPath.nil.cons (by simpa using hvw.ne)
  change (treePath T hT v (edgeTarget T v ⟨s(v, w), hvw⟩).val).snd = w
  rw [ht, hp]
  rfl

variable [Fintype V] [DecidableEq V] [DecidableRel T.Adj]

/-- Definition 2.2, with incident edges canonically indexed by neighbors. -/
def vertexShadow (hT : T.IsTree) (v : V) :
    EuclideanSpace ℝ T.edgeSet → EuclideanSpace ℝ (T.neighborSet v) :=
  finiteShadow (treeBranch T hT v)

theorem vertexShadow_formula (hT : T.IsTree) (v : V)
    (u : EuclideanSpace ℝ T.edgeSet) (e : T.neighborSet v) :
    vertexShadow T hT v u e = Real.sqrt
      (∑ a ∈ Finset.univ.filter (fun a => treeBranch T hT v a = e), u a ^ 2) := rfl

theorem vertexShadow_norm (hT : T.IsTree) (v : V) (u : EuclideanSpace ℝ T.edgeSet) :
    ‖vertexShadow T hT v u‖ = ‖u‖ := finiteShadow_norm _ _

theorem vertexShadow_angular (hT : T.IsTree) (v : V) (u w : EuclideanSpace ℝ T.edgeSet) :
    angular (vertexShadow T hT v u) (vertexShadow T hT v w) ≤ angular u w :=
  finiteShadow_angular _ _ _

end Paper28
