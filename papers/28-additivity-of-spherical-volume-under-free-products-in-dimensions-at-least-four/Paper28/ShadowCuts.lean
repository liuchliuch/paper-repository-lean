import Paper28.EdgeCollapse
import Paper28.ShadowComposition

/-! Exact factorization of the actual vertex shadows through an edge-cut
norm folding, with the canonical correspondence of incident branches. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open SimpleGraph
attribute [local instance] Classical.propDecidable

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- Folding along a bijection only takes coordinatewise absolute values. -/
theorem finiteShadow_equiv_apply (e : ι ≃ κ) (u : EuclideanSpace ℝ ι) (b : ι) :
    finiteShadow e u (e b) = |u b| := by
  have hf : Finset.univ.filter (fun i => e i = e b) = {b} := by
    ext i
    simp
  change Real.sqrt (∑ i ∈ Finset.univ.filter (fun i => e i = e b), u i ^ 2) = _
  rw [hf, Finset.sum_singleton, Real.sqrt_sq_eq_abs]

variable {V : Type*} [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj]

/-- The whole shadow map factors through the cut partition. Its output
branches are identified by the actual retained-neighbor equivalence. -/
theorem vertexShadow_cut_factorization (hT : T.IsTree) (v w : V) (hvw : T.Adj v w)
    (x : V) (hx : x ∈ cutSide T v w) (u : EuclideanSpace ℝ T.edgeSet) :
    finiteShadow (retainedNeighborEquiv T hT v w hvw x hx)
      (vertexShadow (retainedTree T v w) (retainedTree_isTree T hT v w hvw)
        ⟨x, Or.inl hx⟩ (finiteShadow (collapseEdge T v w hvw) u)) =
      vertexShadow T hT x u := by
  unfold vertexShadow
  rw [finiteShadow_comp, finiteShadow_comp]
  congr 1
  funext e
  exact (treeBranch_collapse T hT v w hvw x hx e).symm

/-- Coordinate form of the factorization, with no extra absolute value
because every branch norm is nonnegative. -/
theorem vertexShadow_cut_apply (hT : T.IsTree) (v w : V) (hvw : T.Adj v w)
    (x : V) (hx : x ∈ cutSide T v w) (u : EuclideanSpace ℝ T.edgeSet)
    (b : (retainedTree T v w).neighborSet ⟨x, Or.inl hx⟩) :
    vertexShadow T hT x u (retainedNeighborEquiv T hT v w hvw x hx b) =
      vertexShadow (retainedTree T v w) (retainedTree_isTree T hT v w hvw)
        ⟨x, Or.inl hx⟩ (finiteShadow (collapseEdge T v w hvw) u) b := by
  rw [← vertexShadow_cut_factorization T hT v w hvw x hx u]
  let E := retainedNeighborEquiv T hT v w hvw x hx
  let z := vertexShadow (retainedTree T v w) (retainedTree_isTree T hT v w hvw)
    ⟨x, Or.inl hx⟩ (finiteShadow (collapseEdge T v w hvw) u)
  change finiteShadow E z (E b) = z b
  have hz : 0 ≤ z b := finiteShadow_nonneg
    (treeBranch (retainedTree T v w) (retainedTree_isTree T hT v w hvw) ⟨x, Or.inl hx⟩)
    (finiteShadow (collapseEdge T v w hvw) u) b
  exact (finiteShadow_equiv_apply E z b).trans (abs_of_nonneg hz)

end Paper28
