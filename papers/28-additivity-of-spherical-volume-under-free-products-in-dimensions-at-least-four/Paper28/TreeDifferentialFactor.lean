import Paper28.ShadowDifferentialEquiv

/-! The actual branch differential on an original side factors through the
retained tree. Reindexing its output preserves the Gram form even at zero
branches. This is the analytic map identity needed by the tree induction. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open SimpleGraph
open scoped InnerProductSpace
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj]

/-- Equality of the actual derivative vectors after successive partitions. -/
theorem treeDifferential_cut_factorization (hT : T.IsTree) (v w : V) (hvw : T.Adj v w)
    (x : V) (hx : x ∈ cutSide T v w) (u h : EuclideanSpace ℝ T.edgeSet) :
    shadowDifferential (treeBranch T hT x) u h =
      shadowDifferential (retainedNeighborEquiv T hT v w hvw x hx)
        (vertexShadow (retainedTree T v w) (retainedTree_isTree T hT v w hvw)
          ⟨x, Or.inl hx⟩ (finiteShadow (collapseEdge T v w hvw) u))
        (shadowDifferential
          (treeBranch (retainedTree T v w) (retainedTree_isTree T hT v w hvw) ⟨x, Or.inl hx⟩)
          (finiteShadow (collapseEdge T v w hvw) u)
          (shadowDifferential (collapseEdge T v w hvw) u h)) := by
  unfold vertexShadow
  rw [shadowDifferential_comp, shadowDifferential_comp]
  have hf : treeBranch T hT x =
      ((retainedNeighborEquiv T hT v w hvw x hx) ∘
        treeBranch (retainedTree T v w) (retainedTree_isTree T hT v w hvw) ⟨x, Or.inl hx⟩) ∘
        collapseEdge T v w hvw := by
    funext e
    exact treeBranch_collapse T hT v w hvw x hx e
  rw [hf]

/-- Exact Gram identity on an original side, including all zero branches. -/
theorem treeDifferential_cut_inner (hT : T.IsTree) (v w : V) (hvw : T.Adj v w)
    (x : V) (hx : x ∈ cutSide T v w) (u h k : EuclideanSpace ℝ T.edgeSet) :
    ⟪shadowDifferential (treeBranch T hT x) u h,
      shadowDifferential (treeBranch T hT x) u k⟫_ℝ =
    ⟪shadowDifferential
        (treeBranch (retainedTree T v w) (retainedTree_isTree T hT v w hvw) ⟨x, Or.inl hx⟩)
        (finiteShadow (collapseEdge T v w hvw) u) (shadowDifferential (collapseEdge T v w hvw) u h),
      shadowDifferential
        (treeBranch (retainedTree T v w) (retainedTree_isTree T hT v w hvw) ⟨x, Or.inl hx⟩)
        (finiteShadow (collapseEdge T v w hvw) u) (shadowDifferential (collapseEdge T v w hvw) u k)⟫_ℝ := by
  rw [treeDifferential_cut_factorization T hT v w hvw x hx u h,
    treeDifferential_cut_factorization T hT v w hvw x hx u k]
  apply shadowDifferential_equiv_inner
  · intro b hb
    exact shadowDifferential_zero_coordinate
      (treeBranch (retainedTree T v w) (retainedTree_isTree T hT v w hvw) ⟨x, Or.inl hx⟩)
      (finiteShadow (collapseEdge T v w hvw) u) (shadowDifferential (collapseEdge T v w hvw) u h) b hb
  · intro b hb
    exact shadowDifferential_zero_coordinate
      (treeBranch (retainedTree T v w) (retainedTree_isTree T hT v w hvw) ⟨x, Or.inl hx⟩)
      (finiteShadow (collapseEdge T v w hvw) u) (shadowDifferential (collapseEdge T v w hvw) u k) b hb

end Paper28
