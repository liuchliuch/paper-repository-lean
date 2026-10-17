import Paper28.CutCoordinates

/-! Exact fibers of the actual edge-cut partition. A surviving nonterminal
coordinate has a singleton fiber; all discarded coordinates enter the terminal. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} (T : SimpleGraph V)

theorem collapseEdge_survives (v w : V) (hvw : T.Adj v w) (e : T.edgeSet)
    (h : ∃ d, (retainedEmbedding T v w).mapEdgeSet d = e) :
    (retainedEmbedding T v w).mapEdgeSet (collapseEdge T v w hvw e) = e := by
  unfold collapseEdge
  rw [dif_pos h]
  exact h.choose_spec

theorem collapseEdge_cut (v w : V) (hvw : T.Adj v w) :
    collapseEdge T v w hvw (cutEdge T v w hvw) = retainedCutEdge T v w hvw :=
  collapseEdge_map T v w hvw (retainedCutEdge T v w hvw)

/-- A surviving noncut edge is strictly on the left. -/
theorem surviving_noncut_is_left (hT : T.IsTree) (v w : V) (hvw : T.Adj v w)
    (d : (retainedTree T v w).edgeSet)
    (hne : (retainedEmbedding T v w).mapEdgeSet d ≠ cutEdge T v w hvw) :
    ((retainedEmbedding T v w).mapEdgeSet d).val.out.1 ∈ cutSide T v w := by
  let w' : retainedSide T v w := ⟨w, Or.inr rfl⟩
  let a := edgeTarget (retainedTree T v w) w' d
  have haL : a.val.val ∈ cutSide T v w :=
    a.val.property.resolve_right (fun h => a.property.2 (Subtype.ext h))
  have ha : a.val.val ∈ ((retainedEmbedding T v w).mapEdgeSet d).val :=
    Sym2.mem_map.mpr ⟨a.val, a.property.1, rfl⟩
  exact noncut_endpoint_same_side T hT v w hvw _ hne a.val.val _ ha
    (Sym2.out_fst_mem _) haL

/-- No strict right edge survives in the retained left subtree. -/
theorem rightStrict_not_surviving (hT : T.IsTree) (v w : V) (hvw : T.Adj v w)
    (e : rightStrictEdges T v w hvw) :
    ¬ ∃ d, (retainedEmbedding T v w).mapEdgeSet d = e.val := by
  rintro ⟨d, hd⟩
  apply e.property.2
  rw [← hd]
  exact surviving_noncut_is_left T hT v w hvw d (fun h => e.property.1 (hd.symm.trans h))

theorem collapseEdge_rightStrict (hT : T.IsTree) (v w : V) (hvw : T.Adj v w)
    (e : rightStrictEdges T v w hvw) :
    collapseEdge T v w hvw e.val = retainedCutEdge T v w hvw := by
  unfold collapseEdge
  exact dif_neg (rightStrict_not_surviving T hT v w hvw e)

/-- A nonterminal retained coordinate has exactly its original edge as fiber. -/
theorem collapseEdge_left_fiber (hT : T.IsTree) (v w : V) (hvw : T.Adj v w)
    (a : leftStrictEdges T v w hvw) (e : T.edgeSet) :
    collapseEdge T v w hvw e = collapseEdge T v w hvw a.val ↔ e = a.val := by
  constructor
  · intro he
    have ha := collapseEdge_survives T v w hvw a.val (leftStrict_survives T hT v w hvw a)
    by_cases hs : ∃ d, (retainedEmbedding T v w).mapEdgeSet d = e
    · exact (collapseEdge_survives T v w hvw e hs).symm.trans
        ((congrArg (retainedEmbedding T v w).mapEdgeSet he).trans ha)
    · have hc : collapseEdge T v w hvw e = retainedCutEdge T v w hvw := by
        unfold collapseEdge
        exact dif_neg hs
      have hbad : cutEdge T v w hvw = a.val := by
        change (⟨s(v,w), hvw⟩ : T.edgeSet) = a.val
        rw [← retainedCutEdge_map T v w hvw, ← hc, he, ha]
      exact False.elim (a.property.1 hbad.symm)
  · rintro rfl
    rfl

/-- The left strict edges and one terminal coordinate index precisely the
edges of the actual retained tree. -/
def retainedCoordinateEquiv (hT : T.IsTree) (v w : V) (hvw : T.Adj v w) :
    leftStrictEdges T v w hvw ⊕ Unit ≃ (retainedTree T v w).edgeSet :=
  Equiv.ofBijective
    (Sum.elim (fun a => collapseEdge T v w hvw a.val) (fun _ => retainedCutEdge T v w hvw))
    ⟨by
      intro i j hij
      rcases i with a | z <;> rcases j with b | z'
      · apply congrArg Sum.inl
        apply Subtype.ext
        exact (collapseEdge_left_fiber T hT v w hvw b a.val).mp hij
      · have ha := collapseEdge_survives T v w hvw a.val (leftStrict_survives T hT v w hvw a)
        have hc := congrArg (retainedEmbedding T v w).mapEdgeSet hij
        exact False.elim (a.property.1 (ha.symm.trans hc))
      · have hb := collapseEdge_survives T v w hvw b.val (leftStrict_survives T hT v w hvw b)
        have hc := congrArg (retainedEmbedding T v w).mapEdgeSet hij
        exact False.elim (b.property.1 (hb.symm.trans hc.symm))
      · congr,
    by
      intro d
      let e := (retainedEmbedding T v w).mapEdgeSet d
      by_cases he : e = cutEdge T v w hvw
      · refine ⟨.inr (), ?_⟩
        exact (retainedEmbedding T v w).mapEdgeSet.injective he.symm
      · let a : leftStrictEdges T v w hvw :=
          ⟨e, he, surviving_noncut_is_left T hT v w hvw d he⟩
        exact ⟨.inl a, collapseEdge_map T v w hvw d⟩⟩

end Paper28
