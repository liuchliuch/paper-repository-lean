import Paper28.CutFibers
import Paper28.SplitRight

/-! The partitions of the actual original edge set commute with the native
cut-coordinate equivalences and the two complementary standard partitions. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} (T : SimpleGraph V)

theorem cutEdge_swap (v w : V) (hvw : T.Adj v w) :
    cutEdge T w v hvw.symm = cutEdge T v w hvw := by
  apply Subtype.ext
  exact Sym2.eq_swap

def rightLeftStrictEquiv (hT : T.IsTree) (v w : V) (hvw : T.Adj v w) :
    rightStrictEdges T v w hvw ≃ leftStrictEdges T w v hvw.symm where
  toFun e := ⟨e.val, by
    constructor
    · simpa only [cutEdge_swap T v w hvw] using e.property.1
    · exact (cut_sides_cover T hT.isConnected v w e.val.val.out.1).resolve_left e.property.2⟩
  invFun e := ⟨e.val, by
    constructor
    · simpa only [cutEdge_swap T v w hvw] using e.property.1
    · exact fun h => Set.disjoint_left.mp (cut_sides_disjoint T hT v w hvw) h e.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def rightRetainedCoordinateEquiv (hT : T.IsTree) (v w : V) (hvw : T.Adj v w) :
    rightStrictEdges T v w hvw ⊕ Unit ≃ (retainedTree T w v).edgeSet :=
  (Equiv.sumCongr (rightLeftStrictEquiv T hT v w hvw) (Equiv.refl Unit)).trans
    (retainedCoordinateEquiv T hT w v hvw.symm)

theorem cutPartition_left_route (hT : T.IsTree) (v w : V) (hvw : T.Adj v w)
    (j : leftStrictEdges T v w hvw ⊕ (Unit ⊕ rightStrictEdges T v w hvw)) :
    collapseEdge T v w hvw (cutCoordinateEquiv T v w hvw j) =
      retainedCoordinateEquiv T hT v w hvw (splitLeft j) := by
  rcases j with a | j
  · rfl
  · rcases j with z | b
    · cases z
      exact collapseEdge_cut T v w hvw
    · exact collapseEdge_rightStrict T hT v w hvw b

theorem cutPartition_right_route (hT : T.IsTree) (v w : V) (hvw : T.Adj v w)
    (j : leftStrictEdges T v w hvw ⊕ (Unit ⊕ rightStrictEdges T v w hvw)) :
    collapseEdge T w v hvw.symm (cutCoordinateEquiv T v w hvw j) =
      rightRetainedCoordinateEquiv T hT v w hvw (splitRight j) := by
  rcases j with a | j
  · have ha : a.val ∈ rightStrictEdges T w v hvw.symm := by
      constructor
      · simpa only [cutEdge_swap T v w hvw] using a.property.1
      · exact fun h => Set.disjoint_left.mp (cut_sides_disjoint T hT v w hvw) a.property.2 h
    exact collapseEdge_rightStrict T hT w v hvw.symm ⟨a.val, ha⟩
  · rcases j with z | b
    · cases z
      change collapseEdge T w v hvw.symm (cutEdge T v w hvw) = retainedCutEdge T w v hvw.symm
      rw [← cutEdge_swap T v w hvw]
      exact collapseEdge_cut T w v hvw.symm
    · rfl

end Paper28
