import Paper28.EdgeCollapse
import Paper28.CoordinateSplitting

/-! Native coordinate indexing for an actual cut edge. The distinguished
coordinate and the two strict sides are disjoint and exhaustive. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} (T : SimpleGraph V)

def cutEdge (v w : V) (hvw : T.Adj v w) : T.edgeSet := ⟨s(v,w), hvw⟩
def leftStrictEdges (v w : V) (hvw : T.Adj v w) : Set T.edgeSet :=
  {e | e ≠ cutEdge T v w hvw ∧ e.val.out.1 ∈ cutSide T v w}
def rightStrictEdges (v w : V) (hvw : T.Adj v w) : Set T.edgeSet :=
  {e | e ≠ cutEdge T v w hvw ∧ e.val.out.1 ∉ cutSide T v w}

/-- The actual original edges split into left strict edges, the cut edge,
and right strict edges, with no arbitrary graph or branch surrogate. -/
def cutCoordinateEquiv (v w : V) (hvw : T.Adj v w) :
    leftStrictEdges T v w hvw ⊕ (Unit ⊕ rightStrictEdges T v w hvw) ≃ T.edgeSet where
  toFun := Sum.elim Subtype.val (Sum.elim (fun _ => cutEdge T v w hvw) Subtype.val)
  invFun e := if he : e = cutEdge T v w hvw then .inr (.inl ())
    else if hL : e.val.out.1 ∈ cutSide T v w then .inl ⟨e, he, hL⟩
    else .inr (.inr ⟨e, he, hL⟩)
  left_inv j := by
    rcases j with a | j
    · simp only [Sum.elim_inl, dif_neg a.property.1, dif_pos a.property.2]
    · rcases j with z | b
      · cases z
        simp
      · simp only [Sum.elim_inr, dif_neg b.property.1, dif_neg b.property.2]
  right_inv e := by
    by_cases he : e = cutEdge T v w hvw
    · simp [he]
    · by_cases hL : e.val.out.1 ∈ cutSide T v w <;> simp [he, hL]

/-- A noncut edge cannot have endpoints on different sides. -/
theorem noncut_endpoint_same_side (hT : T.IsTree) (v w : V) (hvw : T.Adj v w)
    (e : T.edgeSet) (he : e ≠ cutEdge T v w hvw) (a b : V)
    (ha : a ∈ e.val) (hb : b ∈ e.val) (haL : a ∈ cutSide T v w) :
    b ∈ cutSide T v w := by
  classical
  rcases cut_sides_cover T hT.isConnected v w b with hbL | hbR
  · exact hbL
  · by_cases hab : a = b
    · exact hab ▸ haL
    · have hAdj : T.Adj a b := T.adj_of_mem_incidenceSet hab ⟨e.property, ha⟩ ⟨e.property, hb⟩
      have hcut := cross_edge_eq_cut T hT v w a b hvw haL hbR hAdj
      have heq : s(a,b) = e.val := Sym2.eq_of_ne_mem hab (by simp) (by simp) ha hb
      exact False.elim (he (Subtype.ext (heq.symm.trans hcut)))

/-- Every endpoint of a strict left edge lies strictly on the left. -/
theorem leftStrict_endpoint (hT : T.IsTree) (v w : V) (hvw : T.Adj v w)
    (e : leftStrictEdges T v w hvw) (a : V) (ha : a ∈ e.val.val) :
    a ∈ cutSide T v w :=
  noncut_endpoint_same_side T hT v w hvw e.val e.property.1 e.val.val.out.1 a
    (Sym2.out_fst_mem _) ha e.property.2

/-- Strict left coordinates are retained by the actual smaller tree. -/
theorem leftStrict_survives (hT : T.IsTree) (v w : V) (hvw : T.Adj v w)
    (e : leftStrictEdges T v w hvw) :
    ∃ d, (retainedEmbedding T v w).mapEdgeSet d = e.val :=
  edge_survives_of_left_endpoint T hT v w hvw e.val e.val.val.out.1
    (Sym2.out_fst_mem _) e.property.2

variable [Fintype V]

/-- The Hilbert decomposition associated to the actual edge cut. -/
def cutCoordinateIsometry (v w : V) (hvw : T.Adj v w) :
    EuclideanSpace ℝ T.edgeSet ≃ₗᵢ[ℝ]
      Triple (EuclideanSpace ℝ (leftStrictEdges T v w hvw))
        (EuclideanSpace ℝ (rightStrictEdges T v w hvw)) :=
  coordinateTriple (cutCoordinateEquiv T v w hvw)

end Paper28
