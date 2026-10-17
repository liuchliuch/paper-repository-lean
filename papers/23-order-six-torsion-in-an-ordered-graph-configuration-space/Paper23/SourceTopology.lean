import Paper23.Topology
import Paper23.Cubical

/-! The topological source objects for the explicit edge list of P23. -/
namespace Paper23

/-- The six-vertex, thirteen-edge multigraph in equation (1). -/
def coreGraph : GraphIncidence Cubical.CoreVertex Cubical.CoreEdge where
  source e := (Cubical.coreEndpoints e).1
  target e := (Cubical.coreEndpoints e).2

/-- The thirty-two-vertex, thirty-nine-edge subdivision of §2. -/
def subdividedGraph : GraphIncidence Cubical.Vertex Cubical.Edge where
  source e := (Cubical.endpoints e).1
  target e := (Cubical.endpoints e).2

/-- The certificate's two constructors select the corresponding topological cell. -/
def sourceCell : Cubical.GraphCell → subdividedGraph.Cell
  | .vertex v => Sum.inl v
  | .edge e => Sum.inr e

theorem sourceCell_vertices (c : Cubical.GraphCell) :
    subdividedGraph.cellVertices (sourceCell c) = (c.vertices : Set Cubical.Vertex) := by
  cases c <;> ext v <;>
    simp [sourceCell, GraphIncidence.cellVertices, Cubical.GraphCell.vertices, subdividedGraph]

/-- The finite endpoint disjointness test is geometrically exact for this graph. -/
theorem sourceCell_closedCarrier_disjoint_iff (c d : Cubical.GraphCell) :
    Disjoint (subdividedGraph.closedCarrier (sourceCell c))
      (subdividedGraph.closedCarrier (sourceCell d)) ↔ Cubical.ClosureDisjoint c d := by
  rw [GraphIncidence.closedCarrier_disjoint_iff, sourceCell_vertices, sourceCell_vertices]
  exact Finset.disjoint_coe

/-- The paper's original ordered configuration space `F₄(G)`. -/
abbrev SourceConfigurationSpace := OrderedConfiguration 4 coreGraph.Realization

/-- The discretized configuration space in §2, as an actual topological subspace. -/
abbrev DiscretizedSourceSpace := subdividedGraph.DiscretizedConfiguration 4

/-- The class asserted by Theorem 1 lives in this integral singular homology group. -/
noncomputable abbrev SourceHomology := IntegralHomology 2 SourceConfigurationSpace

/-- The original theorem's exact conclusion, not an axiom or a proof. -/
def MainTheoremStatement : Prop := ∃ z : SourceHomology, addOrderOf z = 6

end Paper23
