import Paper23.Cubical

/-! Finite incidence facts used in the paper's graph description. -/
namespace Paper23.GraphStructure
open Cubical

/-- The left part `{a,y₁,y₂}` of the exhibited K₃,₃. -/
def leftVertex : Fin 3 → CoreVertex := ![0,4,5]
/-- The right part `{b,x₁,x₂}` of the exhibited K₃,₃. -/
def rightVertex : Fin 3 → CoreVertex := ![1,2,3]
/-- Nine distinct original edges, retaining just one of the parallel a-b edges. -/
def bipartiteEdge (i j : Fin 3) : CoreEdge :=
  (![![0,3,4], ![5,8,10], ![6,9,11]] : Fin 3 → Fin 3 → CoreEdge) i j

theorem left_injective : Function.Injective leftVertex := by decide
theorem right_injective : Function.Injective rightVertex := by decide
theorem parts_disjoint : ∀ i j, leftVertex i ≠ rightVertex j := by decide
theorem bipartiteEdge_injective_coordinates : ∀ i j k l : Fin 3,
    bipartiteEdge i j = bipartiteEdge k l → i = k ∧ j = l := by decide

theorem bipartiteEdge_injective : Function.Injective
    (fun p : Fin 3 × Fin 3 => bipartiteEdge p.1 p.2) := by
  rintro ⟨i,j⟩ ⟨k,l⟩ h
  obtain ⟨rfl,rfl⟩ := bipartiteEdge_injective_coordinates i j k l h
  rfl

/-- Every edge of the complete bipartite graph occurs, possibly reversed. -/
theorem bipartiteEdge_endpoints : ∀ i j,
    coreEndpoints (bipartiteEdge i j) = (leftVertex i, rightVertex j) ∨
    coreEndpoints (bipartiteEdge i j) = (rightVertex j, leftVertex i) := by decide

/-- Subdivide two of the three parallel edges once, as in §1 paragraph 7. -/
def simpleEndpoints : Fin 15 → Fin 8 × Fin 8 := ![
  (0,1), (0,6), (6,1), (0,7), (7,1),
  (0,2), (0,3), (1,4), (1,5),
  (2,3), (2,4), (2,5), (3,4), (3,5), (4,5)]

theorem simple_no_loops : ∀ e, (simpleEndpoints e).1 ≠ (simpleEndpoints e).2 := by
  decide

/-- Distinct edge indices of the simple presentation have distinct unordered endpoints. -/
theorem simple_no_parallel : ∀ e f,
    (simpleEndpoints e = simpleEndpoints f ∨
      simpleEndpoints e = ((simpleEndpoints f).2, (simpleEndpoints f).1)) → e = f := by
  decide

theorem core_no_loops : ∀ e, (coreEndpoints e).1 ≠ (coreEndpoints e).2 := by decide

theorem subdivision_no_loops : ∀ e, (endpoints e).1 ≠ (endpoints e).2 := by decide

theorem subdivision_no_parallel : ∀ e f,
    (endpoints e = endpoints f ∨ endpoints e = ((endpoints f).2, (endpoints f).1)) →
      e = f := by decide

/-- Valence in the thirty-nine-edge subdivided graph. -/
def vertexDegree (v : Vertex) : ℕ :=
  ((List.finRange 39).filter fun e =>
    (endpoints e).1 == v || (endpoints e).2 == v).length

theorem vertexDegree_formula : ∀ v : Vertex,
    vertexDegree v = if v.val < 2 then 5 else if v.val < 6 then 4 else 2 := by
  decide

/-- Exactly the original six vertices have degree different from two. -/
theorem special_vertices : ∀ v : Vertex, vertexDegree v ≠ 2 ↔ v.val < 6 := by
  intro v
  rw [vertexDegree_formula]
  split_ifs <;> omega

end Paper23.GraphStructure
