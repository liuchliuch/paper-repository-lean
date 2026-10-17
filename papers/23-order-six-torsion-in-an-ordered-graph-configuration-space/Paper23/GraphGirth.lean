import Paper23.GraphConnectivity
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Tactic.NormNum

/-! The actual subdivided graph has conventional simple-graph girth six.
The finite certificate enumerates only simple paths along its edge list. -/
namespace Paper23.GraphGirth
open Cubical GraphConnectivity

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Forget edge orientations, retaining the actual finite endpoint adjacency. -/
def graph : SimpleGraph Vertex where
  Adj := Adjacent
  symm := adjacent_symmetric
  loopless := by
    intro v h
    rcases h with ⟨e, h | h⟩ <;>
      exact GraphStructure.subdivision_no_loops e (by rw [h])

instance : DecidableRel graph.Adj := fun u v =>
  inferInstanceAs (Decidable (Adjacent u v))

/-- Neighbors generated directly from the thirty-nine subdivided edges. -/
def generatedNeighbors (v : Vertex) : List Vertex :=
  (List.finRange 39).flatMap fun e =>
    if (endpoints e).1 = v then [(endpoints e).2]
    else if (endpoints e).2 = v then [(endpoints e).1] else []

/-- A cached adjacency table, checked against the edge-list generator. -/
def neighbors : Vertex → List Vertex := ![
  [6,8,10,12,14],
  [7,9,11,16,18],
  [13,20,22,24],
  [15,21,26,28],
  [17,23,27,30],
  [19,25,29,31],
  [0,7],
  [6,1],
  [0,9],
  [8,1],
  [0,11],
  [10,1],
  [0,13],
  [12,2],
  [0,15],
  [14,3],
  [1,17],
  [16,4],
  [1,19],
  [18,5],
  [2,21],
  [20,3],
  [2,23],
  [22,4],
  [2,25],
  [24,5],
  [3,27],
  [26,4],
  [3,29],
  [28,5],
  [4,31],
  [30,5]]

theorem neighbors_generated : ∀ v, neighbors v = generatedNeighbors v := by decide

theorem mem_generatedNeighbors (u v : Vertex) :
    v ∈ generatedNeighbors u ↔ Adjacent u v := by
  simp only [generatedNeighbors, List.mem_flatMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨e, hmem⟩
    by_cases hs : (endpoints e).1 = u
    · have hv : v = (endpoints e).2 := by simpa only [if_pos hs, List.mem_singleton] using hmem
      exact ⟨e, Or.inl (Prod.ext hs hv.symm)⟩
    · by_cases ht : (endpoints e).2 = u
      · have hv : v = (endpoints e).1 := by
          simpa only [if_neg hs, if_pos ht, List.mem_singleton] using hmem
        exact ⟨e, Or.inr (Prod.ext hv.symm ht)⟩
      · simp only [if_neg hs, if_neg ht, List.not_mem_nil] at hmem
  · rintro ⟨e, h | h⟩ <;> refine ⟨e, ?_⟩
    · simp [h]
    · by_cases hne : v = u
      · subst v; simp [h]
      · simp [h, hne]

theorem mem_neighbors (u v : Vertex) : v ∈ neighbors u ↔ graph.Adj u v := by
  rw [neighbors_generated]
  exact mem_generatedNeighbors u v

theorem neighbors_nodup : ∀ v, (neighbors v).Nodup := by decide

theorem neighbors_length : ∀ v, (neighbors v).length =
    if v.val < 2 then 5 else if v.val < 6 then 4 else 2 := by decide

/-- Finite neighbor sets use the computable adjacency decision procedure. -/
instance neighborFintype (v : Vertex) : Fintype (graph.neighborSet v) :=
  inferInstanceAs (Fintype {w : Vertex // graph.Adj v w})

/-- The conventional graph degree agrees with the edge-list incidence degree. -/
theorem degree_eq_incidence (v : Vertex) : graph.degree v = GraphStructure.vertexDegree v := by
  have hset : graph.neighborFinset v = (neighbors v).toFinset := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, List.mem_toFinset, mem_neighbors]
  rw [SimpleGraph.degree, hset, List.toFinset_card_of_nodup (neighbors_nodup v),
    neighbors_length, GraphStructure.vertexDegree_formula]

theorem degree_ne_two_iff (v : Vertex) : graph.degree v ≠ 2 ↔ v.val < 6 := by
  rw [degree_eq_incidence, GraphStructure.special_vertices]

/-- A complete neighbor-based enumeration of simple paths of `n` edges.
Filtering all previously visited vertices in particular forbids backtracking. -/
def simplePaths (n : ℕ) : Vertex → List (List Vertex) :=
  Nat.rec (fun u => [[u]])
    (fun _ rec u => (neighbors u).flatMap fun v =>
      ((rec v).filter fun xs => decide (u ∉ xs)).map (u :: ·)) n

/-- Every ordinary simple-graph path is included in the finite enumeration. -/
theorem support_mem_simplePaths {u v : Vertex} (p : graph.Walk u v)
    (hp : p.support.Nodup) : p.support ∈ simplePaths p.length u := by
  induction p with
  | nil => simp [simplePaths]
  | @cons u v w h p ih =>
    rw [SimpleGraph.Walk.support_cons] at hp ⊢
    have hn := List.nodup_cons.mp hp
    simp only [SimpleGraph.Walk.length_cons, simplePaths, List.mem_flatMap]
    refine ⟨v, (mem_neighbors u v).2 h, ?_⟩
    apply List.mem_map.mpr
    refine ⟨p.support, List.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
    · exact ih hn.2
    · simpa only [decide_eq_true_eq] using hn.1

/-- A path can close to its start only if its last vertex is adjacent to it. -/
def noClosureTest (n : ℕ) (u : Vertex) : Bool :=
  (simplePaths n u).all fun xs => decide (¬graph.Adj (xs.getLastD u) u)

/-- Exhaustion of simple paths of two, three and four edges rules out cycles
of lengths three, four and five.  This uses Lean's kernel reduction. -/
theorem no_short_closure_checked : ∀ u : Vertex, ∀ n : Fin 3,
    noClosureTest (n.val + 2) u = true := by decide

/-- Soundness of the finite no-closure certificate. -/
theorem no_short_closure (u : Vertex) (n : Fin 3) (xs : List Vertex)
    (hxs : xs ∈ simplePaths (n.val + 2) u) : ¬graph.Adj (xs.getLastD u) u := by
  have h := List.all_eq_true.mp (no_short_closure_checked u n) xs hxs
  exact of_decide_eq_true h

@[simp] theorem lastD_support {u v : Vertex} (p : graph.Walk u v) :
    p.support.getLastD u = v := by
  rw [p.support_eq_concat, List.concat_eq_append, List.getLastD_concat]

/-- The finite checked certificate bounds every conventional cycle, with no
restriction to the cycles or vertices used by the displayed six-cycle. -/
theorem cycle_length_ge_six {u : Vertex} (p : graph.Walk u u) (hp : p.IsCycle) :
    6 ≤ p.length := by
  by_contra hn
  have hthree := hp.three_le_length
  have hlength := SimpleGraph.Walk.length_tail_add_one hp.not_nil
  have hnodup : p.tail.support.Nodup := by
    rw [SimpleGraph.Walk.support_tail p hp.not_nil]
    exact hp.support_nodup
  let n : Fin 3 := ⟨p.tail.length - 2, by omega⟩
  have hnval : n.val + 2 = p.tail.length := by dsimp [n]; omega
  have hmem := support_mem_simplePaths p.tail hnodup
  have hclose := no_short_closure p.snd n p.tail.support (by simpa only [hnval] using hmem)
  rw [lastD_support] at hclose
  exact hclose (p.adj_snd hp.not_nil)

/-- Two different subdivided parallel a-b edges form this six-cycle. -/
def sixCycle : graph.Walk 0 0 :=
  .cons (v := 6) (by decide) (.cons (v := 7) (by decide) (.cons (v := 1) (by decide)
    (.cons (v := 9) (by decide) (.cons (v := 8) (by decide) (.cons (v := 0) (by decide) .nil)))))

@[simp] theorem sixCycle_length : sixCycle.length = 6 := rfl

theorem sixCycle_isCycle : sixCycle.IsCycle := by
  rw [SimpleGraph.Walk.isCycle_def, SimpleGraph.Walk.isTrail_def]
  decide

theorem egirth_eq_six : graph.egirth = 6 := by
  apply le_antisymm
  · simpa only [sixCycle_length, Nat.cast_ofNat] using
      SimpleGraph.egirth_le_length sixCycle_isCycle
  · apply SimpleGraph.le_egirth.mpr
    intro u p hp
    exact_mod_cast cycle_length_ge_six p hp

theorem girth_eq_six : graph.girth = 6 := by
  rw [SimpleGraph.girth, egirth_eq_six]
  rfl

/-- The paper's finite graph is connected in the standard graph API. -/
theorem connected : graph.Connected := by
  constructor
  intro u v
  exact (graph.reachable_iff_reflTransGen u v).2 (GraphConnectivity.connected u v)

/-- Every walk (hence every path) between distinct vertices of degree other
than two has at least three edges. -/
theorem special_walk_length {u v : Vertex} (hu : graph.degree u ≠ 2)
    (hv : graph.degree v ≠ 2) (hne : u ≠ v) (p : graph.Walk u v) : 3 ≤ p.length := by
  have hu6 := (degree_ne_two_iff u).1 hu
  have hv6 := (degree_ne_two_iff v).1 hv
  let u' : CoreVertex := ⟨u.val, hu6⟩
  let v' : CoreVertex := ⟨v.val, hv6⟩
  have hne' : u' ≠ v' := by
    intro h
    have hval : u.val = v.val := congrArg (fun w : CoreVertex => w.val) h
    exact hne (Fin.ext hval)
  by_contra hn
  have hc : p.length = 0 ∨ p.length = 1 ∨ p.length = 2 := by omega
  rcases hc with h0 | h1 | h2
  · exact hne (p.eq_of_length_eq_zero h0)
  · exact no_short_special_edge u' v' (p.adj_of_length_eq_one h1)
  · have hfirst := p.adj_getVert_succ (i := 0) (by omega)
    have hlast := p.adj_getVert_succ (i := 1) (by omega)
    have hend : p.getVert 2 = v := by simpa only [h2] using p.getVert_length
    apply no_short_special_two_edges u' v' hne' (p.getVert 1)
    constructor
    · simpa only [p.getVert_zero, zero_add] using hfirst
    · simpa only [hend] using hlast

/-- The sharp three-edge path joining the two original a-b vertices. -/
def specialThreeWalk : graph.Walk 0 1 :=
  .cons (v := 6) (by decide) (.cons (v := 7) (by decide) (.cons (v := 1) (by decide) .nil))

theorem specialThreeWalk_isPath : specialThreeWalk.IsPath := by
  rw [SimpleGraph.Walk.isPath_def]
  decide

@[simp] theorem specialThreeWalk_length : specialThreeWalk.length = 3 := rfl

/-- Combined with `special_walk_length`, the minimum special-vertex path
length is exactly three, as asserted in §2 paragraph 2. -/
theorem shortest_special_path : ∃ u v : Vertex,
    u ≠ v ∧ graph.degree u ≠ 2 ∧ graph.degree v ≠ 2 ∧
      ∃ p : graph.Walk u v, p.IsPath ∧ p.length = 3 := by
  refine ⟨0, 1, by decide, ?_, ?_, specialThreeWalk, specialThreeWalk_isPath, rfl⟩
  all_goals rw [degree_ne_two_iff]; decide

/-- The exact hypotheses needed for the four-particle stable-equivalence
application, stated using standard graph paths and cycles. -/
structure FourParticleConditions : Prop where
  finite_vertices : 4 ≤ Fintype.card Vertex
  connected : graph.Connected
  special_paths : ∀ {u v : Vertex}, graph.degree u ≠ 2 → graph.degree v ≠ 2 → u ≠ v →
    ∀ p : graph.Walk u v, 3 ≤ p.length
  cycles : ∀ {u : Vertex} (p : graph.Walk u u), p.IsCycle → 5 ≤ p.length

/-- All graph-specific hypotheses are proved here, rather than supplied by
an external discretization theorem or by the torsion certificate. -/
theorem fourParticleConditions : FourParticleConditions := by
  refine ⟨by decide, connected, special_walk_length, ?_⟩
  intro u p hp
  have := cycle_length_ge_six p hp
  omega

end Paper23.GraphGirth
