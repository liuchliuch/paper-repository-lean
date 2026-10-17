import SemidegreeExt.Main
open Finset Classical
namespace SemidegreeExt

/-- An arbitrary subdigraph: vertices can be deleted, and any remaining arcs
can independently be deleted. Its vertex type is the actual selected subtype. -/
structure Subdigraph {V : Type*} (G : Digraph V) where
  verts : Finset V
  graph : Digraph {v // v ∈ verts}
  adj_le : ∀ u v, graph.Adj u v → G.Adj u.val v.val

def inducedSubdigraph {V : Type*} (G : Digraph V) (S : Finset V) : Subdigraph G :=
  ⟨S, ⟨fun u v => G.Adj u.val v.val⟩, fun _ _ h => h⟩

lemma subdigraph_out_le {V : Type*} [Fintype V] {G : Digraph V}
    (H : Subdigraph G) (v : {v // v ∈ H.verts}) :
    outDeg H.graph v ≤ outDegOn G H.verts v.val := by
  classical
  unfold outDeg outDegOn
  apply card_le_card_of_injOn Subtype.val
  · intro u hu
    simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at hu
    exact mem_filter.mpr ⟨u.property, H.adj_le v u hu⟩
  · intro u _ w _ h
    exact Subtype.ext h

lemma subdigraph_in_le {V : Type*} [Fintype V] {G : Digraph V}
    (H : Subdigraph G) (v : {v // v ∈ H.verts}) :
    inDeg H.graph v ≤ inDegOn G H.verts v.val := by
  classical
  unfold inDeg inDegOn
  apply card_le_card_of_injOn Subtype.val
  · intro u hu
    simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at hu
    exact mem_filter.mpr ⟨u.property, H.adj_le u v hu⟩
  · intro u _ w _ h
    exact Subtype.ext h

lemma induced_out_eq {V : Type*} [Fintype V] (G : Digraph V) (S : Finset V)
    (v : {v // v ∈ S}) : outDeg (inducedSubdigraph G S).graph v = outDegOn G S v.val := by
  classical
  unfold outDeg outDegOn
  apply card_bij (fun u _ => u.val)
  · intro u hu
    exact mem_filter.mpr ⟨u.property, (mem_filter.mp hu).2⟩
  · intro u _ w _ h
    exact Subtype.ext h
  · intro u hu
    exact ⟨⟨u, (mem_filter.mp hu).1⟩, by simpa using (mem_filter.mp hu).2, rfl⟩

lemma induced_in_eq {V : Type*} [Fintype V] (G : Digraph V) (S : Finset V)
    (v : {v // v ∈ S}) : inDeg (inducedSubdigraph G S).graph v = inDegOn G S v.val := by
  classical
  unfold inDeg inDegOn
  apply card_bij (fun u _ => u.val)
  · intro u hu
    exact mem_filter.mpr ⟨u.property, (mem_filter.mp hu).2⟩
  · intro u _ w _ h
    exact Subtype.ext h
  · intro u hu
    exact ⟨⟨u, (mem_filter.mp hu).1⟩, by simpa using (mem_filter.mp hu).2, rfl⟩

/-- Completing any subdigraph to its induced graph preserves every lower
indegree/outdegree bound; conversely an induced graph is itself a subdigraph. -/
theorem extraction_subdigraph_iff_induced {V : Type*} [Fintype V]
    (G : Digraph V) (c : ℕ) :
    (∃ H : Subdigraph G, H.verts.Nonempty ∧
      ∀ v, c ≤ outDeg H.graph v ∧ c ≤ inDeg H.graph v) ↔
    (∃ S : Finset V, S.Nonempty ∧
      ∀ v ∈ S, c ≤ outDegOn G S v ∧ c ≤ inDegOn G S v) := by
  constructor
  · rintro ⟨H, hH, hd⟩
    refine ⟨H.verts, hH, fun v hv => ?_⟩
    exact ⟨(hd ⟨v,hv⟩).1.trans (subdigraph_out_le H ⟨v,hv⟩),
      (hd ⟨v,hv⟩).2.trans (subdigraph_in_le H ⟨v,hv⟩)⟩
  · rintro ⟨S, hS, hd⟩
    refine ⟨inducedSubdigraph G S, hS, fun v => ?_⟩
    rw [induced_out_eq, induced_in_eq]
    exact hd v.val v.property

/-- The induced-set convention equals quantification over every nonempty
subdigraph with arbitrary vertex and arc deletions. -/
theorem weaklyDegenerate_iff_all_subdigraphs {V : Type*} [Fintype V]
    (G : Digraph V) (k : ℕ) :
    WeaklyDegenerate G k ↔ ∀ H : Subdigraph G, H.verts.Nonempty →
      ∃ v, outDeg H.graph v < k ∨ inDeg H.graph v < k := by
  constructor
  · intro hd H hH
    obtain ⟨v, hv, hlow⟩ := hd H.verts hH
    refine ⟨⟨v,hv⟩, ?_⟩
    exact hlow.imp (fun h => (subdigraph_out_le H ⟨v,hv⟩).trans_lt h)
      (fun h => (subdigraph_in_le H ⟨v,hv⟩).trans_lt h)
  · intro hd S hS
    obtain ⟨v, hv⟩ := hd (inducedSubdigraph G S) hS
    refine ⟨v.val, v.property, ?_⟩
    rwa [induced_out_eq, induced_in_eq] at hv

/-- Section 4's equivalence with the arbitrary-subdigraph definition of weak degeneracy. -/
theorem q_le_iff_all_subdigraphs {V : Type*} [Fintype V]
    (G : Digraph V) (c : ℕ) :
    q G ≤ c ↔ ∀ H : Subdigraph G, H.verts.Nonempty →
      ∃ v, outDeg H.graph v < c+1 ∨ inDeg H.graph v < c+1 := by
  rw [q_le_iff_weaklyDegenerate, weaklyDegenerate_iff_all_subdigraphs]
end SemidegreeExt
