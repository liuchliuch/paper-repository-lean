import SemidegreeExt

/-!
Explicit paper-facing contracts. Statements are written independently of the
proof bodies and use the paper's graph minimum and liminf definitions. The
trusted challenge uses the already proved results as witnesses, so even the
specification module contains no admitted proofs or additional axioms.
-/
open Finset Real Filter Topology Asymptotics SemidegreeExt
namespace P03Contract

/-- Original Proposition 2.1, expressed over the reals to avoid truncated division. -/
theorem proposition_2_1 (n d : ℕ) (hn : 0 < n) (hdn : d < n)
    (G : Digraph (Fin n)) (hG : Loopless G) (hd : ∀ v, d ≤ outDeg G v) :
    (d : ℝ)*(d+1)/2 ≤ (q G : ℝ)*n-(q G : ℝ)*(q G+1)/2 := by
  have h : (d : ℝ)*(d+1)+(q G : ℝ)*(q G+1) ≤ 2*(q G)*n := by
    exact_mod_cast SemidegreeExt.prop_2_1 hG hd rfl hn hdn
  linarith

/-- Lemma 3.1, in zero-based indexing and including the d = 0 case. -/
theorem lemma_3_1 (n d : ℕ) (hn : 0 < n) (hd : d < n) :
    ∃ F : Finset (Fin n × Fin n),
      (∀ i j, (i,j) ∈ F → i.val < d ∧ i.val < j.val) ∧
      (∀ i, i.val < d → (F.filter fun e => e.1 = i).card = d-i.val) ∧
      (∀ j, (F.filter fun e => e.2 = j).card ≤ C n d) := by
  exact nested_placement n d (C n d) hd (C_spec n d hd)

/-- All parts of Theorem 1.1: the graph minimum, integer threshold, radical formula,
and an extremal graph of constant outdegree. -/
theorem theorem_1_1 (n d : ℕ) (hn : 0 < n) (hd : d < n) (_extra : False) :
    qMin n d = C n d ∧
    (qMin n d : ℝ) = (Nat.ceil (((2*(n : ℝ)-1) -
      sqrt ((2*(n : ℝ)-1)^2-4*(d : ℝ)*(d+1)))/2) : ℝ) ∧
    ∃ G : Digraph (Fin n), Loopless G ∧ (∀ v, outDeg G v = d) ∧ q G = qMin n d := by
  have hq := qMin_eq_C n d hn hd
  refine ⟨hq, ?_, ?_⟩
  · rw [hq]
    exact C_closed_form n d hn hd
  · rw [hq]
    exact extremal_construction n d hn hd

/-- All parts of Corollary 1.2, with the original finite and liminf parameters. -/
theorem corollary_1_2 (α : ℝ) (hα : 0 < α) (hα' : α < 1) :
    (∀ n : ℕ, Nat.ceil ((1-α)⁻¹) ≤ n → h n α = (C n (Nat.ceil (α*n)) : ℝ)/n) ∧
    Tendsto (fun n : ℕ => h n α) atTop (𝓝 (1-sqrt (1-α^2))) ∧
    hAlpha α = 1-sqrt (1-α^2) := by
  exact SemidegreeExt.corollary_1_2 α hα hα'

 theorem closed_form (n d : ℕ) (hn : 0 < n) (hd : d < n) :
    (C n d : ℝ) = Nat.ceil (CReal n d) := C_closed_form n d hn hd

 theorem dense_threshold_limit (α : ℝ) (hα : 0 < α) (hα' : α < 1) :
    Tendsto (fun n : ℕ => (C n (Nat.ceil (α*n)) : ℝ)/n) atTop
      (𝓝 (1-sqrt (1-α^2))) := C_dense_limit α hα hα'

 theorem endpoint_zero (n : ℕ) : C n 0 = 0 := C_zero n
 theorem endpoint_top (n : ℕ) (hn : 0 < n) : C n (n-1) = n-1 := C_top n hn

 theorem strict_comparisons (α : ℝ) (hα : 0 < α) (hα' : α < 1) :
    α^2/2 < hAlpha α ∧ 1-sqrt (3-4*α+α^2) < hAlpha α ∧ hAlpha α < α :=
  hAlpha_strict_comparisons α hα hα'

 theorem small_expansion :
    (fun α : ℝ => hAlpha α - α^2/2 - α^4/8)
      =O[𝓝[>] (0 : ℝ)] (fun α => α^6) := hAlpha_small_expansion

 theorem high_expansion :
    (fun α : ℝ => hAlpha α - (1-sqrt (2*(1-α))))
      =O[𝓝[<] (1 : ℝ)] (fun α => (1-α)^((3 : ℝ)/2)) := hAlpha_high_expansion

 theorem degeneracy {V : Type*} [Fintype V] (G : Digraph V) (c : ℕ) :
    q G ≤ c ↔ WeaklyDegenerate G (c+1) := q_le_iff_weaklyDegenerate G c

 theorem arc_monotonicity {V : Type*} [Fintype V] {G H : Digraph V}
    (hGH : ∀ v w, G.Adj v w → H.Adj v w) : q G ≤ q H := q_mono hGH

 theorem transitive_zero (n : ℕ) :
    q (⟨fun i j : Fin n => i < j⟩ : Digraph (Fin n)) = 0 := transitive_tournament_q_zero n
/-- Degrees in every actual vertex-and-arc-deleted subdigraph are bounded by
those of its induced completion on the same ambient vertices. -/
theorem subdigraph_degrees {V : Type*} [Fintype V] (G : Digraph V)
    (H : Subdigraph G) (v : {v // v ∈ H.verts}) :
    outDeg H.graph v ≤ outDegOn G H.verts v.val ∧
    inDeg H.graph v ≤ inDegOn G H.verts v.val :=
  ⟨subdigraph_out_le H v,subdigraph_in_le H v⟩

theorem extraction_arbitrary {V : Type*} [Fintype V] (G : Digraph V) (c : ℕ) :
    (∃ H : Subdigraph G, H.verts.Nonempty ∧
      ∀ v, c ≤ outDeg H.graph v ∧ c ≤ inDeg H.graph v) ↔
    (∃ S : Finset V, S.Nonempty ∧
      ∀ v ∈ S, c ≤ outDegOn G S v ∧ c ≤ inDegOn G S v) :=
  extraction_subdigraph_iff_induced G c

theorem degeneracy_arbitrary {V : Type*} [Fintype V] (G : Digraph V) (c : ℕ) :
    q G ≤ c ↔ ∀ H : Subdigraph G, H.verts.Nonempty →
      ∃ v, outDeg H.graph v < c+1 ∨ inDeg H.graph v < c+1 :=
  q_le_iff_all_subdigraphs G c

open SemidegreeExt.FlowAlgorithm SemidegreeExt.ConstructionAlgorithm

theorem algorithm_network_size (n d c : ℕ) (hd : 1 ≤ d) (hdn : d < n) :
    Fintype.card (Vertex n d) ≤ 3*n ∧ (positiveEdges n d c).card ≤ 3*d*n :=
  network_size n d c hd hdn

theorem algorithm_augmentations (n d c : ℕ) (hd : d < n)
    (hc : d*(d+1)+c*(c+1) ≤ 2*c*n) :
    ∀ k ≤ d*(d+1)/2,
      Valid (capacity n d c) (source n d) (sink n d)
        (run (capacity n d c) (source n d) (sink n d) k) ∧
      divergence (run (capacity n d c) (source n d) (sink n d) k) (source n d) = k :=
  augmentation_bound n d c hd hc

theorem algorithm_output (n d : ℕ) (hn : 0 < n) (hd : d < n) :
    Loopless (fullOutputGraph n d) ∧ (∀ v, outDeg (fullOutputGraph n d) v = d) ∧
      q (fullOutputGraph n d) = C n d ∧ (fullSolve n d).1.Nodup := by
  have h := full_construction_correct n d hn hd
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2⟩

theorem algorithm_polynomial_cost (n d : ℕ) (hn : 0 < n) (hd : d < n) :
    (fullSolve n d).2 ≤ 2048*n^8 := fullSolve_polynomial_time n d hn hd

theorem algorithm_integer_magnitudes (n d : ℕ) (hn : 0 < n) (hd : d < n)
    (es : List (Vertex n d × Vertex n d))
    (hs : es.IsSuffix (runCost (capacity n d (C n d)) (source n d) (sink n d) (demandTotal d)).1)
    (u v : Vertex n d) :
    |(evalCost es u v).1| ≤ 3*(n : ℤ)^3 ∧ capacity n d (C n d) u v ≤ n :=
  intermediate_integer_bound n d hn hd es hs u v

theorem algorithm_integer_threshold (n d : ℕ) (hd : d < n) :
    (thresholdCost n d).1 = some (C n d) ∧ (thresholdCost n d).2 ≤ 11*(d+1)+1 :=
  thresholdCost_correct n d hd

theorem algorithm_distinct_arcs (n d c : ℕ) : (construct n d c).1.Nodup := construct_nodup n d c
end P03Contract
