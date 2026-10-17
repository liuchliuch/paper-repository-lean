import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# Finite loopless digraphs and the extraction parameter `q`

Definitions matching *Exact semidegree extraction from minimum outdegree*.
Digraphs are finite simple digraphs **without loops** (opposite arcs allowed).
-/

open Finset Digraph Nat
open Classical

namespace SemidegreeExt

/-- A loopless digraph (paper: digraphs have no loops or parallel arcs). -/
def Loopless {V : Type*} (G : Digraph V) : Prop := ∀ v : V, ¬ G.Adj v v

variable {V : Type*} [Fintype V]

/-- Outdegree of `v` in the spanning digraph `G`. -/
noncomputable def outDeg (G : Digraph V) (v : V) : ℕ :=
  (univ.filter (fun u => G.Adj v u)).card

/-- Indegree of `v` in the spanning digraph `G`. -/
noncomputable def inDeg (G : Digraph V) (v : V) : ℕ :=
  (univ.filter (fun u => G.Adj u v)).card

/-- Outdegree of `v` inside the induced subdigraph on `S`. -/
noncomputable def outDegOn (G : Digraph V) (S : Finset V) (v : V) : ℕ :=
  (S.filter (fun u => G.Adj v u)).card

/-- Indegree of `v` inside the induced subdigraph on `S`. -/
noncomputable def inDegOn (G : Digraph V) (S : Finset V) (v : V) : ℕ :=
  (S.filter (fun u => G.Adj u v)).card

/-- Minimum of indegree and outdegree of `v` in `G[S]`. -/
noncomputable def semiDegOn (G : Digraph V) (S : Finset V) (v : V) : ℕ :=
  min (outDegOn G S v) (inDegOn G S v)

/-- Minimum semidegree of the induced subdigraph on `S` (0 if `S` empty). -/
noncomputable def minSemiDegOn (G : Digraph V) (S : Finset V) : ℕ :=
  if h : S.Nonempty then S.inf' h (semiDegOn G S) else 0

/-- Extraction parameter `q(G)` = max over nonempty induced subdigraphs of min semidegree. -/
noncomputable def q (G : Digraph V) : ℕ :=
  ((univ : Finset (Finset V)).filter (fun S => S.Nonempty)).sup
    (fun S => minSemiDegOn G S)

/-- Minimum outdegree `δ⁺(G)`; 0 if the vertex type is empty. -/
noncomputable def minOutDeg (G : Digraph V) : ℕ :=
  if h : (univ : Finset V).Nonempty then univ.inf' h (outDeg G) else 0

/-- Threshold `C(n,d)` = least `c ≥ 0` with `d(d+1) + c(c+1) ≤ 2 c n`, for `d < n`. -/
def C (n d : ℕ) : ℕ :=
  if h : d < n then
    Nat.find
      (show ∃ c : ℕ, d * (d + 1) + c * (c + 1) ≤ 2 * c * n from
        ⟨d, by
          have hdn : d + 1 ≤ n := Nat.succ_le_of_lt h
          have h1 : d * (d + 1) + d * (d + 1) = 2 * (d * (d + 1)) := by ring
          have h2 : 2 * (d * (d + 1)) ≤ 2 * (d * n) := by gcongr
          have h3 : 2 * (d * n) = 2 * d * n := by ring
          calc d * (d + 1) + d * (d + 1) = 2 * (d * (d + 1)) := h1
            _ ≤ 2 * (d * n) := h2
            _ = 2 * d * n := h3⟩)
  else 0

/-- Closed-form threshold appearing in Theorem 1.1. -/
noncomputable def CReal (n d : ℕ) : ℝ :=
  ((2 * n - 1 : ℝ) - Real.sqrt (((2 * n - 1 : ℝ)^2 - 4 * (d : ℝ) * (d + 1)))) / 2

@[simp] lemma outDegOn_univ (G : Digraph V) (v : V) : outDegOn G univ v = outDeg G v := by
  simp [outDegOn, outDeg]

lemma outDegOn_le_card (G : Digraph V) (S : Finset V) (v : V) :
    outDegOn G S v ≤ S.card := by
  unfold outDegOn
  exact card_le_card (filter_subset (fun u => G.Adj v u) S)

lemma outDegOn_mono (G : Digraph V) {S T : Finset V} (h : S ⊆ T) (v : V) :
    outDegOn G S v ≤ outDegOn G T v := by
  unfold outDegOn
  exact card_le_card (filter_subset_filter _ h)

lemma outDegOn_le_outDeg (G : Digraph V) (S : Finset V) (v : V) :
    outDegOn G S v ≤ outDeg G v :=
  outDegOn_mono G (subset_univ S) v

/-- `q(G)` is at least the min semidegree of every nonempty induced subdigraph. -/
lemma le_q (G : Digraph V) {S : Finset V} (hS : S.Nonempty) :
    minSemiDegOn G S ≤ q G := by
  have hmem : S ∈ ((univ : Finset (Finset V)).filter (fun S => S.Nonempty)) := by
    simp [hS]
  exact le_sup hmem

/-- If `c = q(G)` then every nonempty induced subdigraph has a vertex of semidegree ≤ `c`. -/
lemma exists_semiDegOn_le {G : Digraph V} {c : ℕ} (hc : c = q G) {S : Finset V}
    (hS : S.Nonempty) :
    ∃ v ∈ S, semiDegOn G S v ≤ c := by
  have h := le_q G hS
  simp only [minSemiDegOn, dif_pos hS] at h
  -- h : S.inf' hS (semiDegOn G S) ≤ c
  -- h : S.inf' hS (semiDegOn G S) ≤ q G
  have h' : ∃ i ∈ S, semiDegOn G S i ≤ q G := by
    simpa [Finset.inf'_le_iff] using h
  obtain ⟨v, hv, hvq⟩ := h'
  exact ⟨v, hv, by omega⟩

/-- `C(n,d) ≤ d` whenever `d < n`. -/
lemma C_le_d (n d : ℕ) (hd : d < n) : C n d ≤ d := by
  have hex : ∃ c : ℕ, d * (d + 1) + c * (c + 1) ≤ 2 * c * n :=
    ⟨d, by
      have hdn : d + 1 ≤ n := Nat.succ_le_of_lt hd
      have h1 : d * (d + 1) + d * (d + 1) = 2 * (d * (d + 1)) := by ring
      have h2 : 2 * (d * (d + 1)) ≤ 2 * (d * n) := by gcongr
      have h3 : 2 * (d * n) = 2 * d * n := by ring
      calc d * (d + 1) + d * (d + 1) = 2 * (d * (d + 1)) := h1
        _ ≤ 2 * (d * n) := h2
        _ = 2 * d * n := h3⟩
  simp only [C, hd]
  have hp : (fun c => d * (d + 1) + c * (c + 1) ≤ 2 * c * n) d :=
    hex.choose_spec |> fun _ => by
      have hdn : d + 1 ≤ n := Nat.succ_le_of_lt hd
      have h1 : d * (d + 1) + d * (d + 1) = 2 * (d * (d + 1)) := by ring
      have h2 : 2 * (d * (d + 1)) ≤ 2 * (d * n) := by gcongr
      have h3 : 2 * (d * n) = 2 * d * n := by ring
      calc d * (d + 1) + d * (d + 1) = 2 * (d * (d + 1)) := h1
        _ ≤ 2 * (d * n) := h2
        _ = 2 * d * n := h3
  exact Nat.find_min' (H := hex) hp

/-- The defining inequality of `C(n,d)` holds. -/
lemma C_spec (n d : ℕ) (hd : d < n) :
    d * (d + 1) + C n d * (C n d + 1) ≤ 2 * C n d * n := by
  have hex : ∃ c : ℕ, d * (d + 1) + c * (c + 1) ≤ 2 * c * n :=
    ⟨d, by
      have hdn : d + 1 ≤ n := Nat.succ_le_of_lt hd
      have h1 : d * (d + 1) + d * (d + 1) = 2 * (d * (d + 1)) := by ring
      have h2 : 2 * (d * (d + 1)) ≤ 2 * (d * n) := by gcongr
      have h3 : 2 * (d * n) = 2 * d * n := by ring
      calc d * (d + 1) + d * (d + 1) = 2 * (d * (d + 1)) := h1
        _ ≤ 2 * (d * n) := h2
        _ = 2 * d * n := h3⟩
  simp only [C, hd]
  exact Nat.find_spec hex

/-- Minimality of `C(n,d)`. -/
lemma C_is_least (n d : ℕ) (hd : d < n) {c : ℕ}
    (h : d * (d + 1) + c * (c + 1) ≤ 2 * c * n) : C n d ≤ c := by
  have hex : ∃ m : ℕ, d * (d + 1) + m * (m + 1) ≤ 2 * m * n := ⟨c, h⟩
  simp only [C, hd]
  exact Nat.find_min' (H := hex) h

end SemidegreeExt
