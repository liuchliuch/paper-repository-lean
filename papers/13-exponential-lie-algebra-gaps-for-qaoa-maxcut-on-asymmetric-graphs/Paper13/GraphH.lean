import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# The seven-vertex gadget `H` and the rigid tree `T_k`

Graph `H` (paper eq. (11)) on vertices `{1,…,7}` with
`E(H) = {12, 23, 34, 45, 56, 67, 26, 36}`.
We use 0-indexed `Fin 7`, so the edge set is
`{01, 12, 23, 34, 45, 56, 15, 25}` and the port is vertex `4`.

The tree `T_k` is the center `0` with three arms of lengths `1`, `2`, `k-4`.
-/

universe u v

set_option maxHeartbeats 400000

namespace Paper13

open SimpleGraph

section Aux

variable {V : Type u} {W : Type v}

/-- Identity automorphism of a graph (self-isomorphism). -/
instance {G : SimpleGraph V} : One (G ≃g G) :=
  ⟨SimpleGraph.Iso.refl⟩

/-- Graph isomorphisms preserve degrees. -/
lemma SimpleGraph.Iso.degree_eq {G : SimpleGraph V} {G' : SimpleGraph W}
    (f : G ≃g G') (v : V) [Fintype (G.neighborSet v)] [Fintype (G'.neighborSet (f v))] :
    G.degree v = G'.degree (f v) := by
  rw [← card_neighborSet_eq_degree, ← card_neighborSet_eq_degree]
  exact Fintype.card_congr (f.mapNeighborSet v)

/-- `NeZero` for sizes at least seven (needed for `Fin k` numerals). -/
lemma neZero_of_seven_le {k : ℕ} (hk : 7 ≤ k) : NeZero k :=
  ⟨by omega⟩




end Aux

/-! ## The gadget `H` -/

/-- Undirected edges of `H` as pairs of vertices. -/
def HEdges : Finset (Finset (Fin 7)) :=
  {{0, 1}, {1, 2}, {2, 3}, {3, 4}, {4, 5}, {5, 6}, {1, 5}, {2, 5}}

/-- The seven-vertex gadget `H` of the paper, on `Fin 7` (0-indexed). -/
def H : SimpleGraph (Fin 7) where
  Adj a b := a ≠ b ∧ {a, b} ∈ HEdges
  symm := by
    intro a b ⟨hne, hE⟩
    exact ⟨hne.symm, by rwa [Finset.pair_comm]⟩
  loopless := by
    intro a h
    exact h.1 rfl

instance (a b : Fin 7) : Decidable (H.Adj a b) :=
  show Decidable (a ≠ b ∧ {a, b} ∈ HEdges) from inferInstance

/-- Port of the gadget `H`: vertex 5 in 1-based numbering = `4 : Fin 7`. -/
def Hport : Fin 7 := 4

/-- Singlet pairing used by the projector: `(1,3), (2,7), (4,6)` in 1-based numbering,
i.e. `(0,2), (1,6), (3,5)` in 0-indexed `Fin 7`. -/
def Hpairs : Finset (Fin 7 × Fin 7) := {(0, 2), (1, 6), (3, 5)}

lemma H_edge_01 : H.Adj 0 1 := by decide
lemma H_edge_12 : H.Adj 1 2 := by decide
lemma H_edge_23 : H.Adj 2 3 := by decide
lemma H_edge_34 : H.Adj 3 4 := by decide
lemma H_edge_45 : H.Adj 4 5 := by decide
lemma H_edge_56 : H.Adj 5 6 := by decide
lemma H_edge_15 : H.Adj 1 5 := by decide
lemma H_edge_25 : H.Adj 2 5 := by decide

/-- Degree table of `H`. -/
lemma H_degree (v : Fin 7) :
    H.degree v = match v with
      | 0 => 1 | 1 => 3 | 2 => 3 | 3 => 2 | 4 => 2 | 5 => 4 | 6 => 1 := by
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  fin_cases v <;> decide

lemma H_degree_0 : H.degree 0 = 1 := by decide
lemma H_degree_1 : H.degree 1 = 3 := by decide
lemma H_degree_2 : H.degree 2 = 3 := by decide
lemma H_degree_3 : H.degree 3 = 2 := by decide
lemma H_degree_4 : H.degree 4 = 2 := by decide
lemma H_degree_5 : H.degree 5 = 4 := by decide
lemma H_degree_6 : H.degree 6 = 1 := by decide

lemma H_sum_degrees : ∑ v : Fin 7, H.degree v = 16 := by
  have h0 : (Finset.univ : Finset (Fin 7)) = {0, 1, 2, 3, 4, 5, 6} := by decide
  rw [h0]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  rw [H_degree_0, H_degree_1, H_degree_2, H_degree_3, H_degree_4, H_degree_5, H_degree_6]
  norm_num

lemma H_neighborFinset_0 : H.neighborFinset 0 = {1} := by decide
lemma H_neighborFinset_1 : H.neighborFinset 1 = {0, 2, 5} := by decide
lemma H_neighborFinset_2 : H.neighborFinset 2 = {1, 3, 5} := by decide
lemma H_neighborFinset_3 : H.neighborFinset 3 = {2, 4} := by decide
lemma H_neighborFinset_4 : H.neighborFinset 4 = {3, 5} := by decide
lemma H_neighborFinset_5 : H.neighborFinset 5 = {1, 2, 4, 6} := by decide
lemma H_neighborFinset_6 : H.neighborFinset 6 = {5} := by decide

/-- Every non-port vertex of `H` has degree at most 4. -/
lemma H_nonport_degree_le_four (v : Fin 7) (h : v ≠ Hport) : H.degree v ≤ 4 := by
  fin_cases v <;> first | (exfalso; simpa [Hport] using h) | decide

lemma H_port_degree : H.degree Hport = 2 := by
  simp [Hport, H_degree_4]

lemma H_degree_le_four (v : Fin 7) : H.degree v ≤ 4 := by
  by_cases h : v = Hport
  · subst h; rw [H_port_degree]; omega
  · exact H_nonport_degree_le_four v h

/-- The triangle `2–3–6` (0-indexed `1,2,5`) shows `H` is non-bipartite. -/
lemma H_triangle : H.Adj 1 2 ∧ H.Adj 2 5 ∧ H.Adj 1 5 :=
  ⟨H_edge_12, H_edge_25, H_edge_15⟩

/-- `H` has exactly 8 undirected edges (as a `Finset`). -/
lemma H_edgeFinset_card : H.edgeFinset.card = 8 := by
  have hsum := SimpleGraph.sum_degrees_eq_twice_card_edges (G := H)
  rw [H_sum_degrees] at hsum
  omega

/-- `H` has exactly 8 undirected edges. -/
lemma H_edgeSet_card : H.edgeSet.ncard = 8 := by
  rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  exact H_edgeFinset_card

/-- `H` is connected (hence each gadget copy is connected). -/
lemma H_connected : H.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, ?_⟩
  intro v
  have r01 : H.Reachable 0 1 := H_edge_01.reachable
  have r12 : H.Reachable 1 2 := H_edge_12.reachable
  have r23 : H.Reachable 2 3 := H_edge_23.reachable
  have r34 : H.Reachable 3 4 := H_edge_34.reachable
  have r45 : H.Reachable 4 5 := H_edge_45.reachable
  have r56 : H.Reachable 5 6 := H_edge_56.reachable
  fin_cases v
  · exact SimpleGraph.Reachable.refl 0
  · exact r01
  · exact r01.trans r12
  · exact (r01.trans r12).trans r23
  · exact ((r01.trans r12).trans r23).trans r34
  · exact (((r01.trans r12).trans r23).trans r34).trans r45
  · exact ((((r01.trans r12).trans r23).trans r34).trans r45).trans r56

/-- Every vertex of `H` is reachable from the port. -/
lemma H_reachable_from_port (v : Fin 7) : H.Reachable Hport v :=
  H_connected Hport v

/-! ## Rigid tree `T_k` -/

/-- Vertex type of the tree `T_k`: `Fin k`. Vertex `0` is the center. -/
abbrev TkVert (k : ℕ) := Fin k

/--
Adjacency of the tree `T_k`: center `0` with three arms of lengths `1`, `2`, `k-4`.
Arm A: `0–1`. Arm B: `0–2–3`. Arm C: `0–(k-1)–(k-2)–…–4`.
All comparisons are on `Nat` values of `Fin k`, so there is no modular wrap-around.
-/
def T (k : ℕ) : SimpleGraph (Fin k) where
  Adj a b := a ≠ b ∧ (
    (a.val = 0 ∧ b.val = 1) ∨ (a.val = 1 ∧ b.val = 0) ∨
    (a.val = 0 ∧ b.val = 2) ∨ (a.val = 2 ∧ b.val = 0) ∨
    (a.val = 2 ∧ b.val = 3) ∨ (a.val = 3 ∧ b.val = 2) ∨
    (a.val = 0 ∧ b.val + 1 = k) ∨ (a.val + 1 = k ∧ b.val = 0) ∨
    (4 ≤ a.val ∧ a.val + 1 = b.val) ∨
    (4 ≤ b.val ∧ b.val + 1 = a.val))
  symm := by
    intro a b h
    obtain ⟨hne, hE⟩ := h
    refine ⟨hne.symm, ?_⟩
    rcases hE with h | h | h | h | h | h | h | h | h | h
    · exact .inr (.inl h.symm)
    · exact .inl h.symm
    · exact .inr (.inr (.inr (.inl h.symm)))
    · exact .inr (.inr (.inl h.symm))
    · exact .inr (.inr (.inr (.inr (.inr (.inl h.symm)))))
    · exact .inr (.inr (.inr (.inr (.inl h.symm))))
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h.symm)))))))
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl h.symm))))))
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr h))))))))
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))))
  loopless := by
    intro a h
    exact h.1 rfl

instance (k : ℕ) : DecidableRel (T k).Adj := fun a b => by
  show Decidable (_ ∧ (_ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _))
  infer_instance

/-- `T_k` has `k` vertices. -/
lemma T_card_verts (k : ℕ) : Fintype.card (Fin k) = k := by
  simp

section TMain
variable {k : ℕ} [NeZero k]

lemma fin_val_zero' : (0 : Fin k).val = 0 := rfl
lemma fin_val_one' (hk : 7 ≤ k) : (1 : Fin k).val = 1 := Fin.val_cast_of_lt (by omega : 1 < k)
lemma fin_val_two' (hk : 7 ≤ k) : (2 : Fin k).val = 2 := Fin.val_cast_of_lt (by omega : 2 < k)
lemma fin_val_three' (hk : 7 ≤ k) : (3 : Fin k).val = 3 := Fin.val_cast_of_lt (by omega : 3 < k)
lemma fin_val_four' (hk : 7 ≤ k) : (4 : Fin k).val = 4 := Fin.val_cast_of_lt (by omega : 4 < k)
lemma fin_val_five' (hk : 7 ≤ k) : (5 : Fin k).val = 5 := Fin.val_cast_of_lt (by omega : 5 < k)

lemma fin_eq_of_val {a b : Fin k} (h : a.val = b.val) : a = b := Fin.eq_of_val_eq h

lemma T_adj_zero_one (hk : 7 ≤ k) : (T k).Adj 0 1 := by
  have hne : (0 : Fin k) ≠ 1 := by
    intro h
    have := congrArg Fin.val h
    rw [fin_val_zero', fin_val_one' hk] at this
    omega
  refine ⟨hne, ?_⟩
  left
  rw [fin_val_zero', fin_val_one' hk]
  exact ⟨rfl, rfl⟩
lemma T_adj_zero_two (hk : 7 ≤ k) : (T k).Adj 0 2 := by
  have hne : (0 : Fin k) ≠ 2 := by
    intro h
    have := congrArg Fin.val h
    rw [fin_val_zero', fin_val_two' hk] at this
    omega
  refine ⟨hne, ?_⟩
  right; right; left
  rw [fin_val_zero', fin_val_two' hk]
  exact ⟨rfl, rfl⟩
lemma T_adj_two_three (hk : 7 ≤ k) : (T k).Adj 2 3 := by
  have hne : (2 : Fin k) ≠ 3 := by
    intro h
    have := congrArg Fin.val h
    rw [fin_val_two' hk, fin_val_three' hk] at this
    omega
  refine ⟨hne, ?_⟩
  right; right; right; right; left
  rw [fin_val_two' hk, fin_val_three' hk]
  exact ⟨rfl, rfl⟩
lemma T_adj_zero_last (hk : 7 ≤ k) : (T k).Adj 0 ⟨k - 1, by omega⟩ := by
  have hne : (0 : Fin k) ≠ ⟨k - 1, by omega⟩ := by
    intro h
    have := congrArg Fin.val h
    rw [fin_val_zero'] at this
    simp at this
    omega
  refine ⟨hne, ?_⟩
  right; right; right; right; right; right; left
  rw [fin_val_zero']
  have hv : (⟨k - 1, by omega⟩ : Fin k).val = k - 1 := rfl
  exact ⟨rfl, by rw [hv]; omega⟩

lemma T_adj_consecutive {i j : ℕ} (hi : i < k) (hj : j < k)
    (h : 4 ≤ i) (hij : i + 1 = j) : (T k).Adj ⟨i, hi⟩ ⟨j, hj⟩ := by
  subst hij
  have hne : (⟨i, hi⟩ : Fin k) ≠ ⟨i + 1, hj⟩ := by
    intro he
    have := congrArg Fin.val he
    simp at this
  exact ⟨hne, .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨h, rfl⟩))))))))⟩

lemma T_adj_pred {i : ℕ} (hi : i < k) (h4 : 5 ≤ i) :
    (T k).Adj ⟨i, hi⟩ ⟨i - 1, by omega⟩ := by
  have hne : (⟨i, hi⟩ : Fin k) ≠ ⟨i - 1, by omega⟩ := by
    intro he
    have := congrArg Fin.val he
    simp at this
    omega
  have hle : (4 : ℕ) ≤ (⟨i - 1, by omega⟩ : Fin k).val := by simp; omega
  have hs : (⟨i - 1, by omega⟩ : Fin k).val + 1 = (⟨i, hi⟩ : Fin k).val := by simp; omega
  refine ⟨hne, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hle, hs⟩))))))))⟩

lemma T_adj_symm' {a b : Fin k} (h : (T k).Adj a b) : (T k).Adj b a := (T k).symm h
lemma T_adj_one_zero (hk : 7 ≤ k) : (T k).Adj 1 0 := T_adj_symm' (T_adj_zero_one hk)
lemma T_adj_three_two (hk : 7 ≤ k) : (T k).Adj 3 2 := T_adj_symm' (T_adj_two_three hk)
lemma T_adj_last_zero (hk : 7 ≤ k) : (T k).Adj ⟨k - 1, by omega⟩ 0 :=
  T_adj_symm' (T_adj_zero_last hk)
lemma T_adj_succ_symm {i : ℕ} (hi : i < k) (h4 : 4 ≤ i) (hlt : i + 1 < k) :
    (T k).Adj ⟨i + 1, hlt⟩ ⟨i, hi⟩ :=
  T_adj_symm' (T_adj_consecutive hi hlt h4 rfl)

lemma T_mem_adj_zero (hk : 7 ≤ k) {b : Fin k} :
    (T k).Adj 0 b ↔ b.val = 1 ∨ b.val = 2 ∨ b.val = k - 1 := by
  have hv0 : ((0 : Fin k) : ℕ) = 0 := fin_val_zero'
  constructor
  · intro ⟨_, hE⟩
    rcases hE with h | h | h | h | h | h | h | h | h | h
      <;> first
        | (left; rw [hv0] at h; omega)
        | (right; left; rw [hv0] at h; omega)
        | (right; right; rw [hv0] at h; omega)
        | (exfalso; rw [hv0] at h; omega)
  · intro h
    rcases h with h | h | h
    · have hbeq : b = 1 := fin_eq_of_val (h.trans (fin_val_one' hk).symm)
      rw [hbeq]; exact T_adj_zero_one hk
    · have hbeq : b = 2 := fin_eq_of_val (h.trans (fin_val_two' hk).symm)
      rw [hbeq]; exact T_adj_zero_two hk
    · have hbeq : b = ⟨k - 1, by omega⟩ := Fin.eq_of_val_eq h
      rw [hbeq]; exact T_adj_zero_last hk

lemma T_neighborFinset_zero (hk : 7 ≤ k) :
    (T k).neighborFinset 0 = {1, 2, ⟨k - 1, by omega⟩} := by
  ext b
  simp only [Finset.mem_insert, Finset.mem_singleton, SimpleGraph.mem_neighborFinset,
    T_mem_adj_zero hk]
  constructor
  · intro h
    rcases h with h | h | h
    · left; exact fin_eq_of_val (h.trans (fin_val_one' hk).symm)
    · right; left; exact fin_eq_of_val (h.trans (fin_val_two' hk).symm)
    · right; right; exact Fin.eq_of_val_eq h
  · intro h
    rcases h with h | h | h
    · left; rw [h]; exact fin_val_one' hk
    · right; left; rw [h]; exact fin_val_two' hk
    · right; right; rw [h]

lemma T_center_degree (hk : 7 ≤ k) : (T k).degree 0 = 3 := by
  show Finset.card ((T k).neighborFinset 0) = 3
  rw [T_neighborFinset_zero hk]
  have h12 : (1 : Fin k) ≠ 2 := by
    intro h; have := congrArg Fin.val h; rw [fin_val_one' hk, fin_val_two' hk] at this; omega
  have h1l : (1 : Fin k) ≠ ⟨k - 1, by omega⟩ := by
    intro h; have := congrArg Fin.val h; rw [fin_val_one' hk] at this; simp at this; omega
  have h2l : (2 : Fin k) ≠ ⟨k - 1, by omega⟩ := by
    intro h; have := congrArg Fin.val h; rw [fin_val_two' hk] at this; simp at this; omega
  simp [h12, h1l, h2l]

lemma T_mem_adj_one (hk : 7 ≤ k) {b : Fin k} : (T k).Adj 1 b ↔ b.val = 0 := by
  have hv1 : ((1 : Fin k) : ℕ) = 1 := fin_val_one' hk
  constructor
  · intro ⟨_, hE⟩
    rcases hE with h | h | h | h | h | h | h | h | h | h
      <;> first | (rw [hv1] at h; omega) | (exfalso; rw [hv1] at h; omega)
  · intro h
    have : b = 0 := fin_eq_of_val (h.trans (fin_val_zero').symm)
    rw [this]; exact T_adj_one_zero hk

lemma T_neighborFinset_one (hk : 7 ≤ k) : (T k).neighborFinset 1 = {0} := by
  ext b
  rw [SimpleGraph.mem_neighborFinset, Finset.mem_singleton, T_mem_adj_one hk]
  constructor
  · intro h
    exact Fin.eq_of_val_eq (h.trans (fin_val_zero').symm)
  · intro h
    rw [h]
    exact fin_val_zero'

lemma T_degree_one (hk : 7 ≤ k) : (T k).degree 1 = 1 := by
  show Finset.card ((T k).neighborFinset 1) = 1
  rw [T_neighborFinset_one hk]
  simp

lemma T_mem_adj_two (hk : 7 ≤ k) {b : Fin k} : (T k).Adj 2 b ↔ b.val = 0 ∨ b.val = 3 := by
  have hv2 : ((2 : Fin k) : ℕ) = 2 := fin_val_two' hk
  constructor
  · intro ⟨_, hE⟩
    rcases hE with h | h | h | h | h | h | h | h | h | h
      <;> first
        | (left; rw [hv2] at h; omega)
        | (right; rw [hv2] at h; omega)
        | (exfalso; rw [hv2] at h; omega)
  · intro h
    rcases h with h | h
    · have hbeq : b = 0 := fin_eq_of_val (h.trans (fin_val_zero').symm)
      rw [hbeq]; exact T_adj_symm' (T_adj_zero_two hk)
    · have hbeq : b = 3 := fin_eq_of_val (h.trans (fin_val_three' hk).symm)
      rw [hbeq]; exact T_adj_two_three hk

lemma T_neighborFinset_two (hk : 7 ≤ k) : (T k).neighborFinset 2 = {0, 3} := by
  ext b
  simp only [Finset.mem_insert, Finset.mem_singleton, SimpleGraph.mem_neighborFinset,
    T_mem_adj_two hk]
  constructor
  · rintro (h | h)
    · left; exact Fin.eq_of_val_eq (h.trans (fin_val_zero').symm)
    · right; exact Fin.eq_of_val_eq (h.trans (fin_val_three' hk).symm)
  · rintro (h | h)
    · left; rw [h]; exact fin_val_zero'
    · right; rw [h]; exact fin_val_three' hk

lemma T_degree_two (hk : 7 ≤ k) : (T k).degree 2 = 2 := by
  show Finset.card ((T k).neighborFinset 2) = 2
  rw [T_neighborFinset_two hk]
  have : (0 : Fin k) ≠ 3 := by
    intro h; have := congrArg Fin.val h; rw [fin_val_zero', fin_val_three' hk] at this; omega
  simp [this]

lemma T_mem_adj_three (hk : 7 ≤ k) {b : Fin k} : (T k).Adj 3 b ↔ b.val = 2 := by
  have hv3 : ((3 : Fin k) : ℕ) = 3 := fin_val_three' hk
  constructor
  · intro ⟨_, hE⟩
    rcases hE with h | h | h | h | h | h | h | h | h | h
      <;> first | (rw [hv3] at h; omega) | (exfalso; rw [hv3] at h; omega)
  · intro h
    have : b = 2 := fin_eq_of_val (h.trans (fin_val_two' hk).symm)
    rw [this]; exact T_adj_three_two hk

lemma T_neighborFinset_three (hk : 7 ≤ k) : (T k).neighborFinset 3 = {2} := by
  ext b
  simp only [Finset.mem_singleton, SimpleGraph.mem_neighborFinset, T_mem_adj_three hk]
  constructor
  · intro h; exact Fin.eq_of_val_eq (h.trans (fin_val_two' hk).symm)
  · intro h; rw [h]; exact fin_val_two' hk

lemma T_degree_three (hk : 7 ≤ k) : (T k).degree 3 = 1 := by
  show Finset.card ((T k).neighborFinset 3) = 1
  rw [T_neighborFinset_three hk]
  simp

lemma T_mem_adj_four (hk : 7 ≤ k) {b : Fin k} : (T k).Adj 4 b ↔ b.val = 5 := by
  have hv4 : ((4 : Fin k) : ℕ) = 4 := fin_val_four' hk
  constructor
  · intro ⟨_, hE⟩
    rcases hE with h | h | h | h | h | h | h | h | h | h
      <;> first | (rw [hv4] at h; omega) | (exfalso; rw [hv4] at h; omega)
  · intro h
    have : b = 5 := fin_eq_of_val (h.trans (fin_val_five' hk).symm)
    rw [this]
    have hne : (4 : Fin k) ≠ 5 := by
      intro h; have := congrArg Fin.val h
      rw [fin_val_four' hk, fin_val_five' hk] at this; omega
    refine ⟨hne, .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨?_, ?_⟩))))))))⟩
    · show 4 ≤ (4 : Fin k).val
      rw [fin_val_four' hk]
    · show (4 : Fin k).val + 1 = (5 : Fin k).val
      rw [fin_val_four' hk, fin_val_five' hk]

lemma T_neighborFinset_four (hk : 7 ≤ k) : (T k).neighborFinset 4 = {5} := by
  ext b
  simp only [Finset.mem_singleton, SimpleGraph.mem_neighborFinset, T_mem_adj_four hk]
  constructor
  · intro h; exact Fin.eq_of_val_eq (h.trans (fin_val_five' hk).symm)
  · intro h; rw [h]; exact fin_val_five' hk

lemma T_degree_four (hk : 7 ≤ k) : (T k).degree 4 = 1 := by
  show Finset.card ((T k).neighborFinset 4) = 1
  rw [T_neighborFinset_four hk]
  simp


lemma T_adj_last_pred (hk : 7 ≤ k) :
    (T k).Adj ⟨k - 1, by omega⟩ ⟨k - 2, by omega⟩ := by
  have hne : (⟨k - 1, by omega⟩ : Fin k) ≠ ⟨k - 2, by omega⟩ := by
    intro he; have := congrArg Fin.val he; simp at this; omega
  have hle : 4 ≤ ((⟨k - 2, by omega⟩ : Fin k) : ℕ) := by simp; omega
  have hs : ((⟨k - 2, by omega⟩ : Fin k) : ℕ) + 1 = ((⟨k - 1, by omega⟩ : Fin k) : ℕ) := by
    simp; omega
  exact ⟨hne, Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| ⟨hle, hs⟩⟩

lemma T_mem_adj_last (hk : 7 ≤ k) {b : Fin k} :
    (T k).Adj ⟨k - 1, by omega⟩ b ↔ b.val = 0 ∨ b.val = k - 2 := by
  have hv : ((⟨k - 1, by omega⟩ : Fin k) : ℕ) = k - 1 := by simp
  constructor
  · intro ⟨_, hE⟩
    rcases hE with h | h | h | h | h | h | h | h | h | h
      <;> first
        | (left; rw [hv] at h; omega)
        | (right; rw [hv] at h; omega)
        | (exfalso; rw [hv] at h; omega)
  · intro h
    rcases h with h | h
    · have hbeq : b = 0 := Fin.eq_of_val_eq (h.trans (fin_val_zero').symm)
      rw [hbeq]; exact T_adj_last_zero hk
    · have hbeq : b = ⟨k - 2, by omega⟩ := Fin.eq_of_val_eq h
      rw [hbeq]; exact T_adj_last_pred hk

lemma T_neighborFinset_last (hk : 7 ≤ k) :
    (T k).neighborFinset ⟨k - 1, by omega⟩ = {0, ⟨k - 2, by omega⟩} := by
  ext b
  simp only [Finset.mem_insert, Finset.mem_singleton, SimpleGraph.mem_neighborFinset,
    T_mem_adj_last hk]
  constructor
  · rintro (h | h)
    · left; exact Fin.eq_of_val_eq (h.trans (fin_val_zero').symm)
    · right; exact Fin.eq_of_val_eq h
  · rintro (h | h)
    · left; rw [h]; exact fin_val_zero'
    · right; rw [h]

lemma T_degree_last (hk : 7 ≤ k) : (T k).degree ⟨k - 1, by omega⟩ = 2 := by
  show Finset.card ((T k).neighborFinset ⟨k - 1, by omega⟩) = 2
  rw [T_neighborFinset_last hk]
  have : (0 : Fin k) ≠ ⟨k - 2, by omega⟩ := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  simp [this]

lemma T_mem_adj_internal {i : ℕ} (hi : i < k) (h5 : 5 ≤ i) (hne : i ≠ k - 1) {b : Fin k} :
    (T k).Adj ⟨i, hi⟩ b ↔ b.val = i - 1 ∨ b.val = i + 1 := by
  have hv : ((⟨i, hi⟩ : Fin k) : ℕ) = i := by simp
  constructor
  · intro ⟨_, hE⟩
    rcases hE with h | h | h | h | h | h | h | h | h | h
      <;> first
        | (left; rw [hv] at h; omega)
        | (right; rw [hv] at h; omega)
        | (exfalso; rw [hv] at h; omega)
  · intro h
    rcases h with h | h
    · have hbeq : b = ⟨i - 1, by omega⟩ := Fin.eq_of_val_eq h
      rw [hbeq]; exact T_adj_pred hi h5
    · have hbeq : b = ⟨i + 1, by omega⟩ := Fin.eq_of_val_eq h
      rw [hbeq]; exact T_adj_consecutive hi (by omega) (by omega) rfl

lemma T_neighborFinset_internal {i : ℕ} (hi : i < k) (h5 : 5 ≤ i) (hne : i ≠ k - 1) :
    (T k).neighborFinset ⟨i, hi⟩ = {⟨i - 1, by omega⟩, ⟨i + 1, by omega⟩} := by
  ext b
  simp only [Finset.mem_insert, Finset.mem_singleton, SimpleGraph.mem_neighborFinset,
    T_mem_adj_internal hi h5 hne]
  constructor
  · rintro (h | h)
    · left; exact Fin.eq_of_val_eq h
    · right; exact Fin.eq_of_val_eq h
  · rintro (h | h)
    · left; rw [h]
    · right; rw [h]

lemma T_degree_internal {i : ℕ} (hi : i < k) (h5 : 5 ≤ i) (hne : i ≠ k - 1) :
    (T k).degree ⟨i, hi⟩ = 2 := by
  show Finset.card ((T k).neighborFinset ⟨i, hi⟩) = 2
  rw [T_neighborFinset_internal hi h5 hne]
  have : (⟨i - 1, by omega⟩ : Fin k) ≠ ⟨i + 1, by omega⟩ := by
    intro h; have := congrArg Fin.val h; simp at this
  simp [this]

lemma T_degree (hk : 7 ≤ k) (v : Fin k) :
    (T k).degree v =
      if v.val = 0 then 3
      else if v.val = 1 ∨ v.val = 3 ∨ v.val = 4 then 1
      else 2 := by
  have e0 : (T k).degree 0 = (if ((0:Fin k) : ℕ) = 0 then 3 else if ((0:Fin k) : ℕ) = 1 ∨ ((0:Fin k) : ℕ) = 3 ∨ ((0:Fin k) : ℕ) = 4 then 1 else 2) := by
    rw [T_center_degree hk, fin_val_zero']; decide
  have e1 : (T k).degree 1 = (if ((1:Fin k) : ℕ) = 0 then 3 else if ((1:Fin k) : ℕ) = 1 ∨ ((1:Fin k) : ℕ) = 3 ∨ ((1:Fin k) : ℕ) = 4 then 1 else 2) := by
    rw [T_degree_one hk, fin_val_one' hk]; decide
  have e2 : (T k).degree 2 = (if ((2:Fin k) : ℕ) = 0 then 3 else if ((2:Fin k) : ℕ) = 1 ∨ ((2:Fin k) : ℕ) = 3 ∨ ((2:Fin k) : ℕ) = 4 then 1 else 2) := by
    rw [T_degree_two hk, fin_val_two' hk]; decide
  have e3 : (T k).degree 3 = (if ((3:Fin k) : ℕ) = 0 then 3 else if ((3:Fin k) : ℕ) = 1 ∨ ((3:Fin k) : ℕ) = 3 ∨ ((3:Fin k) : ℕ) = 4 then 1 else 2) := by
    rw [T_degree_three hk, fin_val_three' hk]; decide
  have e4 : (T k).degree 4 = (if ((4:Fin k) : ℕ) = 0 then 3 else if ((4:Fin k) : ℕ) = 1 ∨ ((4:Fin k) : ℕ) = 3 ∨ ((4:Fin k) : ℕ) = 4 then 1 else 2) := by
    rw [T_degree_four hk, fin_val_four' hk]; decide
  have el : (T k).degree ⟨k-1, by omega⟩ = (if ((⟨k-1, by omega⟩:Fin k) : ℕ) = 0 then 3 else if ((⟨k-1, by omega⟩:Fin k) : ℕ) = 1 ∨ ((⟨k-1, by omega⟩:Fin k) : ℕ) = 3 ∨ ((⟨k-1, by omega⟩:Fin k) : ℕ) = 4 then 1 else 2) := by
    rw [T_degree_last hk]; simp only [Fin.val_mk]; split_ifs <;> omega
  by_cases h0 : v.val = 0
  · have : v = 0 := Fin.eq_of_val_eq (h0.trans (fin_val_zero').symm)
    rw [this]; exact e0
  · by_cases h1 : v.val = 1
    · have : v = 1 := Fin.eq_of_val_eq (h1.trans (fin_val_one' hk).symm)
      rw [this]; exact e1
    · by_cases h3 : v.val = 3
      · have : v = 3 := Fin.eq_of_val_eq (h3.trans (fin_val_three' hk).symm)
        rw [this]; exact e3
      · by_cases h4 : v.val = 4
        · have : v = 4 := Fin.eq_of_val_eq (h4.trans (fin_val_four' hk).symm)
          rw [this]; exact e4
        · by_cases h2 : v.val = 2
          · have : v = 2 := Fin.eq_of_val_eq (h2.trans (fin_val_two' hk).symm)
            rw [this]; exact e2
          · by_cases hl : v.val = k - 1
            · have : v = ⟨k - 1, by omega⟩ := Fin.eq_of_val_eq hl
              rw [this]; exact el
            · have h5 : 5 ≤ v.val := by omega
              have hi : v.val ≠ k - 1 := hl
              rw [T_degree_internal v.isLt h5 hi]
              have hv : ((⟨v.val, v.isLt⟩ : Fin k) : ℕ) = v.val := by simp
              simp [h0, h1, h2, h3, h4]

lemma T_degree_zero (hk : 7 ≤ k) : (T k).degree 0 = 3 := T_center_degree hk

lemma T_degree_le (hk : 7 ≤ k) (v : Fin k) : (T k).degree v ≤ 3 := by
  rw [T_degree hk]; split_ifs <;> omega

lemma T_degree_eq_three_iff (hk : 7 ≤ k) (v : Fin k) :
    (T k).degree v = 3 ↔ v = 0 := by
  constructor
  · intro h
    by_contra hne
    rw [T_degree hk] at h
    by_cases h0 : v.val = 0
    · exact absurd (Fin.eq_of_val_eq (h0.trans (fin_val_zero').symm)) hne
    · simp [h0] at h; split_ifs at h <;> omega
  · intro h; rw [h]; exact T_center_degree hk

lemma T_degree_eq_one_iff (hk : 7 ≤ k) (v : Fin k) :
    (T k).degree v = 1 ↔ v.val = 1 ∨ v.val = 3 ∨ v.val = 4 := by
  rw [T_degree hk]
  by_cases h0 : v.val = 0
  · simp [h0]
  · by_cases h1 : v.val = 1 ∨ v.val = 3 ∨ v.val = 4
    · simp [h0, h1]
    · simp [h0, h1]

lemma T_sum_degrees (hk : 7 ≤ k) : ∑ v : Fin k, (T k).degree v = 2 * (k - 1) := by
  classical
  have hcard : ({1, 3, 4} : Finset (Fin k)).card = 3 := by
    have h13 : (1 : Fin k) ≠ 3 := by
      intro h; have := congrArg Fin.val h; simp only [fin_val_one' hk, fin_val_three' hk] at this; omega
    have h14 : (1 : Fin k) ≠ 4 := by
      intro h; have := congrArg Fin.val h; simp only [fin_val_one' hk, fin_val_four' hk] at this; omega
    have h34 : (3 : Fin k) ≠ 4 := by
      intro h; have := congrArg Fin.val h; simp only [fin_val_three' hk, fin_val_four' hk] at this; omega
    simp [h13, h14, h34]
  have hv : ∀ v : Fin k, (T k).degree v + (if v ∈ ({1,3,4} : Finset (Fin k)) then 1 else 0)
      = 2 + (if v = 0 then 1 else 0) := by
    intro v
    rw [T_degree hk]
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff,
      fin_val_one' hk, fin_val_three' hk, fin_val_four' hk, fin_val_zero']
    split_ifs <;> omega
  have he := congrArg (fun f : Fin k → ℕ => ∑ v, f v) (funext hv)
  simp only [Finset.sum_add_distrib] at he
  have hc : (∑ v : Fin k, if v ∈ ({1,3,4} : Finset (Fin k)) then 1 else 0) = 3 := by
    rw [Finset.sum_boole]
    have hf : (Finset.univ.filter (fun v : Fin k => v ∈ ({1,3,4} : Finset (Fin k)))) = {1,3,4} := by
      ext x
      simp
    rw [hf, hcard]
    norm_num
  have hz : (∑ v : Fin k, if v = 0 then 1 else 0 : ℕ) = 1 := by simp
  simp only [hc, hz, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at he
  omega

lemma T_card_edges (hk : 7 ≤ k) : (T k).edgeFinset.card = k - 1 := by
  have hsum := SimpleGraph.sum_degrees_eq_twice_card_edges (G := T k)
  rw [T_sum_degrees hk] at hsum
  have : 2 * (k - 1) = 2 * (T k).edgeFinset.card := by omega
  omega

lemma T_reachable_from_zero (hk : 7 ≤ k) (v : Fin k) : (T k).Reachable 0 v := by
  by_cases h0 : v.val = 0
  · have : v = 0 := Fin.eq_of_val_eq (h0.trans (fin_val_zero').symm)
    rw [this]
  · by_cases h1 : v.val = 1
    · have : v = 1 := Fin.eq_of_val_eq (h1.trans (fin_val_one' hk).symm)
      rw [this]; exact (T_adj_zero_one hk).reachable
    · by_cases h2 : v.val = 2
      · have : v = 2 := Fin.eq_of_val_eq (h2.trans (fin_val_two' hk).symm)
        rw [this]; exact (T_adj_zero_two hk).reachable
      · by_cases h3 : v.val = 3
        · have : v = 3 := Fin.eq_of_val_eq (h3.trans (fin_val_three' hk).symm)
          rw [this]
          exact ((T_adj_zero_two hk).reachable).trans ((T_adj_two_three hk).reachable)
        · have hv : 4 ≤ v.val := by omega
          have main : ∀ t : ℕ, ∀ m : Fin k, k - 1 - m.val = t → 4 ≤ m.val → (T k).Reachable 0 m := by
            intro t
            induction t using Nat.strong_induction_on with
            | h t ih =>
              intro m ht h4
              by_cases hlast : m.val = k - 1
              · have hm : m = ⟨k - 1, by omega⟩ := Fin.ext hlast
                rw [hm]; exact (T_adj_zero_last hk).reachable
              · have hm1 : m.val + 1 < k := by omega
                have hp := ih (k - 1 - (m.val + 1)) (by omega) ⟨m.val + 1, hm1⟩ rfl (by change 4 ≤ m.val + 1; omega)
                exact hp.trans ((T_adj_succ_symm m.isLt h4 hm1).reachable)
          exact main _ v rfl hv

lemma T_connected (hk : 7 ≤ k) : (T k).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  exact ⟨0, T_reachable_from_zero hk⟩

lemma T_isTree (hk : 7 ≤ k) : (T k).IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  constructor
  · exact T_connected hk
  · rw [Nat.card_eq_fintype_card]
    have hcard : Fintype.card (T k).edgeSet = (T k).edgeFinset.card := by
      rw [SimpleGraph.edgeFinset_card]
    rw [hcard, T_card_edges hk, Nat.card_eq_fintype_card, T_card_verts k]
    omega

lemma T_aut_trivial_core (hk : 7 ≤ k) : ∀ (φ : (T k ≃g T k)), φ = 1 := by
  intro φ
  have map_adj : ∀ a b : Fin k, (T k).Adj a b ↔ (T k).Adj (φ a) (φ b) :=
    fun a b => φ.map_adj_iff.symm
  have deg_eq : ∀ v : Fin k, (T k).degree (φ v) = (T k).degree v :=
    fun v => (Paper13.SimpleGraph.Iso.degree_eq φ v).symm
  have hinj : Function.Injective (⇑φ) := EquivLike.injective φ
  have h0 : φ 0 = 0 :=
    (T_degree_eq_three_iff hk (φ 0)).1 (by rw [deg_eq 0]; exact T_center_degree hk)
  have hN0 : ∀ b : Fin k, (T k).Adj 0 b ↔ b.val = 1 ∨ b.val = 2 ∨ b.val = k - 1 :=
    fun b => T_mem_adj_zero hk
  have hphiN : ∀ b : Fin k, (T k).Adj 0 (φ b) ↔ (T k).Adj 0 b := by
    intro b; simpa only [h0] using (map_adj 0 b).symm
  have h1 : φ 1 = 1 := by
    have hadj : (T k).Adj 0 (φ 1) := (hphiN 1).2 (T_adj_zero_one hk)
    rcases (hN0 (φ 1)).1 hadj with h | h | h
    · exact Fin.eq_of_val_eq (h.trans (fin_val_one' hk).symm)
    · have : (T k).degree (φ 1) = 2 := by
        rw [Fin.eq_of_val_eq (h.trans (fin_val_two' hk).symm)]; exact T_degree_two hk
      have := deg_eq 1; rw [T_degree_one hk] at this; omega
    · have : (T k).degree (φ 1) = 2 := by
        rw [show φ 1 = ⟨k - 1, by omega⟩ from Fin.eq_of_val_eq h]
        exact T_degree_last hk
      have := deg_eq 1; rw [T_degree_one hk] at this; omega
  have h2 : φ 2 = 2 := by
    have hadj : (T k).Adj 0 (φ 2) := (hphiN 2).2 (T_adj_zero_two hk)
    rcases (hN0 (φ 2)).1 hadj with h | h | h
    · have : (T k).degree (φ 2) = 1 := by
        rw [Fin.eq_of_val_eq (h.trans (fin_val_one' hk).symm)]; exact T_degree_one hk
      have := deg_eq 2; rw [T_degree_two hk] at this; omega
    · exact Fin.eq_of_val_eq (h.trans (fin_val_two' hk).symm)
    · have hfeq : φ 2 = ⟨k - 1, by omega⟩ := Fin.eq_of_val_eq h
      have hphi3 : (T k).Adj (φ 2) (φ 3) := (map_adj 2 3).1 (T_adj_two_three hk)
      rw [hfeq] at hphi3
      rcases (T_mem_adj_last hk (b := φ 3)).1 hphi3 with h | h
      · have : φ 3 = 0 := Fin.eq_of_val_eq (h.trans (fin_val_zero').symm)
        have hdeg3 : (T k).degree (φ 3) = 1 := by rw [deg_eq 3]; exact T_degree_three hk
        rw [this, T_center_degree hk] at hdeg3; omega
      · have : φ 3 = ⟨k - 2, by omega⟩ := Fin.eq_of_val_eq h
        have hdeg3 : (T k).degree (φ 3) = 1 := by rw [deg_eq 3]; exact T_degree_three hk
        rw [this] at hdeg3
        have : (T k).degree (⟨k - 2, by omega⟩ : Fin k) = 2 :=
          T_degree_internal (by omega) (by omega) (by omega)
        omega
  have hlast : φ ⟨k - 1, by omega⟩ = ⟨k - 1, by omega⟩ := by
    have hadj : (T k).Adj 0 (φ ⟨k - 1, by omega⟩) := (hphiN _).2 (T_adj_zero_last hk)
    rcases (hN0 _).1 hadj with h | h | h
    · have heq : φ ⟨k - 1, by omega⟩ = φ 1 := by rw [h1]; exact Fin.ext (h.trans (fin_val_one' hk).symm)
      have heqv := congrArg Fin.val (hinj heq)
      simp only [Fin.val_mk, fin_val_one' hk] at heqv
      omega
    · have heq : φ ⟨k - 1, by omega⟩ = φ 2 := by rw [h2]; exact Fin.ext (h.trans (fin_val_two' hk).symm)
      have heqv := congrArg Fin.val (hinj heq)
      simp only [Fin.val_mk, fin_val_two' hk] at heqv
      omega
    · exact Fin.ext h
  have h3 : φ 3 = 3 := by
    have hphi : (T k).Adj (φ 2) (φ 3) := (map_adj 2 3).1 (T_adj_two_three hk)
    rw [h2] at hphi
    rcases (T_mem_adj_two hk (b := φ 3)).1 hphi with h | h
    · have : φ 3 = 0 := Fin.eq_of_val_eq (h.trans (fin_val_zero').symm)
      have hdeg := deg_eq 3
      rw [this, T_degree_three hk, T_center_degree hk] at hdeg; omega
    · exact Fin.eq_of_val_eq (h.trans (fin_val_three' hk).symm)
  have harm : ∀ t : ℕ, ∀ i : Fin k, k - 1 - i.val = t → 4 ≤ i.val → φ i = i := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro i ht h4
      by_cases hlasti : i.val = k - 1
      · have hi : i = ⟨k - 1, by omega⟩ := Fin.ext hlasti
        rw [hi]; exact hlast
      · have hi1 : i.val + 1 < k := by omega
        have hfi1 := ih (k - 1 - (i.val + 1)) (by omega) ⟨i.val + 1, hi1⟩ rfl (by change 4 ≤ i.val + 1; omega)
        have hadj := T_adj_succ_symm i.isLt h4 hi1
        have hphi := (map_adj _ _).1 hadj
        rw [hfi1] at hphi
        by_cases hlast1 : i.val + 1 = k - 1
        · have hi1e : (⟨i.val + 1, hi1⟩ : Fin k) = ⟨k - 1, by omega⟩ := Fin.ext hlast1
          rw [hi1e] at hphi
          rcases (T_mem_adj_last hk).1 hphi with h | h
          · have hzero : φ i = φ 0 := by rw [h0]; exact Fin.ext h
            have heq := congrArg Fin.val (hinj hzero)
            simp only [fin_val_zero'] at heq
            omega
          · change (φ i).val = k - 2 at h
            apply Fin.ext
            change (φ i).val = i.val
            omega
        · rcases (T_mem_adj_internal hi1 (by omega) (by omega)).1 hphi with h | h
          · change (φ i).val = i.val + 1 - 1 at h
            exact Fin.ext (h.trans (by omega))
          · have hi2 : i.val + 2 < k := by omega
            have hfi2 := ih (k - 1 - (i.val + 2)) (by omega) ⟨i.val + 2, hi2⟩ rfl (by change 4 ≤ i.val + 2; omega)
            have heq : φ i = φ ⟨i.val + 2, hi2⟩ := by rw [hfi2]; exact Fin.ext h
            have := congrArg Fin.val (hinj heq)
            simp only [Fin.val_mk] at this
            omega
  apply RelIso.ext
  intro v
  by_cases h0v : v.val = 0
  · have : v = 0 := Fin.eq_of_val_eq (h0v.trans (fin_val_zero').symm)
    rw [this, h0]; rfl
  · by_cases h1v : v.val = 1
    · have : v = 1 := Fin.eq_of_val_eq (h1v.trans (fin_val_one' hk).symm)
      rw [this, h1]; rfl
    · by_cases h2v : v.val = 2
      · have : v = 2 := Fin.eq_of_val_eq (h2v.trans (fin_val_two' hk).symm)
        rw [this, h2]; rfl
      · by_cases h3v : v.val = 3
        · have : v = 3 := Fin.eq_of_val_eq (h3v.trans (fin_val_three' hk).symm)
          rw [this, h3]; rfl
        · have hv : 4 ≤ v.val := by omega
          have := harm _ v rfl hv
          simpa using this

end TMain

/-- `T_k` is rigid: its only automorphism is the identity. -/
lemma T_aut_trivial (k : ℕ) (hk : 7 ≤ k) : ∀ (φ : (T k ≃g T k)), φ = 1 := by
  letI := neZero_of_seven_le hk
  exact T_aut_trivial_core hk

/-- `T_k` is a tree (public form without `NeZero`). -/
lemma T_isTree' (k : ℕ) (hk : 7 ≤ k) : (T k).IsTree := by
  letI := neZero_of_seven_le hk
  exact T_isTree hk

/-- `T_k` is connected (public form without `NeZero`). -/
lemma T_connected' (k : ℕ) (hk : 7 ≤ k) : (T k).Connected := by
  letI := neZero_of_seven_le hk
  exact T_connected hk

/-- Degree of the center of `T_k` (public form). -/
lemma T_center_degree' (k : ℕ) (hk : 7 ≤ k) : (T k).degree (⟨0, by omega⟩ : Fin k) = 3 := by
  letI := neZero_of_seven_le hk
  exact T_center_degree hk

end Paper13
