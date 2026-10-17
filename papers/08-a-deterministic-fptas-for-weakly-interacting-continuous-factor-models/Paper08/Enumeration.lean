import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

/-!
# Enumeration of connected vertex sets

A binary tree encodes an ordered forest by the first-child/next-sibling convention.
Each node stores one of at most `d` neighbour choices. Starting from a root vertex,
its decoded vertex set therefore has an encoding using `a-1` nodes for every connected
set of size `a`. Catalan counting gives the bound `m (4d)^(a-1)`.
-/
noncomputable section
open scoped BigOperators
namespace Paper08.Enumeration

variable {V : Type*} [DecidableEq V]

/-- Vertices visited by the ordered forest, excluding its external root. -/
def forestVertices {d : ℕ} (next : V → Fin d → V) (root : V) : Tree (Fin d) → Finset V
  | .nil => ∅
  | .node i l r => insert (next root i)
      (forestVertices next (next root i) l ∪ forestVertices next root r)

/-- Include the external root in the visited set. -/
def vertices {d : ℕ} (next : V → Fin d → V) (root : V) (t : Tree (Fin d)) : Finset V :=
  insert root (forestVertices next root t)

@[simp] lemma vertices_nil {d : ℕ} (next : V → Fin d → V) (root : V) :
    vertices next root .nil = {root} := rfl

/-- Attach one leaf at any already visited vertex. This is the step that makes
the forest coding cover arbitrary connected sets rather than only paths. -/
lemma attach_leaf {d : ℕ} (next : V → Fin d → V) (root : V) (t : Tree (Fin d))
    (u : V) (hu : u ∈ vertices next root t) (i : Fin d) :
    ∃ t' : Tree (Fin d),
      t'.numNodes = t.numNodes + 1 ∧
      vertices next root t' = insert (next u i) (vertices next root t) := by
  induction t generalizing root with
  | nil =>
    have hur : u = root := by simpa using hu
    subst u
    refine ⟨.node i .nil .nil, by simp, ?_⟩
    ext v
    simp only [vertices, forestVertices, Finset.mem_insert, Finset.notMem_empty, Finset.mem_union]
    tauto
  | node j l r ihl ihr =>
    by_cases hur : u = root
    · subst u
      refine ⟨.node i .nil (.node j l r), by simp, ?_⟩
      simp [vertices, forestVertices, Finset.insert_comm]
    · have hmem : u ∈ vertices next (next root j) l ∨ u ∈ vertices next root r := by
        simp only [vertices, forestVertices, Finset.mem_insert, Finset.mem_union] at hu ⊢
        tauto
      rcases hmem with hul | hur'
      · obtain ⟨l', hsize, hverts⟩ := ihl (next root j) hul
        refine ⟨.node j l' r, by simp; omega, ?_⟩
        have hf : insert (next root j) (forestVertices next (next root j) l') =
            insert (next u i) (insert (next root j) (forestVertices next (next root j) l)) := hverts
        simp only [vertices, forestVertices]
        ext v
        have hm := Finset.ext_iff.mp hf v
        simp only [Finset.mem_insert, Finset.mem_union] at hm ⊢
        tauto
      · obtain ⟨r', hsize, hverts⟩ := ihr root hur'
        refine ⟨.node j l r', by simp; omega, ?_⟩
        have hf : insert root (forestVertices next root r') =
            insert (next u i) (insert root (forestVertices next root r)) := hverts
        simp only [vertices, forestVertices]
        ext v
        have hm := Finset.ext_iff.mp hf v
        simp only [Finset.mem_insert, Finset.mem_union] at hm ⊢
        tauto

/-- A path from a set to its complement contains an edge crossing its boundary. -/
lemma reachable_boundary (G : SimpleGraph V) (P : V → Prop) {x y : V}
    (hxy : G.Reachable x y) (hx : P x) (hy : ¬ P y) :
    ∃ u v, P u ∧ ¬ P v ∧ G.Adj u v := by
  obtain ⟨p⟩ := hxy
  induction p with
  | nil => exact (hy hx).elim
  | @cons u v w huv p ih =>
    by_cases hv : P v
    · exact ih hv hy
    · exact ⟨u, v, hx, hv, huv⟩

/-- A proper nonempty subset of a connected induced graph has an outgoing edge. -/
lemma connected_boundary (G : SimpleGraph V) (A B : Finset V)
    (hconn : (G.induce (A : Set V)).Connected) (hsub : B ⊆ A)
    (hne : B.Nonempty) (hproper : B ≠ A) :
    ∃ u ∈ B, ∃ v ∈ A, v ∉ B ∧ G.Adj u v := by
  obtain ⟨x, hx⟩ := hne
  have hnot : ¬ A ⊆ B := fun h => hproper (Finset.Subset.antisymm hsub h)
  obtain ⟨y, hyA, hyB⟩ := Finset.not_subset.mp hnot
  obtain ⟨u, v, hu, hv, huv⟩ := reachable_boundary (G.induce (A : Set V))
    (fun v => v.val ∈ B) (hconn.preconnected ⟨x, hsub hx⟩ ⟨y, hyA⟩) hx hyB
  exact ⟨u.val, hu, v.val, v.property, hv, huv⟩

/-- Every finite connected set has a forest code with exactly one neighbour
choice per vertex other than its root. -/
lemma exists_forest_code {d : ℕ} (G : SimpleGraph V) (A : Finset V)
    (hconn : (G.induce (A : Set V)).Connected) (root : V) (hroot : root ∈ A)
    (next : V → Fin d → V)
    (hnext : ∀ u v, G.Adj u v → ∃ i, next u i = v) :
    ∃ t : Tree (Fin d), t.numNodes = A.card - 1 ∧ vertices next root t = A := by
  have grow : ∀ n : ℕ, ∀ t : Tree (Fin d),
      vertices next root t ⊆ A → (vertices next root t).card + n = A.card →
      ∃ t' : Tree (Fin d), t'.numNodes = t.numNodes + n ∧ vertices next root t' = A := by
    intro n
    induction n with
    | zero =>
      intro t hsub hcard
      refine ⟨t, by simp, ?_⟩
      exact Finset.eq_of_subset_of_card_le hsub (by omega)
    | succ n ih =>
      intro t hsub hcard
      have hne : (vertices next root t).Nonempty := ⟨root, Finset.mem_insert_self _ _⟩
      have hproper : vertices next root t ≠ A := by
        intro h
        rw [h] at hcard
        omega
      obtain ⟨u, hu, v, hvA, hvB, huv⟩ := connected_boundary G A
        (vertices next root t) hconn hsub hne hproper
      obtain ⟨i, hi⟩ := hnext u v huv
      obtain ⟨t₁, hsize₁, hverts₁⟩ := attach_leaf next root t u hu i
      rw [hi] at hverts₁
      have hsub₁ : vertices next root t₁ ⊆ A := by
        rw [hverts₁]
        exact Finset.insert_subset hvA hsub
      have hcard₁ : (vertices next root t₁).card + n = A.card := by
        rw [hverts₁, Finset.card_insert_of_notMem hvB]
        omega
      obtain ⟨t₂, hsize₂, hverts₂⟩ := ih t₁ hsub₁ hcard₁
      exact ⟨t₂, by omega, hverts₂⟩
  obtain ⟨t, hsize, hverts⟩ := grow (A.card - 1) .nil
    (by simpa using hroot) (by
      simp only [vertices_nil, Finset.card_singleton]
      have := Finset.card_pos.mpr ⟨root, hroot⟩
      omega)
  exact ⟨t, by simpa using hsize, hverts⟩

/-- A padded neighbour lookup table, with exactly `d` available indices. -/
def neighbourStep (N : V → Finset V) (d : ℕ) (u : V) (i : Fin d) : V :=
  if h : i.val < (N u).card then ((N u).equivFin.symm ⟨i.val, h⟩).val else u

lemma neighbourStep_covers (N : V → Finset V) (d : ℕ)
    (hdeg : ∀ u, (N u).card ≤ d) (u v : V) (hv : v ∈ N u) :
    ∃ i : Fin d, neighbourStep N d u i = v := by
  let j := (N u).equivFin ⟨v, hv⟩
  have hj : j.val < d := lt_of_lt_of_le j.isLt (hdeg u)
  refine ⟨⟨j.val, hj⟩, ?_⟩
  simp only [neighbourStep, dif_pos j.isLt]
  exact congrArg Subtype.val ((N u).equivFin.symm_apply_apply ⟨v, hv⟩)

/-- The constructor is injective, so counting labelled forest nodes loses no factors. -/
def nodeEmbedding (d : ℕ) : (Fin d × (Tree (Fin d) × Tree (Fin d))) ↪ Tree (Fin d) where
  toFun x := .node x.1 x.2.1 x.2.2
  inj' := by
    rintro ⟨i, l, r⟩ ⟨j, l', r'⟩ h
    simpa using h

/-- Enumerate all neighbour labelings of one ordered forest shape. -/
def labelings (d : ℕ) : Tree Unit → Finset (Tree (Fin d))
  | .nil => {.nil}
  | .node _ l r =>
    ((Finset.univ : Finset (Fin d)) ×ˢ (labelings d l ×ˢ labelings d r)).map (nodeEmbedding d)

lemma mem_labelings_shape {d : ℕ} (t : Tree (Fin d)) :
    t ∈ labelings d (t.map (fun _ => ())) := by
  induction t with
  | nil => simp [Tree.map, labelings]
  | node i l r hl hr =>
    simp only [Tree.map, labelings, Finset.mem_map]
    exact ⟨⟨i, l, r⟩, by simp [hl, hr], rfl⟩

lemma numNodes_map {α β : Type*} (f : α → β) (t : Tree α) :
    (t.map f).numNodes = t.numNodes := by
  induction t <;> simp [Tree.map, *]

lemma card_labelings (d : ℕ) (t : Tree Unit) :
    (labelings d t).card = d ^ t.numNodes := by
  induction t with
  | nil => simp [labelings]
  | node i l r hl hr =>
    simp only [labelings, Finset.card_map, Finset.card_product, Finset.card_univ,
      Fintype.card_fin, hl, hr, Tree.numNodes, pow_add, pow_succ]
    ring

/-- An actual finite list of all forest encodings with `n` edges. -/
def forestCodes (d n : ℕ) : Finset (Tree (Fin d)) :=
  (Tree.treesOfNumNodesEq n).biUnion (labelings d)

lemma mem_forestCodes {d n : ℕ} (t : Tree (Fin d)) (ht : t.numNodes = n) :
    t ∈ forestCodes d n := by
  apply Finset.mem_biUnion.mpr
  refine ⟨t.map (fun _ => ()), ?_, mem_labelings_shape t⟩
  rw [Tree.mem_treesOfNumNodesEq, numNodes_map, ht]

lemma catalan_le_four_pow (n : ℕ) : catalan n ≤ 4 ^ n := by
  calc
    catalan n = n.centralBinom / (n + 1) := catalan_eq_centralBinom_div n
    _ ≤ n.centralBinom := Nat.div_le_self _ _
    _ ≤ 2 ^ (2 * n) := Nat.choose_le_two_pow _ _
    _ = 4 ^ n := by rw [pow_mul]; norm_num

/-- The candidate count is Catalan times `d` to the number of edges. -/
lemma card_forestCodes_le (d n : ℕ) :
    (forestCodes d n).card ≤ (4 * d) ^ n := by
  calc
    (forestCodes d n).card ≤
        ∑ t ∈ Tree.treesOfNumNodesEq n, (labelings d t).card := Finset.card_biUnion_le
    _ = (Tree.treesOfNumNodesEq n).card * d ^ n := by
      rw [← Finset.sum_const_nat]
      intro t ht
      rw [card_labelings, Tree.mem_treesOfNumNodesEq.mp ht]
    _ = catalan n * d ^ n := by rw [Tree.treesOfNumNodesEq_card_eq_catalan]
    _ ≤ 4 ^ n * d ^ n := Nat.mul_le_mul_right _ (catalan_le_four_pow n)
    _ = (4 * d) ^ n := (mul_pow _ _ _).symm

/-- The finite family of all connected vertex sets of one cardinality. -/
def connectedSets [Fintype V] (G : SimpleGraph V) (a : ℕ) : Finset (Finset V) := by
  classical
  exact Finset.univ.powerset.filter fun A =>
    A.card = a ∧ (G.induce (A : Set V)).Connected

/-- Decode all roots and all ordered-forest candidates. Invalid or repeated-vertex
encodings may occur; filtering and removing duplicates can only reduce the count. -/
def candidateSets [Fintype V] {d : ℕ} (next : V → Fin d → V) (n : ℕ) : Finset (Finset V) :=
  ((Finset.univ : Finset V) ×ˢ forestCodes d n).image fun x => vertices next x.1 x.2

lemma card_candidateSets_le [Fintype V] {d : ℕ} (next : V → Fin d → V) (n : ℕ) :
    (candidateSets next n).card ≤ Fintype.card V * (4 * d) ^ n := by
  calc
    (candidateSets next n).card ≤
        ((Finset.univ : Finset V) ×ˢ forestCodes d n).card := Finset.card_image_le
    _ = Fintype.card V * (forestCodes d n).card := by simp
    _ ≤ Fintype.card V * (4 * d) ^ n := Nat.mul_le_mul_left _ (card_forestCodes_le d n)

/-- Every connected vertex set occurs in the finite enumeration. -/
lemma connectedSets_subset_candidates [Fintype V] {d : ℕ} (G : SimpleGraph V)
    (next : V → Fin d → V) (hnext : ∀ u v, G.Adj u v → ∃ i, next u i = v) (a : ℕ) :
    connectedSets G a ⊆ candidateSets next (a - 1) := by
  classical
  intro A hA
  have hmem := (Finset.mem_filter.mp hA).2
  have hnonempty : A.Nonempty := by
    obtain ⟨r⟩ := hmem.2.nonempty
    exact ⟨r.val, r.property⟩
  obtain ⟨root, hroot⟩ := hnonempty
  obtain ⟨t, hsize, hverts⟩ := exists_forest_code G A hmem.2 root hroot next hnext
  apply Finset.mem_image.mpr
  refine ⟨⟨root, t⟩, ?_, hverts⟩
  simp only [Finset.mem_product, Finset.mem_univ, true_and]
  exact mem_forestCodes t (by simpa only [hmem.1] using hsize)

/-- The connected-set count in Section 2, proved from graph connectivity and a
maximum degree bound, without assuming an enumeration certificate. -/
lemma card_connectedSets_le [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (D a : ℕ) (hdeg : ∀ v, G.degree v ≤ D) :
    (connectedSets G a).card ≤ Fintype.card V * (4 * max 1 D) ^ (a - 1) := by
  let next := neighbourStep (fun u => G.neighborFinset u) (max 1 D)
  have hnext : ∀ u v, G.Adj u v → ∃ i, next u i = v := by
    intro u v huv
    exact neighbourStep_covers (fun u => G.neighborFinset u) (max 1 D)
      (fun u => (hdeg u).trans (le_max_right _ _)) u v (by simpa using huv)
  exact (Finset.card_le_card (connectedSets_subset_candidates G next hnext a)).trans
    (card_candidateSets_le next (a - 1))

end Paper08.Enumeration
