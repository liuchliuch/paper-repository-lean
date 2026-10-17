import Paper08.Enumeration
import Paper08.Connected
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.GetD

/-! # Executable connected-support candidates without a global powerset

Sorted neighbour lookup replaces the choice-based `Finset.equivFin` used in
the existence proof. Supports are decoded from finite ordered forests, and
only their own subsets are enumerated.
-/
open scoped BigOperators
namespace Paper08.EfficientSupports

def next {m : ℕ} (N : Fin m → Finset (Fin m)) (d : ℕ)
    (u : Fin m) (i : Fin d) : Fin m :=
  ((N u).sort (· ≤ ·)).getD i.val u

theorem next_covers {m d : ℕ} (N : Fin m → Finset (Fin m))
    (hdeg : ∀ u, (N u).card ≤ d) (u v : Fin m) (hv : v ∈ N u) :
    ∃ i : Fin d, next N d u i = v := by
  obtain ⟨i, hi, hval⟩ := List.mem_iff_getElem.mp ((Finset.mem_sort (· ≤ ·)).mpr hv)
  have hid : i < d := by rw [Finset.length_sort] at hi; exact hi.trans_le (hdeg u)
  refine ⟨⟨i, hid⟩, ?_⟩
  exact (List.getD_eq_getElem _ _ hi).trans hval

def supports {m : ℕ} (N : Fin m → Finset (Fin m)) (d s : ℕ) :
    Finset (Finset (Fin m)) :=
  (Finset.range s).biUnion (Enumeration.candidateSets (next N d))

/-- Subsets of candidates with a fixed forest size. -/
def candidatePairs {m : ℕ} (N : Fin m → Finset (Fin m)) (d k : ℕ) :
    Finset (Finset (Fin m) × Finset (Fin m)) :=
  (Enumeration.candidateSets (next N d) k).biUnion fun A => A.powerset.image (fun B => (A, B))

/-- Each candidate contributes its own power set, never the global factor power set. -/
def supportPairs {m : ℕ} (N : Fin m → Finset (Fin m)) (d s : ℕ) :
    Finset (Finset (Fin m) × Finset (Fin m)) :=
  (Finset.range s).biUnion (candidatePairs N d)

theorem contains_connected {m d s : ℕ} (N : Fin m → Finset (Fin m))
    (G : SimpleGraph (Fin m)) (hdeg : ∀ u, (N u).card ≤ d)
    (hN : ∀ u v, G.Adj u v → v ∈ N u)
    (A : Finset (Fin m)) (hne : A.Nonempty) (hs : A.card ≤ s)
    (hconn : (G.induce (A : Set (Fin m))).Connected) : A ∈ supports N d s := by
  have hcandidate := Enumeration.connectedSets_subset_candidates G (next N d)
    (fun u v huv => next_covers N hdeg u v (hN u v huv)) A.card
  have hA : A ∈ Enumeration.connectedSets G A.card := by
    classical
    simp [Enumeration.connectedSets, hconn]
  apply Finset.mem_biUnion.mpr
  exact ⟨A.card - 1, Finset.mem_range.mpr (by have := Finset.card_pos.mpr hne; omega),
    hcandidate hA⟩

theorem labeling_numNodes {d : ℕ} (shape : Tree Unit) (t : Tree (Fin d))
    (ht : t ∈ Enumeration.labelings d shape) : t.numNodes = shape.numNodes := by
  induction shape generalizing t with
  | nil =>
    have h : t = Tree.nil := by simpa [Enumeration.labelings] using ht
    subst t
    rfl
  | node u l r hl hr =>
    simp only [Enumeration.labelings, Finset.mem_map, Finset.mem_product,
      Finset.mem_univ, true_and] at ht
    obtain ⟨⟨i, tl, tr⟩, ⟨htl, htr⟩, rfl⟩ := ht
    simpa only [Enumeration.nodeEmbedding, Function.Embedding.coeFn_mk, Tree.numNodes]
      using congrArg₂ (fun a b : ℕ => a + b + 1) (hl tl htl) (hr tr htr)

theorem forest_numNodes {d k : ℕ} {t : Tree (Fin d)}
    (ht : t ∈ Enumeration.forestCodes d k) : t.numNodes = k := by
  obtain ⟨shape, hs, ht⟩ := Finset.mem_biUnion.mp ht
  exact (labeling_numNodes shape t ht).trans (Tree.mem_treesOfNumNodesEq.mp hs)

theorem forest_card_le {m d : ℕ} (f : Fin m → Fin d → Fin m) (root : Fin m)
    (t : Tree (Fin d)) : (Enumeration.forestVertices f root t).card ≤ t.numNodes := by
  induction t generalizing root with
  | nil => simp [Enumeration.forestVertices]
  | node i l r hl hr =>
    calc
      _ ≤ 1 + ((Enumeration.forestVertices f (f root i) l).card +
          (Enumeration.forestVertices f root r).card) := by
        have h₁ := Finset.card_insert_le (f root i)
          (Enumeration.forestVertices f (f root i) l ∪ Enumeration.forestVertices f root r)
        have h₂ := Finset.card_union_le (Enumeration.forestVertices f (f root i) l)
          (Enumeration.forestVertices f root r)
        change (insert (f root i)
          (Enumeration.forestVertices f (f root i) l ∪ Enumeration.forestVertices f root r)).card ≤ _
        omega
      _ ≤ l.numNodes + r.numNodes + 1 := by have := hl (f root i); have := hr root; omega
      _ = _ := rfl

theorem candidate_card_le {m d k : ℕ} (f : Fin m → Fin d → Fin m)
    {A : Finset (Fin m)} (hA : A ∈ Enumeration.candidateSets f k) : A.card ≤ k + 1 := by
  obtain ⟨⟨root, t⟩, hmem, rfl⟩ := Finset.mem_image.mp hA
  have ht := forest_numNodes (Finset.mem_product.mp hmem).2
  change t.numNodes = k at ht
  change (insert root (Enumeration.forestVertices f root t)).card ≤ k + 1
  have h₁ := Finset.card_insert_le root (Enumeration.forestVertices f root t)
  have h₂ := forest_card_le f root t
  omega

theorem support_card_le {m d s : ℕ} (N : Fin m → Finset (Fin m))
    {A : Finset (Fin m)} (hA : A ∈ supports N d s) : A.card ≤ s := by
  obtain ⟨k, hk, hA⟩ := Finset.mem_biUnion.mp hA
  exact (candidate_card_le _ hA).trans (by have := Finset.mem_range.mp hk; omega)

theorem mem_supportPairs {m d s : ℕ} (N : Fin m → Finset (Fin m))
    (A B : Finset (Fin m)) :
    (A, B) ∈ supportPairs N d s ↔ A ∈ supports N d s ∧ B ⊆ A := by
  simp only [supportPairs, candidatePairs, supports, Finset.mem_biUnion,
    Finset.mem_image, Finset.mem_powerset, Prod.mk.injEq]
  constructor
  · rintro ⟨k, hk, C, hC, D, hD, hCA, hDB⟩
    subst C
    subst D
    exact ⟨⟨k, hk, hC⟩, hD⟩
  · rintro ⟨⟨k, hk, hA⟩, hB⟩
    exact ⟨k, hk, A, hA, B, hB, rfl, rfl⟩

theorem candidatePairs_count {m d k : ℕ} (N : Fin m → Finset (Fin m)) :
    (candidatePairs N d k).card ≤ m * (4 * d) ^ k * 2 ^ (k + 1) := by
  calc
    _ ≤ ∑ A ∈ Enumeration.candidateSets (next N d) k,
        (A.powerset.image (fun B => (A, B))).card := Finset.card_biUnion_le
    _ ≤ ∑ _A ∈ Enumeration.candidateSets (next N d) k, 2 ^ (k + 1) := by
      apply Finset.sum_le_sum
      intro A hA
      exact Finset.card_image_le.trans ((by rw [Finset.card_powerset] :
        A.powerset.card = 2 ^ A.card).le.trans
          (Nat.pow_le_pow_right (by omega) (candidate_card_le _ hA)))
    _ = (Enumeration.candidateSets (next N d) k).card * 2 ^ (k + 1) := by simp
    _ ≤ m * (4 * d) ^ k * 2 ^ (k + 1) := by
      apply Nat.mul_le_mul_right
      simpa only [Fintype.card_fin] using Enumeration.card_candidateSets_le (next N d) k

/-- Actual decoded support/subset pairs obey the exponential-in-order bound. -/
theorem supportPairs_count {m d s : ℕ} (N : Fin m → Finset (Fin m)) (hd : 1 ≤ d) :
    (supportPairs N d s).card ≤ m * (8 * d) ^ s := by
  calc
    _ ≤ ∑ k ∈ Finset.range s, (candidatePairs N d k).card := Finset.card_biUnion_le
    _ ≤ ∑ k ∈ Finset.range s, m * (4 * d) ^ k * 2 ^ (k + 1) :=
      Finset.sum_le_sum fun k _ => candidatePairs_count N
    _ = m * (2 * ∑ k ∈ Finset.range s, (8 * d) ^ k) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      have hp : (4 * d) ^ k * 2 ^ k = (8 * d) ^ k := by
        rw [← mul_pow]
        congr 1
        omega
      calc
        _ = m * ((4 * d) ^ k * 2 ^ k) * 2 := by rw [pow_succ]; ring
        _ = m * (2 * (8 * d) ^ k) := by rw [hp]; ring
    _ ≤ m * (8 * d) ^ s := Nat.mul_le_mul_left _
      (Connected.two_mul_sum_range_pow_le _ s (by omega))

end Paper08.EfficientSupports
