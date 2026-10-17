import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# Graph-theoretic core of *Copies of K_{4,4} in K_{3,5}-free graphs*

Predicates used throughout the paper, and a complete proof of
**Lemma 2 (Upper bound)**:

> Every `n`-vertex `K_{3,5}`-free graph `G` satisfies
> `N(K_{4,4}, G) ≤ (1/8) * (n choose 3)`.
-/

open Finset

namespace K44K35Free

variable {V : Type*}

/-! ## Common neighbourhoods and `K_{3,5}`-freeness -/

/-- Common neighbourhood as a set `Γ_G(X) = ⋂_{x ∈ X} N_G(x)`. -/
def commonNeighborsSet (G : SimpleGraph V) (X : Finset V) : Set V :=
  {v | ∀ x ∈ X, G.Adj v x}

theorem mem_commonNeighborsSet {G : SimpleGraph V} {X : Finset V} {v : V} :
    v ∈ commonNeighborsSet G X ↔ ∀ x ∈ X, G.Adj v x :=
  Iff.rfl

/-- Common neighbourhood as a `Finset` (requires a finite vertex type). -/
noncomputable def commonNeighbors [Fintype V] (G : SimpleGraph V) (X : Finset V) : Finset V :=
  (commonNeighborsSet G X).toFinite.toFinset

theorem mem_commonNeighbors [Fintype V] {G : SimpleGraph V} {X : Finset V} {v : V} :
    v ∈ commonNeighbors G X ↔ ∀ x ∈ X, G.Adj v x := by
  unfold commonNeighbors commonNeighborsSet
  exact Set.Finite.mem_toFinset _

/-- `G` is `K_{3,5}`-free iff every triple has at most four common neighbours. -/
def IsK35Free [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ X : Finset V, X.card = 3 → (commonNeighbors G X).card ≤ 4

/-! ## `K_{4,4}` configurations -/

/-- Predicate: ordered sides `A, B` form a complete bipartite `K_{4,4}`. -/
def IsK44Pair (G : SimpleGraph V) (A B : Finset V) : Prop :=
  A.card = 4 ∧ B.card = 4 ∧ Disjoint A B ∧ ∀ ⦃a b⦄, a ∈ A → b ∈ B → G.Adj a b

/-- The finite set of oriented `K_{4,4}` side-pairs. -/
noncomputable def orientedK44 [Fintype V] (G : SimpleGraph V) :
    Finset (Finset V × Finset V) :=
  ({p | IsK44Pair G p.1 p.2} : Set (Finset V × Finset V)).toFinite.toFinset

/-- Number of oriented `K_{4,4}` side-pairs.  Each unlabelled copy of `K_{4,4}`
contributes exactly two orientations. -/
noncomputable def numOrientedK44 [Fintype V] (G : SimpleGraph V) : ℕ :=
  (orientedK44 G).card

/-- Unlabelled copy count `N(K_{4,4}, G)`. -/
noncomputable def numK44 [Fintype V] (G : SimpleGraph V) : ℕ :=
  numOrientedK44 G / 2

theorem numK44_eq [Fintype V] (G : SimpleGraph V) :
    numK44 G = numOrientedK44 G / 2 := rfl

theorem mem_orientedK44 [Fintype V] {G : SimpleGraph V} {A B : Finset V} :
    (A, B) ∈ orientedK44 G ↔ IsK44Pair G A B := by
  unfold orientedK44
  exact Set.Finite.mem_toFinset _

/-! ## Side-triples -/

/-- The `3`-subsets of a side of a `K_{4,4}`. -/
def sideTriples (A : Finset V) : Finset (Finset V) := A.powersetCard 3

theorem mem_sideTriples {A T : Finset V} :
    T ∈ sideTriples A ↔ T ⊆ A ∧ T.card = 3 :=
  mem_powersetCard

theorem card_sideTriples {A : Finset V} (hA : A.card = 4) :
    (sideTriples A).card = 4 := by
  have h : (4 : ℕ).choose 3 = 4 := by norm_num
  rw [sideTriples, card_powersetCard, hA, h]

/-- `T ∪ (A \ T) = A` when `T ⊆ A`. -/
theorem union_sdiff_eq_of_subset {A T : Finset V} [DecidableEq V] (h : T ⊆ A) :
    T ∪ (A \ T) = A :=
  union_sdiff_of_subset h

/-! ## Side-triples under `K_{3,5}`-freeness -/

/-- The opposite side of a `K_{4,4}` equals the common neighbourhood of any
of its side-triples. -/
theorem opposite_eq_commonNeighbors [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hfree : IsK35Free G)
    {A B : Finset V} (h : IsK44Pair G A B) {T : Finset V}
    (hT : T ⊆ A) (h3 : T.card = 3) :
    B = commonNeighbors G T := by
  have hB4 : B.card = 4 := h.2.1
  have hBsub : B ⊆ commonNeighbors G T := by
    intro b hb
    refine mem_commonNeighbors.2 ?_
    intro x hx
    have hAdj : G.Adj x b := h.2.2.2 (hT hx) hb
    exact hAdj.symm
  have hΓ : (commonNeighbors G T).card ≤ 4 := hfree T h3
  apply Subset.antisymm hBsub
  intro v hv
  by_contra hnot
  have hss : B ⊂ commonNeighbors G T := ⟨hBsub, fun habs => hnot (habs hv)⟩
  have hlt := card_lt_card hss
  omega

/-- A side-triple determines the whole ordered pair. -/
theorem sideTriple_determines_pair [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hfree : IsK35Free G)
    {A B A' B' : Finset V} {T : Finset V}
    (h : IsK44Pair G A B) (h' : IsK44Pair G A' B')
    (hT : T ⊆ A) (h3 : T.card = 3) (hT' : T ⊆ A') :
    A = A' ∧ B = B' := by
  have hB : B = commonNeighbors G T := opposite_eq_commonNeighbors hfree h hT h3
  have hB' : B' = commonNeighbors G T := opposite_eq_commonNeighbors hfree h' hT' h3
  have hBB' : B = B' := by rw [hB, hB']
  have hex : ∃ Y : Finset V, Y ⊆ B ∧ Y.card = 3 := by
    have hBne : B.Nonempty := by
      rw [← card_pos, h.2.1]; norm_num
    obtain ⟨b1, hb1⟩ := hBne
    refine ⟨B \ {b1}, sdiff_subset, ?_⟩
    have h1 : (B \ {b1}).card = B.card - ({b1} : Finset V).card :=
      card_sdiff_of_subset (singleton_subset_iff.2 hb1)
    rw [h1, h.2.1, card_singleton]
  obtain ⟨Y, hYsub, hY3⟩ := hex
  have hAΓ : A ⊆ commonNeighbors G Y := by
    intro v hv
    refine mem_commonNeighbors.2 ?_
    intro x hx
    have hAdj : G.Adj v x := h.2.2.2 hv (hYsub hx)
    exact hAdj
  have hA'Γ : A' ⊆ commonNeighbors G Y := by
    intro v hv
    refine mem_commonNeighbors.2 ?_
    intro x hx
    have hAdj : G.Adj v x := h'.2.2.2 hv (by rw [← hBB']; exact hYsub hx)
    exact hAdj
  have hΓ4 : (commonNeighbors G Y).card ≤ 4 := hfree Y hY3
  have hTΓ : T ⊆ commonNeighbors G Y := Subset.trans hT hAΓ
  have hΓT : (commonNeighbors G Y \ T).card ≤ 1 := by
    have hsd := card_sdiff_of_subset hTΓ
    rw [h3] at hsd
    omega
  have hcardA : (A \ T).card = 1 := by
    have hdis : Disjoint T (A \ T) := disjoint_sdiff
    have hU : (T ∪ (A \ T)).card = T.card + (A \ T).card :=
      card_union_of_disjoint hdis
    rw [union_sdiff_eq_of_subset hT, h.1, h3] at hU
    omega
  have hcardA' : (A' \ T).card = 1 := by
    have hdis : Disjoint T (A' \ T) := disjoint_sdiff
    have hU : (T ∪ (A' \ T)).card = T.card + (A' \ T).card :=
      card_union_of_disjoint hdis
    rw [union_sdiff_eq_of_subset hT', h'.1, h3] at hU
    omega
  have hAin : A \ T ⊆ commonNeighbors G Y \ T := by
    intro v hv
    exact mem_sdiff.2 ⟨hAΓ (mem_sdiff.1 hv).1, (mem_sdiff.1 hv).2⟩
  have hA'in : A' \ T ⊆ commonNeighbors G Y \ T := by
    intro v hv
    exact mem_sdiff.2 ⟨hA'Γ (mem_sdiff.1 hv).1, (mem_sdiff.1 hv).2⟩
  have hATeq : A \ T = A' \ T := by
    by_contra hne
    obtain ⟨u, hu⟩ := card_eq_one.1 hcardA
    obtain ⟨u', hu'⟩ := card_eq_one.1 hcardA'
    have huΓ : u ∈ commonNeighbors G Y \ T := hAin (by rw [hu]; exact mem_singleton_self _)
    have hu'Γ : u' ∈ commonNeighbors G Y \ T := hA'in (by rw [hu']; exact mem_singleton_self _)
    have huu' : u ≠ u' := by
      rintro rfl
      apply hne
      rw [hu, hu']
    have h2 : (commonNeighbors G Y \ T).card ≥ 2 := by
      have hsub : ({u, u'} : Finset V) ⊆ commonNeighbors G Y \ T := by
        intro x hx
        rcases mem_insert.1 hx with rfl | hx
        · exact huΓ
        · rcases mem_singleton.1 hx with rfl
          · exact hu'Γ
      have hle := card_le_card hsub
      rw [card_insert_of_notMem (by simpa using huu'), card_singleton] at hle
      omega
    omega
  refine ⟨?_, hBB'⟩
  rw [← union_sdiff_eq_of_subset hT, ← union_sdiff_eq_of_subset hT', hATeq]

/-! ## Lemma 2 (Upper bound) -/

theorem card_leftSideTriples [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hfree : IsK35Free G) :
    ((orientedK44 G).biUnion (fun p => sideTriples p.1)).card
      = 4 * numOrientedK44 G := by
  classical
  have hpair : ∀ p ∈ orientedK44 G, (sideTriples (p.1 : Finset V)).card = 4 := by
    rintro ⟨A, B⟩ hp
    exact card_sideTriples (mem_orientedK44.1 hp).1
  have hinj : (orientedK44 G).toSet.PairwiseDisjoint
      (fun p => sideTriples (p.1 : Finset V)) := by
    intro p hp p' hp' hne
    show Disjoint (sideTriples p.1) (sideTriples p'.1)
    rw [Finset.disjoint_left]
    intro T hT hT'
    rcases p with ⟨A, B⟩
    rcases p' with ⟨A', B'⟩
    rcases mem_sideTriples.1 hT with ⟨hTs, h3⟩
    rcases mem_sideTriples.1 hT' with ⟨hTs', h3'⟩
    obtain ⟨rfl, rfl⟩ := sideTriple_determines_pair hfree
      (mem_orientedK44.1 hp) (mem_orientedK44.1 hp') hTs h3 hTs'
    exact hne rfl
  rw [card_biUnion hinj, sum_congr rfl (fun p hp => hpair p hp), sum_const]
  simp only [numOrientedK44, nsmul_eq_mul, Nat.mul_comm]
  rfl

/-- **Lemma 2 (Upper bound).**
Every `n`-vertex `K_{3,5}`-free graph `G` satisfies
`N(K_{4,4}, G) ≤ (1/8) * (n choose 3)`. -/
theorem lemma_2_upper_bound [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hfree : IsK35Free G) :
    8 * numK44 G ≤ (Fintype.card V).choose 3 := by
  classical
  set S : Finset (Finset V) := (orientedK44 G).biUnion (fun p => sideTriples p.1) with hS
  have hsub : S ⊆ (univ.powersetCard 3 : Finset (Finset V)) := by
    intro T hT
    simp only [hS, mem_biUnion, mem_sideTriples] at hT
    obtain ⟨⟨A, B⟩, _, hTs, h3⟩ := hT
    exact mem_powersetCard.2 ⟨subset_univ T, h3⟩
  have hcard_pow :
      ((univ.powersetCard 3 : Finset (Finset V))).card = (Fintype.card V).choose 3 := by
    rw [card_powersetCard, card_univ]
  have hcard_sub : S.card ≤ (Fintype.card V).choose 3 := by
    rw [← hcard_pow]
    exact card_le_card hsub
  have hcard_S : S.card = 4 * numOrientedK44 G := by
    rw [hS]
    exact card_leftSideTriples G hfree
  have hnum : numK44 G = numOrientedK44 G / 2 := rfl
  have h8 : 8 * numK44 G ≤ 4 * numOrientedK44 G := by
    rw [hnum]
    omega
  rw [hcard_S] at hcard_sub
  omega

/-- Convenient restatement of Lemma 2 in the paper's exact numerical form. -/
theorem lemma_2_paper_form [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hfree : IsK35Free G) :
    numK44 G ≤ (Fintype.card V).choose 3 / 8 := by
  have h := lemma_2_upper_bound G hfree
  omega

end K44K35Free
