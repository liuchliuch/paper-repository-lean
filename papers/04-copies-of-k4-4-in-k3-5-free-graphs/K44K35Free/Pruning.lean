import K44K35Free.Basic
import Mathlib.Data.Finset.Sum

/-!
# The local block pruning

Edges are ordered pairs in the fixed bipartition.  A block retains its original
two vertex sets throughout deletion.  `prunedEdges` implements the simultaneous
local choices, including when several indexed blocks have the same edge set.
-/

open Finset

namespace K44K35Free
namespace Pruning

variable {P I : Type*} [DecidableEq P]

/-- A complete bipartite block, with a specified controlled side. -/
structure Block (P : Type*) where
  controlledLeft : Bool
  left : Finset P
  right : Finset P

namespace Block

def controlled (B : Block P) : Finset P := if B.controlledLeft then B.left else B.right

def exceptional (B : Block P) : Finset P := if B.controlledLeft then B.right else B.left

def edges (B : Block P) : Finset (P × P) := B.left ×ˢ B.right

/-- Write an edge with its controlled endpoint first. -/
def edge (B : Block P) (x y : P) : P × P :=
  if B.controlledLeft then (x, y) else (y, x)

def controlledEnd (B : Block P) (e : P × P) : P :=
  if B.controlledLeft then e.1 else e.2

def exceptionalEnd (B : Block P) (e : P × P) : P :=
  if B.controlledLeft then e.2 else e.1

@[simp] theorem controlledEnd_edge (B : Block P) (x y : P) :
    B.controlledEnd (B.edge x y) = x := by
  cases h : B.controlledLeft <;> simp [controlledEnd, edge, h]

@[simp] theorem exceptionalEnd_edge (B : Block P) (x y : P) :
    B.exceptionalEnd (B.edge x y) = y := by
  cases h : B.controlledLeft <;> simp [exceptionalEnd, edge, h]

@[simp] theorem edge_mem_edges (B : Block P) (x y : P) :
    B.edge x y ∈ B.edges ↔ x ∈ B.controlled ∧ y ∈ B.exceptional := by
  cases h : B.controlledLeft <;> simp [edge, edges, controlled, exceptional, h, and_comm]

theorem edge_endpoints (B : Block P) (e : P × P) :
    B.edge (B.controlledEnd e) (B.exceptionalEnd e) = e := by
  cases h : B.controlledLeft <;> simp [edge, controlledEnd, exceptionalEnd, h]

end Block

/-- A block is active precisely when it needs a local two-subset choice. -/
def Active (B : Block P) : Prop := 3 ≤ B.controlled.card

/-- An outcome of local pruning, applied to the already altered edge set.
The condition ranges over the original blocks, not blocks recomputed after deletion. -/
noncomputable def prunedEdges (pre : Finset (P × P)) (blocks : I → Block P)
    (isMutual : I → Prop) (R : I → P → Finset P) : Finset (P × P) := by
  classical
  exact pre.filter fun e => ∀ i, ¬ isMutual i → Active (blocks i) →
    e ∈ (blocks i).edges →
    (blocks i).controlledEnd e ∈ R i ((blocks i).exceptionalEnd e)

theorem mem_prunedEdges {pre : Finset (P × P)} {blocks : I → Block P}
    {isMutual : I → Prop} {R : I → P → Finset P} {e : P × P} :
    e ∈ prunedEdges pre blocks isMutual R ↔ e ∈ pre ∧
      ∀ i, ¬ isMutual i → Active (blocks i) → e ∈ (blocks i).edges →
        (blocks i).controlledEnd e ∈ R i ((blocks i).exceptionalEnd e) := by
  classical
  simp [prunedEdges]

theorem prunedEdges_subset (pre : Finset (P × P)) (blocks : I → Block P)
    (isMutual : I → Prop) (R : I → P → Finset P) :
    prunedEdges pre blocks isMutual R ⊆ pre := by
  intro e he
  exact (mem_prunedEdges.mp he).1

/-- The vertices required by one local choice to preserve a given edge set. -/
noncomputable def requirements (D : Finset (P × P)) (B : Block P) (y : P) : Finset P := by
  classical
  exact B.controlled.filter fun x => B.edge x y ∈ D

@[simp] theorem mem_requirements {D : Finset (P × P)} {B : Block P} {x y : P} :
    x ∈ requirements D B y ↔ x ∈ B.controlled ∧ B.edge x y ∈ D := by
  classical
  simp [requirements]

theorem requirements_subset (D : Finset (P × P)) (B : Block P) (y : P) :
    requirements D B y ⊆ B.controlled := by
  intro x hx
  exact (mem_requirements.mp hx).1

theorem requirements_product_subset (A C : Finset P) (B : Block P) (y : P) :
    requirements (A ×ˢ C) B y ⊆
      (if B.controlledLeft then A else C) ∩ B.controlled := by
  intro x hx
  obtain ⟨hxcontrol, hxedge⟩ := mem_requirements.mp hx
  refine mem_inter.mpr ⟨?_, hxcontrol⟩
  cases h : B.controlledLeft
  · have hh : y ∈ A ∧ x ∈ C := by simpa [Block.edge, h] using hxedge
    simpa [h] using hh.2
  · have hh : x ∈ A ∧ y ∈ C := by simpa [Block.edge, h] using hxedge
    simpa [h] using hh.1

theorem requirements_product_card_le (A C : Finset P) (B : Block P) (y : P) :
    (requirements (A ×ˢ C) B y).card ≤
      ((if B.controlledLeft then A else C) ∩ B.controlled).card :=
  card_le_card (requirements_product_subset A C B y)

/-- The exact survival condition used by the independent local choices. -/
theorem subset_prunedEdges_iff {D pre : Finset (P × P)} {blocks : I → Block P}
    {isMutual : I → Prop} {R : I → P → Finset P} :
    D ⊆ prunedEdges pre blocks isMutual R ↔ D ⊆ pre ∧
      ∀ i, ¬ isMutual i → Active (blocks i) → ∀ y ∈ (blocks i).exceptional,
        requirements D (blocks i) y ⊆ R i y := by
  constructor
  · intro hD
    refine ⟨hD.trans (prunedEdges_subset _ _ _ _), ?_⟩
    intro i hi hactive y hy x hx
    obtain ⟨hx, he⟩ := mem_requirements.mp hx
    have hmem := (mem_prunedEdges.mp (hD he)).2 i hi hactive
      ((Block.edge_mem_edges _ _ _).mpr ⟨hx, hy⟩)
    simpa using hmem
  · rintro ⟨hD, hR⟩ e he
    refine mem_prunedEdges.mpr ⟨hD he, ?_⟩
    intro i hi hactive hblock
    have hends : (blocks i).controlledEnd e ∈ (blocks i).controlled ∧
        (blocks i).exceptionalEnd e ∈ (blocks i).exceptional := by
      apply (Block.edge_mem_edges _ _ _).mp
      simpa only [Block.edge_endpoints] using hblock
    apply hR i hi hactive _ hends.2
    exact mem_requirements.mpr ⟨hends.1, by simpa only [Block.edge_endpoints] using he⟩

/-- Three controlled vertices cannot share an exceptional-side neighbor after
pruning.  Mutual blocks were already removed, and every other relevant choice
has only two vertices. -/
theorem no_triple_in_block {pre : Finset (P × P)} {blocks : I → Block P}
    {isMutual : I → Prop} {R : I → P → Finset P}
    (hmutual : ∀ i, isMutual i → Disjoint pre (blocks i).edges)
    (hR : ∀ i, ¬ isMutual i → Active (blocks i) → ∀ y ∈ (blocks i).exceptional,
      (R i y).card = 2)
    (i : I) {X : Finset P} (hX : X.card = 3)
    (hsub : X ⊆ (blocks i).controlled) {y : P} (hy : y ∈ (blocks i).exceptional) :
    ¬ ∀ x ∈ X, (blocks i).edge x y ∈ prunedEdges pre blocks isMutual R := by
  intro hall
  have hactive : Active (blocks i) := by
    change 3 ≤ (blocks i).controlled.card
    simpa only [hX] using card_le_card hsub
  by_cases hi : isMutual i
  · have hne : X.Nonempty := by rw [← card_pos, hX]; decide
    obtain ⟨x, hx⟩ := hne
    exact Finset.disjoint_left.mp (hmutual i hi)
      (prunedEdges_subset _ _ _ _ (hall x hx))
      ((Block.edge_mem_edges _ _ _).mpr ⟨hsub hx, hy⟩)
  · have hXR : X ⊆ R i y := by
      intro x hx
      have he := (mem_prunedEdges.mp (hall x hx)).2 i hi hactive
        ((Block.edge_mem_edges _ _ _).mpr ⟨hsub hx, hy⟩)
      simpa using he
    have hcard := card_le_card hXR
    rw [hX, hR i hi hactive y hy] at hcard
    omega

section Bipartite
variable [Fintype P]

/-- The graph associated to ordered edges in the fixed bipartition. -/
def bipartiteGraph (edges : Finset (P × P)) : SimpleGraph (P ⊕ P) where
  Adj u v := match u, v with
    | .inl x, .inr y => (x, y) ∈ edges
    | .inr y, .inl x => (x, y) ∈ edges
    | _, _ => False
  symm := by intro u v; cases u <;> cases v <;> simp_all
  loopless := by intro u; cases u <;> simp

@[simp] theorem adj_left_right (edges : Finset (P × P)) (x y : P) :
    (bipartiteGraph edges).Adj (.inl x) (.inr y) ↔ (x, y) ∈ edges := Iff.rfl

@[simp] theorem adj_right_left (edges : Finset (P × P)) (x y : P) :
    (bipartiteGraph edges).Adj (.inr y) (.inl x) ↔ (x, y) ∈ edges := Iff.rfl

@[simp] theorem not_adj_left_left (edges : Finset (P × P)) (x y : P) :
    ¬ (bipartiteGraph edges).Adj (.inl x) (.inl y) := by simp [bipartiteGraph]

@[simp] theorem not_adj_right_right (edges : Finset (P × P)) (x y : P) :
    ¬ (bipartiteGraph edges).Adj (.inr x) (.inr y) := by simp [bipartiteGraph]

noncomputable def rightNeighbors (edges : Finset (P × P)) (X : Finset P) : Finset P := by
  classical
  exact univ.filter fun y => ∀ x ∈ X, (x, y) ∈ edges

noncomputable def leftNeighbors (edges : Finset (P × P)) (X : Finset P) : Finset P := by
  classical
  exact univ.filter fun x => ∀ y ∈ X, (x, y) ∈ edges

@[simp] theorem mem_rightNeighbors {edges : Finset (P × P)} {X : Finset P} {y : P} :
    y ∈ rightNeighbors edges X ↔ ∀ x ∈ X, (x, y) ∈ edges := by
  classical
  simp [rightNeighbors]

@[simp] theorem mem_leftNeighbors {edges : Finset (P × P)} {X : Finset P} {x : P} :
    x ∈ leftNeighbors edges X ↔ ∀ y ∈ X, (x, y) ∈ edges := by
  classical
  simp [leftNeighbors]

/-- The two one-sided common-neighborhood bounds imply the usual forbidden
subgraph condition, including triples meeting both classes. -/
theorem isK35Free_bipartiteGraph (edges : Finset (P × P))
    (hleft : ∀ X : Finset P, X.card = 3 → (leftNeighbors edges X).card ≤ 4)
    (hright : ∀ X : Finset P, X.card = 3 → (rightNeighbors edges X).card ≤ 4) :
    IsK35Free (bipartiteGraph edges) := by
  classical
  intro X hX
  let C := commonNeighbors (bipartiteGraph edges) X
  have hCL : C.toLeft ⊆ leftNeighbors edges X.toRight := by
    intro x hx
    apply mem_leftNeighbors.mpr
    intro y hy
    exact (mem_commonNeighbors.mp (mem_toLeft.mp hx)) _ (mem_toRight.mp hy)
  have hCR : C.toRight ⊆ rightNeighbors edges X.toLeft := by
    intro y hy
    apply mem_rightNeighbors.mpr
    intro x hx
    exact (mem_commonNeighbors.mp (mem_toRight.mp hy)) _ (mem_toLeft.mp hx)
  have hCLempty : X.toLeft.Nonempty → C.toLeft = ∅ := by
    rintro ⟨x, hx⟩
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro y hy
    exact not_adj_left_left edges y x
      ((mem_commonNeighbors.mp (mem_toLeft.mp hy)) _ (mem_toLeft.mp hx))
  have hCRempty : X.toRight.Nonempty → C.toRight = ∅ := by
    rintro ⟨x, hx⟩
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro y hy
    exact not_adj_right_right edges y x
      ((mem_commonNeighbors.mp (mem_toRight.mp hy)) _ (mem_toRight.mp hx))
  have hsumX := X.card_toLeft_add_card_toRight
  have hsumC := C.card_toLeft_add_card_toRight
  change C.card ≤ 4
  by_cases hXL : X.toLeft = ∅
  · have hXR : X.toRight.card = 3 := by simpa [hXL, hX] using hsumX
    have hXRne : X.toRight.Nonempty := by rw [← card_pos, hXR]; decide
    have hCE := hCRempty hXRne
    have hbound := (card_le_card hCL).trans (hleft X.toRight hXR)
    simp only [hCE, card_empty, Nat.add_zero] at hsumC
    omega
  · have hXLne := Finset.nonempty_iff_ne_empty.mpr hXL
    have hCE := hCLempty hXLne
    by_cases hXR : X.toRight = ∅
    · have hXL3 : X.toLeft.card = 3 := by simpa [hXR, hX] using hsumX
      have hbound := (card_le_card hCR).trans (hright X.toLeft hXL3)
      simp only [hCE, card_empty, Nat.zero_add] at hsumC
      omega
    · have hCE' := hCRempty (Finset.nonempty_iff_ne_empty.mpr hXR)
      simp [hCE, hCE'] at hsumC
      omega

end Bipartite

section PlaneSections

variable {A : Type*} [Fintype P]

/-- Blocks are indexed even when their edge sets coincide. `true` denotes
type I, `false` type II; only exceptional planes occur in the index. -/
abbrev SectionBlockIndex (bad : A → Prop) := Bool × { E : A // bad E }

def sectionBlock (sectionOf : A → Finset P) (leftDual rightDual : A → A)
    {bad : A → Prop} (i : SectionBlockIndex bad) : Block P where
  controlledLeft := i.1
  left := if i.1 then sectionOf (leftDual i.2.val) else sectionOf i.2.val
  right := if i.1 then sectionOf i.2.val else sectionOf (rightDual i.2.val)

def sectionMutual (bad : A → Prop) (leftDual rightDual : A → A)
    (i : SectionBlockIndex bad) : Prop :=
  if i.1 then bad (leftDual i.2.val) else bad (rightDual i.2.val)

@[simp] theorem sectionBlock_controlled_typeI (sectionOf : A → Finset P)
    (leftDual rightDual : A → A) {bad : A → Prop} (E : {E // bad E}) :
    (sectionBlock sectionOf leftDual rightDual (true, E)).controlled =
      sectionOf (leftDual E.val) := by
  simp [sectionBlock, Block.controlled]

@[simp] theorem sectionBlock_exceptional_typeI (sectionOf : A → Finset P)
    (leftDual rightDual : A → A) {bad : A → Prop} (E : {E // bad E}) :
    (sectionBlock sectionOf leftDual rightDual (true, E)).exceptional =
      sectionOf E.val := by
  simp [sectionBlock, Block.exceptional]

@[simp] theorem sectionBlock_edge_typeI (sectionOf : A → Finset P)
    (leftDual rightDual : A → A) {bad : A → Prop} (E : {E // bad E}) (x y : P) :
    (sectionBlock sectionOf leftDual rightDual (true, E)).edge x y = (x, y) := by
  simp [sectionBlock, Block.edge]

@[simp] theorem sectionBlock_controlled_typeII (sectionOf : A → Finset P)
    (leftDual rightDual : A → A) {bad : A → Prop} (E : {E // bad E}) :
    (sectionBlock sectionOf leftDual rightDual (false, E)).controlled =
      sectionOf (rightDual E.val) := by
  simp [sectionBlock, Block.controlled]

@[simp] theorem sectionBlock_exceptional_typeII (sectionOf : A → Finset P)
    (leftDual rightDual : A → A) {bad : A → Prop} (E : {E // bad E}) :
    (sectionBlock sectionOf leftDual rightDual (false, E)).exceptional =
      sectionOf E.val := by
  simp [sectionBlock, Block.exceptional]

@[simp] theorem sectionBlock_edge_typeII (sectionOf : A → Finset P)
    (leftDual rightDual : A → A) {bad : A → Prop} (E : {E // bad E}) (x y : P) :
    (sectionBlock sectionOf leftDual rightDual (false, E)).edge x y = (y, x) := by
  simp [sectionBlock, Block.edge]

theorem sectionBlock_controlled_card_le_four (sectionOf : A → Finset P)
    (bad : A → Prop) (leftDual rightDual : A → A)
    (hsmall : ∀ E, ¬ bad E → (sectionOf E).card ≤ 4)
    (i : SectionBlockIndex bad) (hi : ¬ sectionMutual bad leftDual rightDual i) :
    (sectionBlock sectionOf leftDual rightDual i).controlled.card ≤ 4 := by
  rcases i with ⟨b, E⟩
  cases b
  · simpa [sectionBlock, Block.controlled] using
      hsmall (rightDual E.val) (by simpa [sectionMutual] using hi)
  · simpa [sectionBlock, Block.controlled] using
      hsmall (leftDual E.val) (by simpa [sectionMutual] using hi)

/-- Two different plane sections of a cap meet in at most two points. -/
theorem intersection_card_le_two (sectionOf : A → Finset P)
    (hunique : ∀ (X : Finset P), X.card = 3 → ∀ E Q : A,
      X ⊆ sectionOf E → X ⊆ sectionOf Q → E = Q)
    {E Q : A} (hne : E ≠ Q) :
    (sectionOf E ∩ sectionOf Q).card ≤ 2 := by
  by_contra hcard
  have hthree : 3 ≤ (sectionOf E ∩ sectionOf Q).card := by omega
  obtain ⟨X, hX, hX3⟩ := Finset.exists_subset_card_eq hthree
  apply hne
  apply hunique X hX3 E Q
  · exact hX.trans inter_subset_left
  · exact hX.trans inter_subset_right

/-- Lemma 8: the two controlled-plane intersections for a designated pair.
The sole geometric input is uniqueness of the plane containing three cap points. -/
theorem lemma8_of_plane_sections (sectionOf : A → Finset P) (bad : A → Prop)
    (leftDual rightDual : A → A)
    (hdualRL : ∀ E, rightDual (leftDual E) = E)
    (hdualLR : ∀ E, leftDual (rightDual E) = E)
    (hunique : ∀ (X : Finset P), X.card = 3 → ∀ E Q : A,
      X ⊆ sectionOf E → X ⊆ sectionOf Q → E = Q)
    {Q C E : A} (hdesignated : Q = leftDual C)
    (hQ : ¬ bad Q) (hC : ¬ bad C) (hE : bad E) :
    (sectionOf Q ∩ sectionOf (leftDual E)).card ≤ 2 ∧
      (sectionOf C ∩ sectionOf (rightDual E)).card ≤ 2 := by
  constructor
  · apply intersection_card_le_two sectionOf hunique
    intro h
    have hCE : C = E := by
      have hc := congrArg rightDual (hdesignated.symm.trans h)
      simpa only [hdualRL] using hc
    exact hC (hCE ▸ hE)
  · apply intersection_card_le_two sectionOf hunique
    intro h
    have hQE : Q = E := by
      rw [hdesignated, h]
      exact hdualLR E
    exact hQ (hQE ▸ hE)

/-- Proposition 9's combinatorial step, expressed in terms of actual plane
sections.  The geometric inputs identify each triple's whole initial common
neighborhood with the dual plane section.  No common-neighborhood bound for
the final graph is assumed. -/
theorem proposition9_of_plane_sections
    (sectionOf : A → Finset P) (bad : A → Prop) (leftDual rightDual : A → A)
    (hdualLR : ∀ E, leftDual (rightDual E) = E)
    (hdualRL : ∀ E, rightDual (leftDual E) = E)
    (hsmall : ∀ E, ¬ bad E → (sectionOf E).card ≤ 4)
    (initial pre : Finset (P × P))
    (hpre : pre ⊆ initial)
    (hleftTriple : ∀ X : Finset P, X.card = 3 → ∃ Q : A,
      X ⊆ sectionOf Q ∧ leftNeighbors initial X = sectionOf (leftDual Q))
    (hrightTriple : ∀ X : Finset P, X.card = 3 → ∃ Q : A,
      X ⊆ sectionOf Q ∧ rightNeighbors initial X = sectionOf (rightDual Q))
    (R : SectionBlockIndex bad → P → Finset P)
    (hmutual : ∀ i, sectionMutual bad leftDual rightDual i →
      Disjoint pre (sectionBlock sectionOf leftDual rightDual i).edges)
    (hR : ∀ i, ¬ sectionMutual bad leftDual rightDual i →
      Active (sectionBlock sectionOf leftDual rightDual i) →
      ∀ y ∈ (sectionBlock sectionOf leftDual rightDual i).exceptional,
        (R i y).card = 2) :
    IsK35Free (bipartiteGraph (prunedEdges pre
      (sectionBlock sectionOf leftDual rightDual)
      (sectionMutual bad leftDual rightDual) R)) := by
  classical
  let blocks := sectionBlock sectionOf leftDual rightDual (bad := bad)
  let isMutual := sectionMutual bad leftDual rightDual
  let final := prunedEdges pre blocks isMutual R
  have hfin : final ⊆ initial := (prunedEdges_subset _ _ _ _).trans hpre
  change IsK35Free (bipartiteGraph final)
  apply isK35Free_bipartiteGraph
  · intro X hX
    obtain ⟨Q, hXQ, hcommon⟩ := hleftTriple X hX
    by_cases hb : bad (leftDual Q)
    · have hempty : leftNeighbors final X = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro y hy
        have hyinitial : y ∈ leftNeighbors initial X := by
          apply mem_leftNeighbors.mpr
          intro x hx
          exact hfin (mem_leftNeighbors.mp hy x hx)
        have hyE : y ∈ sectionOf (leftDual Q) := by
          rwa [hcommon] at hyinitial
        let i : SectionBlockIndex bad := (false, ⟨leftDual Q, hb⟩)
        have hcontrol : X ⊆ (blocks i).controlled := by
          simpa [blocks, i, hdualRL] using hXQ
        have hexception : y ∈ (blocks i).exceptional := by
          simpa [blocks, i] using hyE
        apply no_triple_in_block hmutual hR i hX hcontrol hexception
        intro x hx
        simpa [blocks, i] using mem_leftNeighbors.mp hy x hx
      simp [hempty]
    · have hsub : leftNeighbors final X ⊆ sectionOf (leftDual Q) := by
        intro y hy
        rw [← hcommon]
        apply mem_leftNeighbors.mpr
        intro x hx
        exact hfin (mem_leftNeighbors.mp hy x hx)
      exact (card_le_card hsub).trans (hsmall _ hb)
  · intro X hX
    obtain ⟨Q, hXQ, hcommon⟩ := hrightTriple X hX
    by_cases hb : bad (rightDual Q)
    · have hempty : rightNeighbors final X = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro y hy
        have hyinitial : y ∈ rightNeighbors initial X := by
          apply mem_rightNeighbors.mpr
          intro x hx
          exact hfin (mem_rightNeighbors.mp hy x hx)
        have hyE : y ∈ sectionOf (rightDual Q) := by
          rwa [hcommon] at hyinitial
        let i : SectionBlockIndex bad := (true, ⟨rightDual Q, hb⟩)
        have hcontrol : X ⊆ (blocks i).controlled := by
          simpa [blocks, i, hdualLR] using hXQ
        have hexception : y ∈ (blocks i).exceptional := by
          simpa [blocks, i] using hyE
        apply no_triple_in_block hmutual hR i hX hcontrol hexception
        intro x hx
        simpa [blocks, i] using mem_rightNeighbors.mp hy x hx
      simp [hempty]
    · have hsub : rightNeighbors final X ⊆ sectionOf (rightDual Q) := by
        intro y hy
        rw [← hcommon]
        apply mem_rightNeighbors.mpr
        intro x hx
        exact hfin (mem_rightNeighbors.mp hy x hx)
      exact (card_le_card hsub).trans (hsmall _ hb)

end PlaneSections

end Pruning
end K44K35Free
