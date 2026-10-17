/-
Copyright (c) 2026. Actual closure-conflict coloring for equation (3.13).
The degree bound is derived from the constructed covering, followed by a finite
greedy coloring proof. No degree or coloring certificate is assumed.
-/
import Paper09.BlockCovering
import Mathlib.Combinatorics.SimpleGraph.Coloring

open Finset BigOperators
open Paper09.LatticeGeometry Paper09.BlockCovering

noncomputable section

namespace Paper09.BlockColoring

/-- Conflict graph of a finite family: distinct indices conflict exactly when
their finite vertex sets intersect. -/
def intersectionGraph {ι α : Type*} [DecidableEq α] (C : ι → Finset α) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ (C i ∩ C j).Nonempty
  symm := by intro i j h; exact ⟨h.1.symm,by simpa [Finset.inter_comm] using h.2⟩
  loopless := by intro i h; exact h.1 rfl

instance intersectionGraph_decidable {ι α : Type*} [DecidableEq ι] [DecidableEq α] (C : ι → Finset α) :
    DecidableRel (intersectionGraph C).Adj := by
  intro i j
  unfold intersectionGraph
  infer_instance

/-- Count the whole closed neighborhood by assigning each conflicting index
one of its shared sites. The index itself is included, so no `+1` is lost. -/
theorem intersection_degree_add_one_le {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (C : ι → Finset α) (T : ℕ)
    (hcover : ∀ i x, x ∈ C i → (Finset.univ.filter (fun j => x ∈ C j)).card ≤ T)
    (i : ι) (hi : (C i).Nonempty) :
    (intersectionGraph C).degree i + 1 ≤ (C i).card * T := by
  classical
  let G := intersectionGraph C
  have hsub : insert i (G.neighborFinset i) ⊆
      (C i).biUnion (fun x => Finset.univ.filter (fun j => x ∈ C j)) := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · obtain ⟨x,hx⟩ := hi
      exact Finset.mem_biUnion.mpr ⟨x,hx,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩⟩
    · obtain ⟨_,x,hx⟩ := (G.mem_neighborFinset i j).mp hj
      obtain ⟨hxi,hxj⟩ := Finset.mem_inter.mp hx
      exact Finset.mem_biUnion.mpr ⟨x,hxi,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxj⟩⟩
  calc
    G.degree i + 1 = (insert i (G.neighborFinset i)).card := by
      rw [Finset.card_insert_of_notMem (G.notMem_neighborFinset_self i)]
      rfl
    _ ≤ ((C i).biUnion (fun x => Finset.univ.filter (fun j => x ∈ C j))).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ x ∈ C i, (Finset.univ.filter (fun j => x ∈ C j)).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ C i, T := Finset.sum_le_sum (fun x hx => hcover i x hx)
    _ = (C i).card*T := by simp

/-- Finite greedy coloring: a palette larger than every degree suffices.
The proof colors a finite set one vertex at a time and chooses an unused
neighbor color at each insertion. -/
theorem finite_greedy_coloring {ι : Type*} [Fintype ι] (G : SimpleGraph ι) [DecidableRel G.Adj]
    (Q : ℕ) (hQ : 0 < Q) (hdegree : ∀ i, G.degree i < Q) :
    Nonempty (G.Coloring (Fin Q)) := by
  classical
  have hpartial : ∀ A : Finset ι, ∃ f : ι → Fin Q,
      ∀ i ∈ A, ∀ j ∈ A, G.Adj i j → f i ≠ f j := by
    intro A
    induction A using Finset.induction_on with
    | empty => exact ⟨fun _ => ⟨0,hQ⟩,by simp⟩
    | @insert a A ha ih =>
      obtain ⟨f,hf⟩ := ih
      let forbidden := (A.filter (G.Adj a)).image f
      have hcard : forbidden.card < Q := by
        calc
          forbidden.card ≤ (A.filter (G.Adj a)).card := Finset.card_image_le
          _ ≤ (G.neighborFinset a).card := Finset.card_le_card (by
            intro j hj
            exact (G.mem_neighborFinset a j).mpr (Finset.mem_filter.mp hj).2)
          _ < Q := hdegree a
      obtain ⟨c,_,hc⟩ := Finset.exists_mem_notMem_of_card_lt_card
        (show forbidden.card < (Finset.univ : Finset (Fin Q)).card by simpa using hcard)
      refine ⟨Function.update f a c,?_⟩
      intro i hi j hj hadj
      by_cases hia : i=a <;> by_cases hja : j=a
      · subst i; subst j; exact False.elim (G.loopless a hadj)
      · subst i
        have hjA := (Finset.mem_insert.mp hj).resolve_left hja
        simp only [Function.update_self,Function.update_of_ne hja]
        intro hcolor
        apply hc
        exact Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨hjA,hadj⟩,hcolor.symm⟩
      · subst j
        have hiA := (Finset.mem_insert.mp hi).resolve_left hia
        simp only [Function.update_self,Function.update_of_ne hia]
        intro hcolor
        apply hc
        exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨hiA,G.symm hadj⟩,hcolor⟩
      · have hiA := (Finset.mem_insert.mp hi).resolve_left hia
        have hjA := (Finset.mem_insert.mp hj).resolve_left hja
        simpa only [Function.update_of_ne hia,Function.update_of_ne hja] using hf i hiA j hjA hadj
  obtain ⟨f,hf⟩ := hpartial Finset.univ
  exact ⟨SimpleGraph.Coloring.mk f (fun {i j} hij => hf i (Finset.mem_univ _) j (Finset.mem_univ _) hij)⟩

/-- A finite-domain vertex boundary has at most `2d` times the block size. -/
theorem boundary_card_le {d : ℕ} (V B : Finset (Point d)) :
    (boundary V B).card ≤ 2*d*B.card := by
  have hsub : boundary V B ⊆ B.biUnion neighbors := by
    intro y hy
    obtain ⟨_,_,x,hx,hxy⟩ := mem_boundary.mp hy
    exact Finset.mem_biUnion.mpr ⟨x,hx,mem_neighbors.mpr hxy⟩
  calc
    (boundary V B).card ≤ (B.biUnion neighbors).card := Finset.card_le_card hsub
    _ ≤ ∑ x ∈ B, (neighbors x).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ B, 2*d := Finset.sum_le_sum (fun x _ => card_neighbors_le x)
    _ = 2*d*B.card := by simp [Nat.mul_comm]

/-- The relative one-step closure of an actual covering block. -/
def closure {d : ℕ} {good : Point d → Prop} {n s : ℕ} (i : BlockIndex good n s) :
    Finset (Point d) := block i ∪ boundary (volume n) (block i)

theorem block_subset_closure {d : ℕ} {good : Point d → Prop} {n s : ℕ}
    (i : BlockIndex good n s) : block i ⊆ closure i := Finset.subset_union_left

theorem closure_nonempty {d : ℕ} {good : Point d → Prop} {n s : ℕ}
    (i : BlockIndex good n s) : (closure i).Nonempty :=
  (block_nonempty i).mono (block_subset_closure i)

theorem closure_subset_volume {d : ℕ} {good : Point d → Prop} {n s : ℕ}
    (i : BlockIndex good n s) : closure i ⊆ volume n := by
  intro y hy
  rcases Finset.mem_union.mp hy with hy | hy
  · exact block_subset_volume i hy
  · exact (mem_boundary.mp hy).1

theorem closure_card_le {d : ℕ} {good : Point d → Prop} {n s : ℕ}
    (i : BlockIndex good n s) : (closure i).card ≤ (2*d+1)*(block i).card := by
  have hb := boundary_card_le (volume n) (block i)
  exact (Finset.card_union_le _ _).trans (by nlinarith)

/-- At each site, the closure multiplicity is exactly `I_y + J_y`. -/
theorem closure_multiplicity {d : ℕ} (good : Point d → Prop) (n s : ℕ) (y : Point d) :
    (Finset.univ.filter (fun i : BlockIndex good n s => y ∈ closure i)).card =
      I good n s y + J good n s y := by
  classical
  have heq : Finset.univ.filter (fun i : BlockIndex good n s => y ∈ closure i) =
      Finset.univ.filter (fun i => y ∈ block i) ∪
        Finset.univ.filter (fun i => y ∈ boundary (volume n) (block i)) := by
    ext i; simp [closure]
  have hdisj : Disjoint (Finset.univ.filter (fun i : BlockIndex good n s => y ∈ block i))
      (Finset.univ.filter (fun i => y ∈ boundary (volume n) (block i))) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (mem_boundary.mp (Finset.mem_filter.mp hj).2).2.1 (Finset.mem_filter.mp hi).2
  rw [heq,Finset.card_union_of_disjoint hdisj,card_block_cover,card_block_boundary]

/-- Uniform closure multiplicity, derived from Lemma 3.3. -/
theorem closure_multiplicity_bound {d : ℕ} {good : Point d → Prop} {n s L : ℕ}
    (hs : 0 < s) (hevent : SmallClusters good n s L) {y : Point d} (hy : y ∈ volume n) :
    (Finset.univ.filter (fun i : BlockIndex good n s => y ∈ closure i)).card ≤
      (2+4*d)*(8*s)^d := by
  rw [closure_multiplicity]
  obtain ⟨_,hI,hJ⟩ := covering_scaled hs hevent hy
  have hp : (8*s)^(d-1) ≤ (8*s)^d := pow_le_pow_right' (by omega : 1 ≤ 8*s) (Nat.sub_le d 1)
  have hJ' := hJ.trans (Nat.mul_le_mul_left (4*d) hp)
  nlinarith

/-- The actual finite conflict graph on the constructed indexed blocks. -/
def conflictGraph {d : ℕ} (good : Point d → Prop) (n s : ℕ) :
    SimpleGraph (BlockIndex good n s) := intersectionGraph closure

instance {d : ℕ} (good : Point d → Prop) (n s : ℕ) :
    DecidableRel (conflictGraph good n s).Adj :=
  @intersectionGraph_decidable (BlockIndex good n s) (Point d) inferInstance inferInstance
    (fun i : BlockIndex good n s => closure i)

/-- An explicit dimension constant for the number of colors. -/
def coloringConstant (d : ℕ) : ℕ := (2*d+1)*(2+4*d)

def colorCount {d : ℕ} (good : Point d → Prop) (n s : ℕ) : ℕ :=
  coloringConstant d * maxBlockSize good n s * (8*s)^d

/-- The complete closed-neighborhood bound, hence the greedy coloring budget. -/
theorem conflict_degree_add_one_bound {d : ℕ} {good : Point d → Prop} {n s L : ℕ}
    (hs : 0 < s) (hevent : SmallClusters good n s L) (i : BlockIndex good n s) :
    (conflictGraph good n s).degree i + 1 ≤ colorCount good n s := by
  classical
  have hcover (i : BlockIndex good n s) (y : Point d) (hy : y ∈ closure i) :
      (Finset.univ.filter (fun j : BlockIndex good n s => y ∈ closure j)).card ≤ (2+4*d)*(8*s)^d :=
    closure_multiplicity_bound hs hevent (closure_subset_volume i hy)
  have hsize : (block i).card ≤ maxBlockSize good n s := Finset.le_sup (f := fun i : BlockIndex good n s => (block i).card) (Finset.mem_univ i)
  calc
    (conflictGraph good n s).degree i + 1 ≤ (closure i).card*((2+4*d)*(8*s)^d) :=
      intersection_degree_add_one_le (fun j : BlockIndex good n s => closure j)
        ((2+4*d)*(8*s)^d) hcover i (closure_nonempty i)
    _ ≤ ((2*d+1)*(block i).card)*((2+4*d)*(8*s)^d) :=
      Nat.mul_le_mul_right _ (closure_card_le i)
    _ ≤ ((2*d+1)*maxBlockSize good n s)*((2+4*d)*(8*s)^d) := by gcongr
    _ = colorCount good n s := by unfold colorCount coloringConstant; ring

/-- The covering always has a block index, even when there are no good labels. -/
theorem blockIndex_nonempty {d : ℕ} {good : Point d → Prop} {n s L : ℕ}
    (hs : 0 < s) (hevent : SmallClusters good n s L) : Nonempty (BlockIndex good n s) := by
  classical
  have hy : (0 : Point d) ∈ volume n := mem_cube.mpr (near_refl n 0)
  have hI : 0 < I good n s 0 :=
    lt_of_lt_of_le (by positivity : 0 < (2*s+1)^d) (covering_lower hs hevent hy)
  have hc : 0 < (Finset.univ.filter (fun i : BlockIndex good n s => (0 : Point d) ∈ block i)).card := by
    rwa [card_block_cover]
  obtain ⟨i,_⟩ := Finset.card_pos.mp hc
  exact ⟨i⟩

theorem colorCount_pos {d : ℕ} {good : Point d → Prop} {n s L : ℕ}
    (hs : 0 < s) (hevent : SmallClusters good n s L) : 0 < colorCount good n s := by
  obtain ⟨i⟩ := blockIndex_nonempty hs hevent
  have hdeg := conflict_degree_add_one_bound hs hevent i
  omega

/-- Actual greedy coloring of the closure-conflict graph, with precisely the
palette size claimed in (3.13), up to an explicit dimension-only constant. -/
theorem exists_coloring {d : ℕ} {good : Point d → Prop} {n s L : ℕ}
    (hs : 0 < s) (hevent : SmallClusters good n s L) :
    Nonempty ((conflictGraph good n s).Coloring (Fin (colorCount good n s))) := by
  apply finite_greedy_coloring _ _ (colorCount_pos hs hevent)
  intro i
  exact lt_of_lt_of_le (Nat.lt_succ_self _) (conflict_degree_add_one_bound hs hevent i)

/-- A fixed field-dependent proper coloring; all later class schedules use
this concrete chosen coloring. -/
def coloring {d : ℕ} {good : Point d → Prop} {n s L : ℕ}
    (hs : 0 < s) (hevent : SmallClusters good n s L) :
    (conflictGraph good n s).Coloring (Fin (colorCount good n s)) :=
  Classical.choice (exists_coloring hs hevent)

/-- Distinct same-color blocks have disjoint one-step closures. -/
theorem same_color_closures_disjoint {d : ℕ} {good : Point d → Prop} {n s : ℕ}
    {α : Type*} (c : (conflictGraph good n s).Coloring α) {i j : BlockIndex good n s}
    (hne : i ≠ j) (hcolor : c i = c j) : Disjoint (closure i) (closure j) := by
  apply Finset.disjoint_left.mpr
  intro y hyi hyj
  have hconflict : (conflictGraph good n s).Adj i j :=
    ⟨hne,⟨y,Finset.mem_inter.mpr ⟨hyi,hyj⟩⟩⟩
  exact (c.valid hconflict) hcolor

theorem same_color_blocks_disjoint {d : ℕ} {good : Point d → Prop} {n s : ℕ}
    {α : Type*} (c : (conflictGraph good n s).Coloring α) {i j : BlockIndex good n s}
    (hne : i ≠ j) (hcolor : c i = c j) : Disjoint (block i) (block j) :=
  (same_color_closures_disjoint c hne hcolor).mono (block_subset_closure i) (block_subset_closure j)

/-- No lattice edge joins distinct same-color blocks. Thus their conditional
Gibbs resamplings and frozen-exterior local chains can run independently. -/
theorem same_color_no_edge {d : ℕ} {good : Point d → Prop} {n s : ℕ}
    {α : Type*} (c : (conflictGraph good n s).Coloring α) {i j : BlockIndex good n s}
    (hne : i ≠ j) (hcolor : c i = c j) {x y : Point d}
    (hx : x ∈ block i) (hy : y ∈ block j) : ¬ Adj x y := by
  intro hxy
  have hd := same_color_closures_disjoint c hne hcolor
  have hyj := block_subset_closure j hy
  by_cases hyi : y ∈ block i
  · exact Finset.disjoint_left.mp hd (block_subset_closure i hyi) hyj
  · have hyb : y ∈ boundary (volume n) (block i) :=
      mem_boundary.mpr ⟨block_subset_volume j hy,hyi,x,hx,hxy⟩
    exact Finset.disjoint_left.mp hd (Finset.mem_union_right _ hyb) hyj

/-- Actual block indices in one color class. -/
def classIndices {d : ℕ} {good : Point d → Prop} {n s : ℕ} {α : Type*}
    (c : (conflictGraph good n s).Coloring α) (a : α) : Finset (BlockIndex good n s) := by
  classical
  exact Finset.univ.filter (fun i => c i = a)

@[simp] theorem mem_classIndices {d : ℕ} {good : Point d → Prop} {n s : ℕ} {α : Type*}
    {c : (conflictGraph good n s).Coloring α} {a : α} {i : BlockIndex good n s} :
    i ∈ classIndices c a ↔ c i = a := by
  classical
  simp [classIndices]

/-- Vertex set whose rate-one clocks are retained during this color's phase. -/
def classSites {d : ℕ} {good : Point d → Prop} {n s : ℕ} {α : Type*}
    (c : (conflictGraph good n s).Coloring α) (a : α) : Finset (Point d) :=
  (classIndices c a).biUnion block

/-- The union of closed blocks in a color class. -/
def classClosures {d : ℕ} {good : Point d → Prop} {n s : ℕ} {α : Type*}
    (c : (conflictGraph good n s).Coloring α) (a : α) : Finset (Point d) :=
  (classIndices c a).biUnion closure

@[simp] theorem mem_classSites {d : ℕ} {good : Point d → Prop} {n s : ℕ} {α : Type*}
    {c : (conflictGraph good n s).Coloring α} {a : α} {y : Point d} :
    y ∈ classSites c a ↔ ∃ i : BlockIndex good n s, c i = a ∧ y ∈ block i := by
  simp [classSites]

@[simp] theorem mem_classClosures {d : ℕ} {good : Point d → Prop} {n s : ℕ} {α : Type*}
    {c : (conflictGraph good n s).Coloring α} {a : α} {y : Point d} :
    y ∈ classClosures c a ↔ ∃ i : BlockIndex good n s, c i = a ∧ y ∈ closure i := by
  simp [classClosures]

theorem classSites_subset_volume {d : ℕ} {good : Point d → Prop} {n s : ℕ} {α : Type*}
    (c : (conflictGraph good n s).Coloring α) (a : α) : classSites c a ⊆ volume n := by
  intro y hy
  obtain ⟨i,_,hyi⟩ := mem_classSites.mp hy
  exact block_subset_volume i hyi

/-- Color-class closures are pairwise disjoint as finite sets, the exact
parallel-update property used by the ideal and physical block kernels. -/
theorem class_closures_pairwiseDisjoint {d : ℕ} {good : Point d → Prop} {n s : ℕ} {α : Type*}
    (c : (conflictGraph good n s).Coloring α) (a : α) :
    (classIndices c a).toSet.PairwiseDisjoint closure := by
  intro i hi j hj hne
  exact same_color_closures_disjoint c hne ((mem_classIndices.mp hi).trans (mem_classIndices.mp hj).symm)

/-- For each color and site, at most one selected block can be affected by a
one-site perturbation. This counts interior and boundary membership together. -/
theorem class_affected_card_le_one {d : ℕ} {good : Point d → Prop} {n s : ℕ} {α : Type*}
    (c : (conflictGraph good n s).Coloring α) (a : α) (y : Point d) :
    ((classIndices c a).filter (fun i => y ∈ closure i)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  obtain ⟨hiC,hiy⟩ := Finset.mem_filter.mp hi
  obtain ⟨hjC,hjy⟩ := Finset.mem_filter.mp hj
  by_contra hne
  have hd := same_color_closures_disjoint c hne
    ((mem_classIndices.mp hiC).trans (mem_classIndices.mp hjC).symm)
  exact Finset.disjoint_left.mp hd hiy hjy

/-- Equation (3.13) with an actual finite coloring and disjoint class closures. -/
theorem equation_3_13 {d : ℕ} {good : Point d → Prop} {n s L : ℕ}
    (hs : 0 < s) (hevent : SmallClusters good n s L) :
    ∃ Q : ℕ, 0 < Q ∧ Q ≤ coloringConstant d * maxBlockSize good n s * (8*s)^d ∧
      ∃ c : (conflictGraph good n s).Coloring (Fin Q),
        ∀ a : Fin Q, (classIndices c a).toSet.PairwiseDisjoint closure := by
  refine ⟨colorCount good n s,colorCount_pos hs hevent,le_rfl,coloring hs hevent,?_⟩
  exact class_closures_pairwiseDisjoint (coloring hs hevent)

end Paper09.BlockColoring
