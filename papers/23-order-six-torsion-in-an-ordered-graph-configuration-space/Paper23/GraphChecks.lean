import Paper23.Cubical
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.FinRange
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FinCases
import Mathlib.SetTheory.Cardinal.Finite

/-! Finite matching enumeration for the graph in equation (1).
Numerical certificates use ordinary kernel reduction.  Larger cube counts
are deduced from the matching count and disjointness, rather than evaluating
a list of millions of labelled cubes. -/
set_option Elab.async false
namespace Paper23.GraphChecks
open Cubical

/-- Disjoint closed edges, including all four endpoint inequalities. -/
def EdgesDisjoint (a b : Edge) : Bool :=
  let p := endpoints a
  let q := endpoints b
  p.1 != q.1 && p.1 != q.2 && p.2 != q.1 && p.2 != q.2

/-- Increasing three-edge matchings, grouped by their least edge.
The product enumerates the 39² possible remaining ordered edge pairs. -/
def matchingRow (a : Edge) : List (Edge × Edge × Edge) :=
  (List.finRange 39).flatMap fun b =>
    (List.finRange 39).filterMap fun c =>
      if a < b && b < c && EdgesDisjoint a b &&
          EdgesDisjoint a c && EdgesDisjoint b c then some (a,b,c) else none

@[irreducible] def threeMatchings : List (Edge × Edge × Edge) :=
  (List.finRange 39).flatMap matchingRow

/-- One stationary vertex outside the three closed moving edges. -/
def stationaryVertices (t : Edge × Edge × Edge) : List Vertex :=
  (List.finRange 32).filter fun v =>
    let a := endpoints t.1
    let b := endpoints t.2.1
    let c := endpoints t.2.2
    v != a.1 && v != a.2 && v != b.1 && v != b.2 && v != c.1 && v != c.2

/-- Canonical cubes are first stationary vertex, then three increasing edge tokens. -/
@[irreducible] def canonicalThreeCubes : List RawCube :=
  threeMatchings.flatMap fun t =>
    (stationaryVertices t).map fun v =>
      [.vertex v, .edge t.1, .edge t.2.1, .edge t.2.2]

/-- All particle assignments; list position is the particle label. -/
@[irreducible] def labelledThreeCubes : List RawCube :=
  canonicalThreeCubes.flatMap List.permutations

/-- The 39 independently reducible row counts, in edge order. -/
def matchingRowCount : Edge → ℕ := ![
  474,570,446,416,476,389,361,389,335,309,311,242,262,
  241,181,179,181,130,144,129,87,74,87,63,52,53,35,
  34,27,15,10,10,6,3,1,0,0,0,0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
/-- Kernel-checked exhaustive enumeration of the remaining two edges. -/
theorem matchingRow_length (a : Edge) : (matchingRow a).length = matchingRowCount a := by
  fin_cases a <;> (rw [matchingRow, List.length_flatMap]; decide +kernel)

/-- The graph has exactly 6,722 increasing matchings of three closed edges. -/
theorem threeMatchings_length : threeMatchings.length = 6722 := by
  rw [threeMatchings, List.length_flatMap]
  have h : (List.finRange 39).map (fun a => (matchingRow a).length) =
      (List.finRange 39).map matchingRowCount :=
    List.map_congr_left (fun a _ => matchingRow_length a)
  rw [h]
  decide +kernel

/-- Subdivision produces no loop edges. -/
theorem endpoints_ne (e : Edge) : (endpoints e).1 ≠ (endpoints e).2 := by
  fin_cases e <;> decide

/-- The Boolean edge test is exactly disjointness in the original cube model. -/
theorem edgesDisjoint_iff (a b : Edge) :
    EdgesDisjoint a b = true ↔ ClosureDisjoint (.edge a) (.edge b) := by
  simp [EdgesDisjoint, ClosureDisjoint, GraphCell.vertices, Finset.disjoint_left, and_assoc]

/-- The mathematical matching property, including its canonical increasing order. -/
def IsThreeMatching (t : Edge × Edge × Edge) : Prop :=
  t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧
    ClosureDisjoint (.edge t.1) (.edge t.2.1) ∧
    ClosureDisjoint (.edge t.1) (.edge t.2.2) ∧
    ClosureDisjoint (.edge t.2.1) (.edge t.2.2)

theorem mem_matchingRow_iff (a : Edge) (t : Edge × Edge × Edge) :
    t ∈ matchingRow a ↔ t.1 = a ∧ IsThreeMatching t := by
  rcases t with ⟨x,b,c⟩
  simp [matchingRow, IsThreeMatching, edgesDisjoint_iff, and_assoc]
  constructor
  · rintro ⟨hab,hbc,h₁,h₂,h₃,hax⟩
    subst x
    exact ⟨rfl,hab,hbc,h₁,h₂,h₃⟩
  · rintro ⟨hxa,hab,hbc,h₁,h₂,h₃⟩
    subst x
    exact ⟨hab,hbc,h₁,h₂,h₃,rfl⟩

theorem mem_threeMatchings_iff (t : Edge × Edge × Edge) :
    t ∈ threeMatchings ↔ IsThreeMatching t := by
  simp [threeMatchings, mem_matchingRow_iff]

/-- The six endpoints occupied by a three-edge matching. -/
def occupiedVertices (t : Edge × Edge × Edge) : Finset Vertex :=
  (.edge t.1 : GraphCell).vertices ∪
    (.edge t.2.1 : GraphCell).vertices ∪ (.edge t.2.2 : GraphCell).vertices

theorem edge_vertices_card (e : Edge) : (.edge e : GraphCell).vertices.card = 2 := by
  simp [GraphCell.vertices, endpoints_ne]

theorem occupiedVertices_card (t : Edge × Edge × Edge) (h : IsThreeMatching t) :
    (occupiedVertices t).card = 6 := by
  rcases h with ⟨_, _, hab, hac, hbc⟩
  rw [occupiedVertices, Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hac,hbc⟩),
    Finset.card_union_of_disjoint hab]
  simp only [edge_vertices_card]

theorem stationaryVertices_nodup (t : Edge × Edge × Edge) :
    (stationaryVertices t).Nodup :=
  (List.nodup_finRange 32).filter _

theorem stationaryVertices_toFinset (t : Edge × Edge × Edge) :
    (stationaryVertices t).toFinset = Finset.univ \ occupiedVertices t := by
  ext v
  simp [stationaryVertices, occupiedVertices, GraphCell.vertices, and_assoc, and_comm, and_left_comm]

/-- Six distinct endpoints leave precisely 26 choices of stationary vertex. -/
theorem stationaryVertices_length (t : Edge × Edge × Edge) (h : IsThreeMatching t) :
    (stationaryVertices t).length = 26 := by
  rw [← List.toFinset_card_of_nodup (stationaryVertices_nodup t), stationaryVertices_toFinset,
    Finset.card_sdiff_of_subset (Finset.subset_univ _), occupiedVertices_card t h]
  decide

/-- The canonical 3-cube count in §2, deduced without expanding the cube list. -/
theorem canonicalThreeCubes_length : canonicalThreeCubes.length = 174772 := by
  rw [canonicalThreeCubes, List.length_flatMap]
  have h : ∀ t ∈ threeMatchings, ((stationaryVertices t).map fun v =>
      ([.vertex v, .edge t.1, .edge t.2.1, .edge t.2.2] : RawCube)).length = 26 := by
    intro t ht
    rw [List.length_map, stationaryVertices_length t ((mem_threeMatchings_iff t).mp ht)]
  rw [List.map_congr_left h]
  rw [List.map_const', List.sum_replicate_nat, threeMatchings_length]

/-- A stationary-vertex test is exactly disjointness from all three edges. -/
theorem mem_stationaryVertices_iff (v : Vertex) (t : Edge × Edge × Edge) :
    v ∈ stationaryVertices t ↔
      ClosureDisjoint (.vertex v) (.edge t.1) ∧
      ClosureDisjoint (.vertex v) (.edge t.2.1) ∧
      ClosureDisjoint (.vertex v) (.edge t.2.2) := by
  simp [stationaryVertices, ClosureDisjoint, GraphCell.vertices, and_assoc, ne_comm]

/-- Every enumerated canonical list is an original labelled cube of degree three. -/
theorem canonicalThreeCubes_valid {c : RawCube} (hc : c ∈ canonicalThreeCubes) :
    IsCube c ∧ degree c = 3 := by
  rw [canonicalThreeCubes] at hc
  obtain ⟨t, ht, hc'⟩ := List.mem_flatMap.mp hc
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hc'
  have hm := (mem_threeMatchings_iff t).mp ht
  have hs := (mem_stationaryVertices_iff v t).mp hv
  simp [IsCube, degree, GraphCell.dimension, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2,
    hs.1, hs.2.1, hs.2.2]

/-- Every canonical cube has four distinguishable graph cells. -/
theorem canonicalThreeCubes_length_four {c : RawCube} (hc : c ∈ canonicalThreeCubes) :
    c.length = 4 := (canonicalThreeCubes_valid hc).1.1

/-- Enumerating all 24 assignments yields the labelled count in §2. -/
theorem labelledThreeCubes_length : labelledThreeCubes.length = 4194528 := by
  rw [labelledThreeCubes, List.length_flatMap]
  have h : ∀ c ∈ canonicalThreeCubes, c.permutations.length = 24 := by
    intro c hc
    rw [List.length_permutations, canonicalThreeCubes_length_four hc]
    decide
  rw [List.map_congr_left h]
  rw [List.map_const', List.sum_replicate_nat, canonicalThreeCubes_length]


/-- Filtering and then recording a tuple preserves the enumeration order. -/
theorem filterMap_ite_some {α β : Type*} (l : List α) (p : α → Bool) (f : α → β) :
    l.filterMap (fun x => if p x then some (f x) else none) = (l.filter p).map f := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : p a <;> simp [h, ih]

theorem matchingRow_nodup (a : Edge) : (matchingRow a).Nodup := by
  unfold matchingRow
  simp_rw [filterMap_ite_some]
  apply List.nodup_flatMap.mpr
  constructor
  · intro b hb
    apply ((List.nodup_finRange 39).filter _).map
    intro c d h
    exact congrArg (fun t : Edge × Edge × Edge => t.2.2) h
  · apply (List.nodup_finRange 39).imp
    intro b b' hne t ht ht'
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ht
    obtain ⟨c',hc',heq⟩ := List.mem_map.mp ht'
    exact hne (congrArg (fun t : Edge × Edge × Edge => t.2.1) heq).symm

/-- The matching enumeration has no repeated triples. -/
theorem threeMatchings_nodup : threeMatchings.Nodup := by
  rw [threeMatchings]
  apply List.nodup_flatMap.mpr
  constructor
  · intro a ha
    exact matchingRow_nodup a
  · apply (List.nodup_finRange 39).imp
    intro a b hne t ht ht'
    exact hne (((mem_matchingRow_iff a t).mp ht).1.symm.trans
      ((mem_matchingRow_iff b t).mp ht').1)

/-- Distinct canonical tuples encode distinct raw cubes. -/
theorem canonicalEncoding_injective : Function.Injective
    (fun p : Vertex × (Edge × Edge × Edge) =>
      [.vertex p.1, .edge p.2.1, .edge p.2.2.1, .edge p.2.2.2] :
        Vertex × (Edge × Edge × Edge) → RawCube) := by
  intro p q h
  rcases p with ⟨v,a,b,c⟩
  rcases q with ⟨w,d,e,f⟩
  simpa only [List.cons.injEq, GraphCell.vertex.injEq, GraphCell.edge.injEq,
    Prod.mk.injEq, and_true] using h

/-- The canonical cube enumeration has no repetitions. -/
theorem canonicalThreeCubes_nodup : canonicalThreeCubes.Nodup := by
  rw [canonicalThreeCubes]
  apply List.nodup_flatMap.mpr
  constructor
  · intro t ht
    apply (stationaryVertices_nodup t).map
    intro v w h
    exact congrArg Prod.fst (@canonicalEncoding_injective (v,t) (w,t) h)
  · apply threeMatchings_nodup.imp
    intro t s hne c ht hs
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ht
    obtain ⟨w,hw,heq⟩ := List.mem_map.mp hs
    exact hne (congrArg Prod.snd (@canonicalEncoding_injective (w,s) (v,t) heq)).symm

/-- Permuting particle labels preserves the original cube and degree conditions. -/
theorem labelledThreeCubes_valid {c : RawCube} (hc : c ∈ labelledThreeCubes) :
    IsCube c ∧ degree c = 3 := by
  rw [labelledThreeCubes] at hc
  obtain ⟨d,hd,hp⟩ := List.mem_flatMap.mp hc
  have hp := List.perm_of_mem_permutations hp
  have hv := canonicalThreeCubes_valid hd
  refine ⟨⟨hp.length_eq.trans hv.1.1, hp.symm.pairwise hv.1.2 ?_⟩, ?_⟩
  · intro x y h
    exact h.symm
  · exact (hp.map GraphCell.dimension).sum_eq.trans hv.2


/-- Cell closures are nonempty, including in the presence of parallel edges. -/
theorem cell_vertices_nonempty (g : GraphCell) : g.vertices.Nonempty := by
  cases g with
  | vertex v => exact ⟨v, by simp [GraphCell.vertices]⟩
  | edge e => exact ⟨(endpoints e).1, by simp [GraphCell.vertices]⟩

/-- Closure-disjoint products cannot repeat a graph cell. -/
theorem isCube_nodup {c : RawCube} (hc : IsCube c) : c.Nodup := by
  apply hc.2.imp
  intro x y h hxy
  subst y
  exact (cell_vertices_nonempty x).ne_empty ((Finset.disjoint_self_iff_empty x.vertices).mp h)

/-- A canonical increasing representative is determined by its particle-label orbit. -/
theorem canonical_perm_eq {c d : RawCube} (hc : c ∈ canonicalThreeCubes)
    (hd : d ∈ canonicalThreeCubes) (hp : c.Perm d) : c = d := by
  rw [canonicalThreeCubes] at hc hd
  obtain ⟨t,ht,hc'⟩ := List.mem_flatMap.mp hc
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hc'
  obtain ⟨s,hs,hd'⟩ := List.mem_flatMap.mp hd
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hd'
  have hvw : v = w := by
    have hm := hp.subset (by simp : GraphCell.vertex v ∈
      [GraphCell.vertex v, .edge t.1, .edge t.2.1, .edge t.2.2])
    simpa using hm
  have he : [t.1,t.2.1,t.2.2].Perm [s.1,s.2.1,s.2.2] := by
    simpa using hp.filterMap (fun g => match g with
      | .vertex _ => none
      | .edge e => some e)
  have ht' := (mem_threeMatchings_iff t).mp ht
  have hs' := (mem_threeMatchings_iff s).mp hs
  have hsortt : [t.1,t.2.1,t.2.2].Pairwise (· ≤ ·) := by
    simp [ht'.1.le, ht'.2.1.le, (lt_trans ht'.1 ht'.2.1).le]
  have hsorts : [s.1,s.2.1,s.2.2].Pairwise (· ≤ ·) := by
    simp [hs'.1.le, hs'.2.1.le, (lt_trans hs'.1 hs'.2.1).le]
  have heq := List.Perm.eq_of_sorted (fun a b _ _ hab hba => le_antisymm hab hba)
    hsortt hsorts he
  have hts : t = s := by
    rcases t with ⟨a,b,c⟩
    rcases s with ⟨x,y,z⟩
    simpa only [List.cons.injEq, Prod.mk.injEq, and_true] using heq
  rw [hvw, hts]

/-- The labelled cube enumeration is without multiplicities. -/
theorem labelledThreeCubes_nodup : labelledThreeCubes.Nodup := by
  rw [labelledThreeCubes]
  apply List.nodup_flatMap.mpr
  constructor
  · intro c hc
    exact List.nodup_permutations c (isCube_nodup (canonicalThreeCubes_valid hc).1)
  · apply List.Pairwise.imp_of_mem (p := canonicalThreeCubes_nodup)
    intro c d hc hd hne e hec hed
    exact hne (canonical_perm_eq hc hd
      ((List.perm_of_mem_permutations hec).symm.trans (List.perm_of_mem_permutations hed)))

/-- The canonical count also counts distinct original raw cubes. -/
theorem canonicalThreeCubes_card : canonicalThreeCubes.toFinset.card = 174772 := by
  rw [List.toFinset_card_of_nodup canonicalThreeCubes_nodup, canonicalThreeCubes_length]

/-- The labelled count also counts distinct original raw cubes. -/
theorem labelledThreeCubes_card : labelledThreeCubes.toFinset.card = 4194528 := by
  rw [List.toFinset_card_of_nodup labelledThreeCubes_nodup, labelledThreeCubes_length]

/-- A length-four degree-three product contains one vertex and three moving edges. -/
theorem degree_three_shape {c : RawCube} (hl : c.length = 4) (hd : degree c = 3) :
    ∃ (v : Vertex) (a b e : Edge),
      c.Perm [.vertex v, .edge a, .edge b, .edge e] := by
  obtain ⟨g₀,g₁,g₂,g₃,rfl⟩ := List.length_eq_four.mp hl
  cases g₀ <;> cases g₁ <;> cases g₂ <;> cases g₃ <;>
    simp [degree, GraphCell.dimension] at hd
  all_goals first
    | exact ⟨_,_,_,_,List.Perm.refl _⟩
    | exact ⟨_,_,_,_,List.Perm.swap _ _ _⟩
    | exact ⟨_,_,_,_,(List.Perm.cons _ (List.Perm.swap _ _ _)).trans
        (List.Perm.swap _ _ _)⟩
    | exact ⟨_,_,_,_,(List.Perm.cons _ (List.Perm.cons _ (List.Perm.swap _ _ _))).trans
        ((List.Perm.cons _ (List.Perm.swap _ _ _)).trans (List.Perm.swap _ _ _))⟩

/-- Three distinct moving edges admit an increasing representative. -/
theorem sort_three_edges (a b c : Edge) (h : [a,b,c].Nodup) :
    ∃ x y z : Edge, x < y ∧ y < z ∧ [a,b,c].Perm [x,y,z] := by
  have hne : a ≠ b ∧ a ≠ c ∧ b ≠ c := by simpa [and_assoc] using h
  have hnab : a.val ≠ b.val := fun hval => hne.1 (Fin.ext hval)
  have hnac : a.val ≠ c.val := fun hval => hne.2.1 (Fin.ext hval)
  have hnbc : b.val ≠ c.val := fun hval => hne.2.2 (Fin.ext hval)
  have hback : ∀ x y : Edge, x.val < y.val → x < y := fun _ _ h => h
  by_cases hab : a.val < b.val <;> by_cases hac : a.val < c.val <;> by_cases hbc : b.val < c.val
  all_goals first
    | exact ⟨a,b,c,hback _ _ (by omega),hback _ _ (by omega),List.Perm.refl _⟩
    | exact ⟨a,c,b,hback _ _ (by omega),hback _ _ (by omega),List.Perm.cons _ (List.Perm.swap _ _ _)⟩
    | exact ⟨b,a,c,hback _ _ (by omega),hback _ _ (by omega),List.Perm.swap _ _ _⟩
    | exact ⟨b,c,a,hback _ _ (by omega),hback _ _ (by omega),(List.Perm.swap _ _ _).trans
        (List.Perm.cons _ (List.Perm.swap _ _ _))⟩
    | exact ⟨c,a,b,hback _ _ (by omega),hback _ _ (by omega),(List.Perm.cons _ (List.Perm.swap _ _ _)).trans
        (List.Perm.swap _ _ _)⟩
    | exact ⟨c,b,a,hback _ _ (by omega),hback _ _ (by omega),(List.Perm.swap _ _ _).trans
        ((List.Perm.cons _ (List.Perm.swap _ _ _)).trans (List.Perm.swap _ _ _))⟩

/-- Closure-disjointness is invariant under changes of particle labels. -/
theorem isCube_of_perm {c d : RawCube} (hp : c.Perm d) (hc : IsCube c) : IsCube d := by
  refine ⟨hp.length_eq.symm.trans hc.1, hp.pairwise hc.2 ?_⟩
  intro x y h
  exact h.symm

/-- Every original degree-three cube occurs in the finite labelled enumeration. -/
theorem labelledThreeCubes_complete {c : RawCube} (hc : IsCube c) (hd : degree c = 3) :
    c ∈ labelledThreeCubes := by
  obtain ⟨v,a,b,e,hshape⟩ := degree_three_shape hc.1 hd
  have hfirst := isCube_of_perm hshape hc
  have hne : [a,b,e].Nodup := by
    simpa using (isCube_nodup hfirst).tail
  obtain ⟨x,y,z,hxy,hyz,hsort⟩ := sort_three_edges a b e hne
  have hp := hshape.trans (List.Perm.cons (.vertex v) (hsort.map GraphCell.edge))
  have hcan := isCube_of_perm hp hc
  have hvx := (List.pairwise_cons.mp hcan.2).1 (.edge x) (by simp)
  have hvy := (List.pairwise_cons.mp hcan.2).1 (.edge y) (by simp)
  have hvz := (List.pairwise_cons.mp hcan.2).1 (.edge z) (by simp)
  have hxy' := (List.pairwise_cons.mp hcan.2.tail).1 (.edge y) (by simp)
  have hxz' := (List.pairwise_cons.mp hcan.2.tail).1 (.edge z) (by simp)
  have hyz' := (List.pairwise_cons.mp hcan.2.tail.tail).1 (.edge z) (by simp)
  have hm : (x,y,z) ∈ threeMatchings :=
    (mem_threeMatchings_iff _).mpr ⟨hxy,hyz,hxy',hxz',hyz'⟩
  have hv : v ∈ stationaryVertices (x,y,z) :=
    (mem_stationaryVertices_iff _ _).mpr ⟨hvx,hvy,hvz⟩
  have he : [.vertex v,.edge x,.edge y,.edge z] ∈ canonicalThreeCubes :=
    by rw [canonicalThreeCubes]; exact List.mem_flatMap.mpr ⟨(x,y,z),hm,List.mem_map.mpr ⟨v,hv,rfl⟩⟩
  rw [labelledThreeCubes]
  exact List.mem_flatMap.mpr ⟨_,he,List.mem_permutations.mpr hp⟩

/-- Exact correspondence with the original ordered cube predicate. -/
theorem mem_labelledThreeCubes_iff (c : RawCube) :
    c ∈ labelledThreeCubes ↔ IsCube c ∧ degree c = 3 :=
  ⟨labelledThreeCubes_valid, fun h => labelledThreeCubes_complete h.1 h.2⟩

/-- The enumerated finite set is equivalent to the actual degree-three cube type. -/
def degreeThreeEquiv : CubeInDegree 3 ≃ {c : RawCube // c ∈ labelledThreeCubes.toFinset} where
  toFun c := ⟨c.1.1, by
    rw [List.mem_toFinset, mem_labelledThreeCubes_iff]
    exact ⟨c.1.2,c.2⟩⟩
  invFun c := ⟨⟨c.1, ((mem_labelledThreeCubes_iff c.1).mp
    (List.mem_toFinset.mp c.2)).1⟩, ((mem_labelledThreeCubes_iff c.1).mp
    (List.mem_toFinset.mp c.2)).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The original ordered degree-three cube type has exactly 4,194,528 elements. -/
theorem cubeInDegree_three_card : Nat.card (CubeInDegree 3) = 4194528 := by
  rw [Nat.card_congr degreeThreeEquiv, Nat.card_eq_fintype_card]
  simpa only [Fintype.card_coe] using labelledThreeCubes_card

end Paper23.GraphChecks
