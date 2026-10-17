import Paper09.Percolation
import Paper09.RFIM
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkDecomp
import Mathlib.Probability.Independence.InfinitePi

open Finset BigOperators Classical
open MeasureTheory ProbabilityTheory

noncomputable section
set_option maxHeartbeats 1000000

namespace Paper09.Percolation

/-- The graph induced by open vertices, retaining the original vertex type. -/
def openGraph {V : Type*} (G : SimpleGraph V) (ω : V → Prop) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ ω x ∧ ω y
  symm := by tauto
  loopless x h := G.loopless x h.1

/-- The actual open connected component, empty when the root is closed. -/
def cluster {V : Type*} (G : SimpleGraph V) (ω : V → Prop) (z : V) : Set V :=
  {x | ω z ∧ (openGraph G ω).Reachable z x}

/-- Size at least `r`, including infinite components, expressed by a finite
subset of the actual reachable component. -/
def clusterAtLeast {V : Type*} (G : SimpleGraph V) (ω : V → Prop) (z : V) (r : ℕ) : Prop :=
  ∃ S : Finset V, S.card = r ∧ (↑S : Set V) ⊆ cluster G ω z

@[simp] theorem mem_cluster {V : Type*} {G : SimpleGraph V} {ω : V → Prop} {z x : V} :
    x ∈ cluster G ω z ↔ ω z ∧ (openGraph G ω).Reachable z x := Iff.rfl

theorem cluster_root {V : Type*} (G : SimpleGraph V) {ω : V → Prop} {z : V}
    (hz : ω z) : z ∈ cluster G ω z := ⟨hz, .rfl⟩

theorem cluster_open {V : Type*} {G : SimpleGraph V} {ω : V → Prop} {z x : V}
    (hx : x ∈ cluster G ω z) : ω x := by
  obtain ⟨hz, ⟨p⟩⟩ := hx
  have hend : ∀ {u v : V} (p : (openGraph G ω).Walk u v), ω u → ω v := by
    intro u v p
    induction p with
    | nil => exact id
    | cons h p ih => exact fun _ => ih h.2.2
  exact hend p hz

/-- Every walk from inside a set to outside it crosses its vertex boundary. -/
theorem reachable_exit {V : Type*} {G : SimpleGraph V} {S : Finset V} {z x : V}
    (hz : z ∈ S) (hx : x ∉ S) (hreach : G.Reachable z x) :
    ∃ a ∈ S, ∃ b ∉ S, G.Adj a b := by
  obtain ⟨p⟩ := hreach
  induction p with
  | nil => exact (hx hz).elim
  | @cons z y x h p ih =>
    by_cases hy : y ∈ S
    · exact ih hy hx
    · exact ⟨z, hz, y, hy, h⟩

theorem clusterAtLeast_mono {V : Type*} {G : SimpleGraph V} {ω : V → Prop}
    {z : V} {m n : ℕ} (h : clusterAtLeast G ω z n) (hmn : m ≤ n) :
    clusterAtLeast G ω z m := by
  classical
  obtain ⟨S, hS, hsub⟩ := h
  obtain ⟨T, hTS, hT⟩ := exists_subset_card_eq (by omega : m ≤ S.card)
  exact ⟨T, hT, fun x hx => hsub (hTS hx)⟩

/-- Insert a two-edge excursion into a closed walk at a visited vertex. -/
def insertExcursion {V : Type*} [DecidableEq V] {G : SimpleGraph V} {z a b : V}
    (p : G.Walk z z) (ha : a ∈ p.support) (hab : G.Adj a b) : G.Walk z z :=
  (p.takeUntil a ha).append (.cons hab (.cons hab.symm (p.dropUntil a ha)))

theorem insertExcursion_length {V : Type*} [DecidableEq V] {G : SimpleGraph V} {z a b : V}
    (p : G.Walk z z) (ha : a ∈ p.support) (hab : G.Adj a b) :
    (insertExcursion p ha hab).length = p.length + 2 := by
  have hs := congrArg SimpleGraph.Walk.length (p.take_spec ha)
  simp only [SimpleGraph.Walk.length_append] at hs
  simp only [insertExcursion, SimpleGraph.Walk.length_append,
    SimpleGraph.Walk.length_cons]
  omega

theorem insertExcursion_support {V : Type*} [DecidableEq V] {G : SimpleGraph V} {z a b : V}
    (p : G.Walk z z) (ha : a ∈ p.support) (hab : G.Adj a b) :
    (insertExcursion p ha hab).support.toFinset = insert b p.support.toFinset := by
  classical
  ext x
  have hs (x : V) := congrArg (fun q : G.Walk z z => x ∈ q.support) (p.take_spec ha)
  simp only [SimpleGraph.Walk.mem_support_append_iff] at hs
  simp only [insertExcursion, List.mem_toFinset, Finset.mem_insert,
    SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_cons, List.mem_cons]
  have hs' := eq_iff_iff.mp (hs x)
  have ha' : x = a → x ∈ p.support := by rintro rfl; exact ha
  tauto

/-- An actual cluster of size at least `r` contains a rooted connected set of
exactly `r` vertices. Its spanning tree is encoded by a closed depth-first walk
of length `2(r-1)`; this also applies to infinite clusters. -/
theorem clusterAtLeast_closed_walk {V : Type*} [DecidableEq V] {G : SimpleGraph V} {ω : V → Prop}
    {z : V} {r : ℕ} (hr : 0 < r) (h : clusterAtLeast G ω z r) :
    ∃ p : (openGraph G ω).Walk z z,
      p.length = 2 * (r - 1) ∧ p.support.toFinset.card = r := by
  classical
  induction r, hr using Nat.le_induction with
  | base =>
    obtain ⟨S, hS, hsub⟩ := h
    obtain ⟨x, hx⟩ := card_pos.mp (by omega : 0 < S.card)
    have hz := (hsub hx).1
    exact ⟨.nil, by simp, by simp⟩
  | @succ r hr ih =>
    obtain ⟨p, hp, hpc⟩ := ih (clusterAtLeast_mono h (by omega))
    obtain ⟨S, hS, hsub⟩ := h
    have hnsub : ¬ S ⊆ p.support.toFinset := by
      intro hsub'
      have := card_le_card hsub'
      omega
    obtain ⟨x, hx, hxp⟩ := Finset.not_subset.mp hnsub
    obtain ⟨a, ha, b, hb, hab⟩ := reachable_exit
      (by simpa using p.start_mem_support)
      hxp (hsub hx).2
    let q := insertExcursion p (by simpa using ha) hab
    refine ⟨q, ?_, ?_⟩
    · dsimp [q]
      rw [insertExcursion_length, hp]
      omega
    · dsimp [q]
      rw [insertExcursion_support, card_insert_of_notMem hb, hpc]

/-- Forgetting the openness condition preserves every graph edge. -/
theorem openGraph_le {V : Type*} (G : SimpleGraph V) (ω : V → Prop) :
    openGraph G ω ≤ G := fun _ _ h => h.1

/-- A walk all of whose vertices are open is genuinely a walk inside the open
component. This statement concerns the original graph, not a certificate. -/
theorem walk_support_subset_cluster {V : Type*} {G : SimpleGraph V} {ω : V → Prop}
    {z x : V} (p : G.Walk z x) (hω : ∀ v ∈ p.support, ω v) :
    ∀ v ∈ p.support, v ∈ cluster G ω z := by
  induction p with
  | nil => simpa using cluster_root G (hω _ (by simp))
  | @cons z y x h p ih =>
    have hz := hω z (by simp)
    have hy := hω y (by simp)
    have hi := ih (fun v hv => hω v (by simp [hv]))
    intro v hv
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact cluster_root G hz
    · exact ⟨hz, ((show (openGraph G ω).Adj z y from ⟨h, hz, hy⟩).reachable).trans
        (hi v hv).2⟩

/-- A closed walk in the original graph exactly encoding the selected cluster
subset; each visited site is actually open. -/
theorem clusterAtLeast_walk {V : Type*} [DecidableEq V] {G : SimpleGraph V} {ω : V → Prop}
    {z : V} {r : ℕ} (hr : 0 < r) (h : clusterAtLeast G ω z r) :
    ∃ p : G.Walk z z, p.length = 2 * (r - 1) ∧ p.support.toFinset.card = r ∧
      ∀ x ∈ p.support, ω x := by
  classical
  obtain ⟨p, hp, hc⟩ := clusterAtLeast_closed_walk hr h
  have hω (x : V) (hx : x ∈ p.support) : ω x := by
    have hz : ω z := by
      obtain ⟨S, hS, hsub⟩ := h
      obtain ⟨a, ha⟩ := card_pos.mp (by omega : 0 < S.card)
      exact (hsub ha).1
    exact cluster_open ⟨hz, (p.takeUntil x hx).reachable⟩
  let q := p.map (SimpleGraph.Hom.ofLE (openGraph_le G ω))
  refine ⟨q, ?_, ?_, ?_⟩
  · simpa [q] using hp
  · simpa [q] using hc
  · simpa [q] using hω

/-- The graph ball described by walks of length at most `r`. -/
def shortBall {V : Type*} (G : SimpleGraph V) (z : V) (r : ℕ) : Set V :=
  {x | ∃ p : G.Walk z x, p.length ≤ r}

/-- A connected set of `r` vertices lies within distance `r-1` of its root:
erase loops from a walk and use the number of distinct vertices. -/
theorem walk_support_shortBall {V : Type*} [DecidableEq V] {G : SimpleGraph V} {z : V}
    (p : G.Walk z z) {r : ℕ} (hc : p.support.toFinset.card = r) :
    ∀ x ∈ p.support, x ∈ shortBall G z (r - 1) := by
  classical
  intro x hx
  let q := (p.takeUntil x hx).toPath
  have hsub : (q : G.Walk z x).support.toFinset ⊆ p.support.toFinset := by
    intro v hv
    exact List.mem_toFinset.mpr (p.support_takeUntil_subset hx
      ((p.takeUntil x hx).support_toPath_subset (List.mem_toFinset.mp hv)))
  have hcard := card_le_card hsub
  rw [hc, List.toFinset_card_of_nodup q.property.support_nodup,
    SimpleGraph.Walk.length_support] at hcard
  exact ⟨q.val, by omega⟩

/-- Locality asserted in Lemma 3.2: the cluster-size event is determined by
marks within graph distance `r-1`. No finite-cluster assumption is needed. -/
theorem clusterAtLeast_local {V : Type*} [DecidableEq V] {G : SimpleGraph V} {ω ω' : V → Prop}
    {z : V} {r : ℕ} (hr : 0 < r)
    (heq : ∀ x ∈ shortBall G z (r - 1), ω x ↔ ω' x) :
    clusterAtLeast G ω z r ↔ clusterAtLeast G ω' z r := by
  classical
  suffices hforward : ∀ {a b : V → Prop},
      (∀ x ∈ shortBall G z (r - 1), a x → b x) →
      clusterAtLeast G a z r → clusterAtLeast G b z r by
    exact ⟨hforward (fun x hx => (heq x hx).mp),
      hforward (fun x hx => (heq x hx).mpr)⟩
  intro a b hab h
  obtain ⟨p, hp, hc, ha⟩ := clusterAtLeast_walk hr h
  have hb : ∀ x ∈ p.support, b x := fun x hx =>
    hab x (walk_support_shortBall p hc x hx) (ha x hx)
  exact ⟨p.support.toFinset, hc, fun x hx =>
    walk_support_subset_cluster p hb x (List.mem_toFinset.mp hx)⟩

/-- The number of bounded-degree walks is at most the degree bound to the
walk length; in particular closed walks obey the same bound. -/
theorem card_walkLength_le {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [G.LocallyFinite] (D : ℕ) (hdeg : ∀ x, Fintype.card (G.neighborSet x) ≤ D)
    (n : ℕ) (z x : V) : (G.finsetWalkLength n z x).card ≤ D ^ n := by
  induction n generalizing z x with
  | zero =>
    by_cases h : z = x
    · subst x
      simp [SimpleGraph.finsetWalkLength]
    · simp [SimpleGraph.finsetWalkLength, h]
  | succ n ih =>
    calc
      (G.finsetWalkLength (n + 1) z x).card
          ≤ ∑ y : G.neighborSet z, (G.finsetWalkLength n y.val x).card := by
        simpa only [SimpleGraph.finsetWalkLength, card_map] using
          (Finset.card_biUnion_le (s := (univ : Finset (G.neighborSet z)))
            (t := fun y => (G.finsetWalkLength n y.val x).map
              ⟨fun p => SimpleGraph.Walk.cons y.property p, fun _ _ => by simp⟩))
      _ ≤ ∑ _y : G.neighborSet z, D ^ n := sum_le_sum (fun _ _ => ih _ _)
      _ = Fintype.card (G.neighborSet z) * D ^ n := by simp
      _ ≤ D * D ^ n := Nat.mul_le_mul_right _ (hdeg z)
      _ = D ^ (n + 1) := by simp [pow_succ, Nat.mul_comm]

/-- A finite list of all possible rooted connected vertex sets of size `r`.
The encoding is an actual walk enumeration, independently of the random marks. -/
def rootedAnimals {V : Type*} [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite]
    (z : V) (r : ℕ) : Finset (Finset V) :=
  ((G.finsetWalkLength (2 * (r - 1)) z z).image
    (fun p => p.support.toFinset)).filter (fun S => S.card = r)

/-- The paper's depth-first connected-set bound, proved from the walk encoding. -/
theorem card_rootedAnimals_le {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [G.LocallyFinite] (D : ℕ) (hdeg : ∀ x, Fintype.card (G.neighborSet x) ≤ D)
    (z : V) (r : ℕ) : (rootedAnimals G z r).card ≤ D ^ (2 * (r - 1)) := by
  exact (card_filter_le _ _).trans ((card_image_le).trans
    (card_walkLength_le G D hdeg _ z z))

/-- The actual cluster event is the finite union over these deterministic
connected animals. This is the bridge from reachability, including an infinite
component, to finite-event probability bounds. -/
theorem clusterAtLeast_iff_animal {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [G.LocallyFinite] (ω : V → Prop) (z : V) (r : ℕ) (hr : 0 < r) :
    clusterAtLeast G ω z r ↔ ∃ S ∈ rootedAnimals G z r, ∀ x ∈ S, ω x := by
  constructor
  · intro h
    obtain ⟨p, hp, hc, hω⟩ := clusterAtLeast_walk hr h
    refine ⟨p.support.toFinset, ?_, fun x hx => hω x (List.mem_toFinset.mp hx)⟩
    exact mem_filter.mpr ⟨mem_image.mpr ⟨p,
      SimpleGraph.mem_finsetWalkLength_iff.mpr hp, rfl⟩, hc⟩
  · rintro ⟨S, hS, hω⟩
    obtain ⟨himage, hcard⟩ := mem_filter.mp hS
    obtain ⟨p, hp, rfl⟩ := mem_image.mp himage
    refine ⟨p.support.toFinset, hcard, ?_⟩
    intro x hx
    exact walk_support_subset_cluster p
      (fun v hv => hω v (List.mem_toFinset.mpr hv)) x (List.mem_toFinset.mp hx)

/-- Nearest-neighbor graph on the full integer lattice. -/
def nnGraph (d : ℕ) : SimpleGraph (LatticeGeometry.Point d) where
  Adj := LatticeGeometry.Adj
  symm := by intro x y h; exact LatticeGeometry.adj_symm h
  loopless := LatticeGeometry.adj_irrefl

/-- Integer lattice cubes, including their boundary layers. -/
def latticeCube {d : ℕ} (z : LatticeGeometry.Point d) (r : ℕ) :
    Finset (LatticeGeometry.Point d) :=
  Fintype.piFinset (fun j => Finset.Icc (z j - (r : ℤ)) (z j + r))

@[simp] theorem mem_latticeCube {d : ℕ} {z x : LatticeGeometry.Point d} {r : ℕ} :
    x ∈ latticeCube z r ↔ ∀ j, z j - (r : ℤ) ≤ x j ∧ x j ≤ z j + r := by
  simp [latticeCube, Fintype.mem_piFinset]

theorem card_latticeCube {d : ℕ} (z : LatticeGeometry.Point d) (r : ℕ) :
    (latticeCube z r).card = (2 * r + 1) ^ d := by
  simp only [latticeCube, Fintype.card_piFinset, Int.card_Icc]
  have heq (j : Fin d) : (z j + (r : ℤ) + 1 - (z j - r)).toNat = 2 * r + 1 := by
    omega
  simp only [heq, prod_const, card_univ, Fintype.card_fin]

instance nnGraph_locallyFinite (d : ℕ) : (nnGraph d).LocallyFinite := by
  intro z
  let e : ↥(LatticeGeometry.neighbors z) ≃ (nnGraph d).neighborSet z :=
    { toFun := fun x => ⟨x.val, LatticeGeometry.mem_neighbors.mp x.property⟩
      invFun := fun x => ⟨x.val, LatticeGeometry.mem_neighbors.mpr x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Fintype.ofEquiv _ e

theorem nnGraph_degree_le {d : ℕ} (z : LatticeGeometry.Point d) :
    Fintype.card ((nnGraph d).neighborSet z) ≤ 2 * d := by
  let f : (nnGraph d).neighborSet z → ↥(LatticeGeometry.neighbors z) :=
    fun x => ⟨x.val, LatticeGeometry.mem_neighbors.mpr x.property⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun t : ↥(LatticeGeometry.neighbors z) => t.val) h
  exact (Fintype.card_le_of_injective f hf).trans
    (by simpa using LatticeGeometry.card_neighbors_le z)

theorem nn_adj_coordinate {d : ℕ} {x y : LatticeGeometry.Point d}
    (h : (nnGraph d).Adj x y) (j : Fin d) :
    x j - 1 ≤ y j ∧ y j ≤ x j + 1 := by
  obtain ⟨k, hk, hrest⟩ := h
  by_cases hj : j = k
  · subst j
    rcases hk with h | h <;> omega
  · have := hrest j hj
    omega

/-- Each nearest-neighbor step changes any coordinate by at most one. -/
theorem nn_walk_coordinate {d : ℕ} {x y : LatticeGeometry.Point d}
    (p : (nnGraph d).Walk x y) (j : Fin d) :
    x j - (p.length : ℤ) ≤ y j ∧ y j ≤ x j + p.length := by
  induction p with
  | nil => simp
  | @cons x a y h p ih =>
    have ha := nn_adj_coordinate h j
    simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
    omega

theorem nn_shortBall_subset_cube {d : ℕ} (z : LatticeGeometry.Point d) (r : ℕ) :
    shortBall (nnGraph d) z r ⊆ (latticeCube z r : Set (LatticeGeometry.Point d)) := by
  rintro x ⟨p, hp⟩
  apply mem_latticeCube.mpr
  intro j
  have hcoord := nn_walk_coordinate p j
  omega

/-- In lattice coordinates, the exact event only uses the `r-1` cube. -/
theorem clusterAtLeast_cube_local {d : ℕ} {ω ω' : LatticeGeometry.Point d → Prop}
    {z : LatticeGeometry.Point d} {r : ℕ} (hr : 0 < r)
    (heq : ∀ x ∈ latticeCube z (r - 1), ω x ↔ ω' x) :
    clusterAtLeast (nnGraph d) ω z r ↔ clusterAtLeast (nnGraph d) ω' z r :=
  clusterAtLeast_local hr (fun x hx => heq x (nn_shortBall_subset_cube z _ hx))

/-- Star adjacency on coarse lattice indices; equal indices are excluded. -/
def starGraph (d : ℕ) : SimpleGraph (LatticeGeometry.Point d) where
  Adj x y := x ≠ y ∧ ∀ j, x j - 1 ≤ y j ∧ y j ≤ x j + 1
  symm := by
    rintro x y ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    intro j
    have := h j
    omega
  loopless := by intro x h; exact h.1 rfl

def starNeighbors {d : ℕ} (z : LatticeGeometry.Point d) : Finset (LatticeGeometry.Point d) :=
  (latticeCube z 1).erase z

@[simp] theorem mem_starNeighbors {d : ℕ} {z x : LatticeGeometry.Point d} :
    x ∈ starNeighbors z ↔ (starGraph d).Adj z x := by
  simp only [starNeighbors, mem_erase, mem_latticeCube, Nat.cast_one, starGraph]
  exact ⟨fun h => ⟨h.1.symm, h.2⟩, fun h => ⟨h.1.symm, h.2⟩⟩

instance starGraph_locallyFinite (d : ℕ) : (starGraph d).LocallyFinite := by
  intro z
  let e : ↥(starNeighbors z) ≃ (starGraph d).neighborSet z :=
    { toFun := fun x => ⟨x.val, mem_starNeighbors.mp x.property⟩
      invFun := fun x => ⟨x.val, mem_starNeighbors.mpr x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Fintype.ofEquiv _ e

theorem card_starNeighbors {d : ℕ} (z : LatticeGeometry.Point d) :
    (starNeighbors z).card = 3 ^ d - 1 := by
  rw [starNeighbors, card_erase_of_mem (by simp), card_latticeCube]

theorem starGraph_degree_le {d : ℕ} (z : LatticeGeometry.Point d) :
    Fintype.card ((starGraph d).neighborSet z) ≤ 3 ^ d - 1 := by
  let f : (starGraph d).neighborSet z → ↥(starNeighbors z) :=
    fun x => ⟨x.val, mem_starNeighbors.mpr x.property⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun t : ↥(starNeighbors z) => t.val) h
  exact (Fintype.card_le_of_injective f hf).trans (by simp [card_starNeighbors])

/-- Measurability of the actual cluster size event follows from the finite
animal union, not from an assumed finite random cluster. -/
theorem measurableSet_clusterAtLeast {Ω V : Type*} [MeasurableSpace Ω]
    [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite]
    (ω : Ω → V → Prop) (hω : ∀ x, MeasurableSet {a | ω a x})
    (z : V) (r : ℕ) (hr : 0 < r) :
    MeasurableSet {a | clusterAtLeast G (ω a) z r} := by
  have hs : {a | clusterAtLeast G (ω a) z r} =
      ⋃ S ∈ rootedAnimals G z r, ⋂ x ∈ S, {a | ω a x} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter]
    rw [clusterAtLeast_iff_animal G (ω a) z r hr]
    constructor
    · rintro ⟨S, hS, h⟩
      exact ⟨S, hS, h⟩
    · rintro ⟨S, hS, h⟩
      exact ⟨S, hS, h⟩
  rw [hs]
  exact Finset.measurableSet_biUnion _ (fun S _ =>
    Finset.measurableSet_biInter S (fun x _ => hω x))

/-- Excluding the next integer size is exactly finiteness together with the
claimed size bound. Infinite components are therefore excluded by the same event. -/
theorem not_clusterAtLeast_iff {V : Type*} {G : SimpleGraph V} {ω : V → Prop}
    (z : V) (L : ℕ) :
    ¬clusterAtLeast G ω z (L + 1) ↔
      (cluster G ω z).Finite ∧ (cluster G ω z).ncard ≤ L := by
  classical
  constructor
  · intro h
    have hfin : (cluster G ω z).Finite := by
      by_contra hinf
      obtain ⟨S, hsub, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (L + 1)
      exact h ⟨S, hcard, hsub⟩
    refine ⟨hfin, ?_⟩
    by_contra hcard
    have hlarge : L + 1 ≤ hfin.toFinset.card := by
      rw [← Set.ncard_eq_toFinset_card _ hfin]
      omega
    obtain ⟨S, hsub, hS⟩ := exists_subset_card_eq hlarge
    apply h
    refine ⟨S, hS, ?_⟩
    intro x hx
    exact hfin.mem_toFinset.mp (hsub hx)
  · rintro ⟨hfin, hcard⟩ ⟨S, hS, hsub⟩
    have hc := Set.ncard_le_ncard hsub hfin
    simp only [Set.ncard_coe_finset, hS] at hc
    omega

end Paper09.Percolation
