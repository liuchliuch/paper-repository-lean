/-
Copyright (c) 2026. The actual disorder-adapted block covering of Lemma 3.3.
The coarse labels are arbitrary. The sole environmental hypothesis is the
paper's finite bad-cluster event; all covering geometry is derived below.
-/
import Paper09.LatticeGeometry

open Finset BigOperators
open Paper09.LatticeGeometry

noncomputable section

namespace Paper09.BlockCovering

/-- Coordinatewise distance at most `r`, the integer sup-norm ball relation. -/
def Near {d : ℕ} (r : ℕ) (x y : Point d) : Prop :=
  ∀ j, y j - (r : ℤ) ≤ x j ∧ x j ≤ y j + (r : ℤ)

instance {d : ℕ} (r : ℕ) (x y : Point d) : Decidable (Near r x y) := by
  unfold Near
  infer_instance

def cube {d : ℕ} (r : ℕ) (y : Point d) : Finset (Point d) :=
  Fintype.piFinset (fun j => Finset.Icc (y j - (r : ℤ)) (y j + (r : ℤ)))

@[simp] theorem mem_cube {d : ℕ} {r : ℕ} {x y : Point d} :
    x ∈ cube r y ↔ Near r x y := by simp [cube, Near]

theorem near_refl {d : ℕ} (r : ℕ) (x : Point d) : Near r x x := by
  intro j; constructor <;> omega

theorem near_symm {d : ℕ} {r : ℕ} {x y : Point d} (h : Near r x y) : Near r y x := by
  intro j; have := h j; constructor <;> omega

theorem near_mono {d : ℕ} {r t : ℕ} {x y : Point d} (h : Near r x y) (hrt : r ≤ t) :
    Near t x y := by intro j; have := h j; constructor <;> omega

theorem near_triangle {d : ℕ} {r t : ℕ} {x y z : Point d}
    (hxy : Near r x y) (hyz : Near t y z) : Near (r+t) x z := by
  intro j; have := hxy j; have := hyz j; constructor <;> omega

theorem adj_near {d : ℕ} {x y : Point d} (h : Adj x y) : Near 1 x y := by
  obtain ⟨j,hj,hother⟩ := h
  intro k
  by_cases hkj : k = j
  · subst k; rcases hj with h | h <;> constructor <;> omega
  · rw [hother k hkj]; constructor <;> omega

theorem card_cube {d : ℕ} (r : ℕ) (y : Point d) : (cube r y).card = (2*r+1)^d := by
  unfold cube
  rw [Fintype.card_piFinset]
  have hcard (j : Fin d) : (Finset.Icc (y j-(r:ℤ)) (y j+(r:ℤ))).card = 2*r+1 := by
    rw [Int.card_Icc]
    omega
  simp_rw [hcard]
  simp

/-- We parametrize the paper's divisible-by-eight scale by `R = 8s`. -/
def center {d : ℕ} (s : ℕ) (k : Point d) : Point d := fun j => k j * (8*s : ℕ)

/-- Disjoint coarse cells `T_v`, with their actual half-open integer intervals. -/
def cell {d : ℕ} (s : ℕ) (k : Point d) : Finset (Point d) :=
  Fintype.piFinset (fun j => Finset.Ico
    (center s k j - (4*s : ℕ)) (center s k j + (4*s : ℕ)))

/-- The unique coarse index of the cell containing a fine-lattice point. -/
def cellOf {d : ℕ} (s : ℕ) (x : Point d) : Point d :=
  fun j => (x j + (4*s : ℕ)) / (8*s : ℕ)

@[simp] theorem mem_cell {d : ℕ} {s : ℕ} {k x : Point d} : x ∈ cell s k ↔
    ∀ j, center s k j - (4*s : ℕ) ≤ x j ∧ x j < center s k j + (4*s : ℕ) := by
  simp [cell]

theorem cellOf_eq_iff {d : ℕ} {s : ℕ} (hs : 0 < s) (x k : Point d) :
    cellOf s x = k ↔ x ∈ cell s k := by
  have hR : (0 : ℤ) < 8*(s:ℤ) := by positivity
  rw [funext_iff, mem_cell]
  apply forall_congr'
  intro j
  dsimp [cellOf, center]
  rw [Int.ediv_eq_iff_of_pos hR]
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

theorem mem_own_cell {d : ℕ} {s : ℕ} (hs : 0 < s) (x : Point d) :
    x ∈ cell s (cellOf s x) := (cellOf_eq_iff hs x _).mp rfl

theorem cell_near_center {d : ℕ} {s : ℕ} {k x : Point d} (hx : x ∈ cell s k) :
    Near (4*s) x (center s k) := by
  intro j
  have h := mem_cell.mp hx j
  exact ⟨h.1,le_of_lt h.2⟩

theorem card_cell {d : ℕ} (s : ℕ) (k : Point d) : (cell s k).card = (8*s)^d := by
  unfold cell
  rw [Fintype.card_piFinset]
  have hcard (j : Fin d) :
      (Finset.Ico (center s k j-(4*s:ℕ)) (center s k j+(4*s:ℕ))).card = 8*s := by
    rw [Int.card_Ico]
    omega
  simp_rw [hcard]
  simp

/-- Equality or star-adjacency on coarse indices. Self loops do not affect components. -/
def StarNear {d : ℕ} (k l : Point d) : Prop := Near 1 k l

theorem cells_starNear {d : ℕ} {s : ℕ} (hs : 0 < s) {x y : Point d}
    (hxy : Near (8*s) x y) : StarNear (cellOf s x) (cellOf s y) := by
  have hx := mem_cell.mp (mem_own_cell hs x)
  have hy := mem_cell.mp (mem_own_cell hs y)
  intro j
  have h1 := hx j
  have h2 := hy j
  have h3 := hxy j
  dsimp [center] at h1 h2
  push_cast at h1 h2 h3
  have hs' : (0:ℤ) < s := by exact_mod_cast hs
  constructor
  · by_contra h
    have hgap : (cellOf s x j : ℤ) + 2 ≤ cellOf s y j := by omega
    have hmul := mul_nonneg (show (0:ℤ) ≤ cellOf s y j - cellOf s x j - 2 by omega) hs'.le
    nlinarith [h1.2,h2.1,h3.1]
  · by_contra h
    have hgap : (cellOf s y j : ℤ) + 2 ≤ cellOf s x j := by omega
    have hmul := mul_nonneg (show (0:ℤ) ≤ cellOf s x j - cellOf s y j - 2 by omega) hs'.le
    nlinarith [h1.1,h2.2,h3.2]

/-- Bad-site steps in the true coarse star graph. -/
def BadStep {d : ℕ} (good : Point d → Prop) (k l : Point d) : Prop :=
  ¬ good k ∧ ¬ good l ∧ StarNear k l

/-- The actual bad connected component, empty at a good root. -/
def BadReach {d : ℕ} (good : Point d → Prop) (k l : Point d) : Prop :=
  ¬ good k ∧ Relation.ReflTransGen (BadStep good) k l

def clusterSet {d : ℕ} (good : Point d → Prop) (k : Point d) : Set (Point d) :=
  {l | BadReach good k l}

theorem badReach_refl {d : ℕ} {good : Point d → Prop} {k : Point d} (hk : ¬ good k) :
    BadReach good k k := ⟨hk,Relation.ReflTransGen.refl⟩

theorem badReach_bad {d : ℕ} {good : Point d → Prop} {k l : Point d}
    (h : BadReach good k l) : ¬ good l := by
  rcases h with ⟨hk,hpath⟩
  induction hpath with
  | refl => exact hk
  | tail _ hstep _ => exact hstep.2.1

theorem badReach_symm {d : ℕ} {good : Point d → Prop} {k l : Point d}
    (h : BadReach good k l) : BadReach good l k := by
  refine ⟨badReach_bad h, Relation.ReflTransGen.symmetric ?_ h.2⟩
  intro a b hab
  exact ⟨hab.2.1,hab.1,near_symm hab.2.2⟩

theorem badReach_trans {d : ℕ} {good : Point d → Prop} {k l m : Point d}
    (h1 : BadReach good k l) (h2 : BadReach good l m) : BadReach good k m :=
  ⟨h1.1,h1.2.trans h2.2⟩

theorem badReach_of_star {d : ℕ} {good : Point d → Prop} {k l : Point d}
    (hk : ¬ good k) (hl : ¬ good l) (hkl : StarNear k l) : BadReach good k l :=
  ⟨hk,Relation.ReflTransGen.single ⟨hk,hl,hkl⟩⟩

theorem clusterSet_eq_of_reach {d : ℕ} {good : Point d → Prop} {k l : Point d}
    (h : BadReach good k l) : clusterSet good k = clusterSet good l := by
  ext m
  exact ⟨fun hm => badReach_trans (badReach_symm h) hm,fun hm => badReach_trans h hm⟩

/-- A finite component as a finset; only the actual finite-component event is
used when this definition is instantiated. -/
def clusterFin {d : ℕ} (good : Point d → Prop) (k : Point d) : Finset (Point d) := by
  classical
  exact if h : (clusterSet good k).Finite then h.toFinset else ∅

@[simp] theorem mem_clusterFin {d : ℕ} {good : Point d → Prop} {k l : Point d}
    (hfin : (clusterSet good k).Finite) : l ∈ clusterFin good k ↔ BadReach good k l := by
  classical
  rw [clusterFin,dif_pos hfin]
  exact hfin.mem_toFinset

/-- The environmental event of Lemma 3.2, with the source's exact relevant radius. -/
def SmallClusters {d : ℕ} (good : Point d → Prop) (n s L : ℕ) : Prop :=
  ∀ k, Near (n+8*s) (center s k) 0 →
    (clusterSet good k).Finite ∧ (clusterSet good k).ncard ≤ L

/-- Only these roots can generate a translated block that meets the finite volume. -/
def relevantRoots {d : ℕ} (n s : ℕ) : Finset (Point d) :=
  (cube (n+s) (0 : Point d)).image (cellOf s)

theorem relevant_center {d : ℕ} {n s : ℕ} (hs : 0 < s) {k : Point d}
    (hk : k ∈ relevantRoots n s) : Near (n+8*s) (center s k) 0 := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hk
  have hc := near_symm (cell_near_center (mem_own_cell hs x))
  have ht := near_triangle hc (mem_cube.mp hx)
  exact near_mono ht (by omega)

/-- The full relevant bad clusters, with duplicate root descriptions identified. -/
def clusters {d : ℕ} (good : Point d → Prop) (n s : ℕ) : Finset (Finset (Point d)) := by
  classical
  exact ((relevantRoots n s).filter (fun k => ¬ good k)).image (clusterFin good)

/-- Intrinsic statement that a finset is a full, finite bad component. -/
def IsCluster {d : ℕ} (good : Point d → Prop) (C : Finset (Point d)) : Prop :=
  ∃ k, ¬ good k ∧ (clusterSet good k).Finite ∧ C = clusterFin good k

theorem clusters_spec {d : ℕ} {good : Point d → Prop} {n s L : ℕ}
    (hs : 0 < s) (hevent : SmallClusters good n s L) {C : Finset (Point d)}
    (hC : C ∈ clusters good n s) : IsCluster good C ∧ C.card ≤ L := by
  classical
  obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hC
  obtain ⟨hkroot,hkbad⟩ := Finset.mem_filter.mp hk
  obtain ⟨hfin,hsize⟩ := hevent k (relevant_center hs hkroot)
  refine ⟨⟨k,hkbad,hfin,rfl⟩,?_⟩
  rw [clusterFin,dif_pos hfin]
  rwa [← Set.ncard_eq_toFinset_card (clusterSet good k) hfin]

theorem isCluster_nonempty {d : ℕ} {good : Point d → Prop} {C : Finset (Point d)}
    (hC : IsCluster good C) : C.Nonempty := by
  obtain ⟨k,hk,hfin,rfl⟩ := hC
  exact ⟨k,(mem_clusterFin hfin).mpr (badReach_refl hk)⟩

theorem isCluster_bad {d : ℕ} {good : Point d → Prop} {C : Finset (Point d)}
    (hC : IsCluster good C) {k : Point d} (hk : k ∈ C) : ¬ good k := by
  obtain ⟨v,hv,hfin,rfl⟩ := hC
  exact badReach_bad ((mem_clusterFin hfin).mp hk)

theorem isCluster_closed {d : ℕ} {good : Point d → Prop} {C : Finset (Point d)}
    (hC : IsCluster good C) {k l : Point d} (hk : k ∈ C) (hl : ¬ good l)
    (hkl : StarNear k l) : l ∈ C := by
  obtain ⟨v,hv,hfin,rfl⟩ := hC
  apply (mem_clusterFin hfin).mpr
  exact badReach_trans ((mem_clusterFin hfin).mp hk)
    (badReach_of_star (badReach_bad ((mem_clusterFin hfin).mp hk)) hl hkl)

theorem isCluster_eq_of_star {d : ℕ} {good : Point d → Prop}
    {C D : Finset (Point d)} (hC : IsCluster good C) (hD : IsCluster good D)
    {k l : Point d} (hk : k ∈ C) (hl : l ∈ D) (hkl : StarNear k l) : C = D := by
  obtain ⟨v,hv,hvfin,rfl⟩ := hC
  obtain ⟨w,hw,hwfin,rfl⟩ := hD
  have hvk := (mem_clusterFin hvfin).mp hk
  have hwl := (mem_clusterFin hwfin).mp hl
  have hvw := badReach_trans (badReach_trans hvk
    (badReach_of_star (badReach_bad hvk) (badReach_bad hwl) hkl)) (badReach_symm hwl)
  have hsets := clusterSet_eq_of_reach hvw
  ext z
  simp only [mem_clusterFin hvfin,mem_clusterFin hwfin]
  change z ∈ clusterSet good v ↔ z ∈ clusterSet good w
  rw [hsets]

/-- The union of the disjoint cells belonging to a bad component. -/
def clusterRegion {d : ℕ} (s : ℕ) (C : Finset (Point d)) : Finset (Point d) :=
  C.biUnion (cell s)

theorem mem_clusterRegion {d : ℕ} {s : ℕ} (hs : 0 < s)
    {C : Finset (Point d)} {x : Point d} :
    x ∈ clusterRegion s C ↔ cellOf s x ∈ C := by
  constructor
  · intro hx
    obtain ⟨k,hk,hxk⟩ := Finset.mem_biUnion.mp hx
    rwa [(cellOf_eq_iff hs x k).mpr hxk]
  · intro hx
    exact Finset.mem_biUnion.mpr ⟨cellOf s x,hx,mem_own_cell hs x⟩

def translate {d : ℕ} (a : Point d) (B : Finset (Point d)) : Finset (Point d) :=
  B.image (fun x => x+a)

@[simp] theorem mem_translate {d : ℕ} {a x : Point d} {B : Finset (Point d)} :
    x ∈ translate a B ↔ x-a ∈ B := by
  constructor
  · intro hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    simpa using hz
  · intro hx
    exact Finset.mem_image.mpr ⟨x-a,hx,by simp⟩

theorem card_translate {d : ℕ} (a : Point d) (B : Finset (Point d)) :
    (translate a B).card = B.card :=
  Finset.card_image_of_injective _ (fun _ _ h => add_right_cancel h)

/-- Relative external vertex boundary, with no artificial outer-volume boundary. -/
def boundary {d : ℕ} (V B : Finset (Point d)) : Finset (Point d) :=
  V.filter (fun y => y ∉ B ∧ ∃ x ∈ B, Adj x y)

@[simp] theorem mem_boundary {d : ℕ} {V B : Finset (Point d)} {y : Point d} :
    y ∈ boundary V B ↔ y ∈ V ∧ y ∉ B ∧ ∃ x ∈ B, Adj x y := by simp [boundary]

def volume {d : ℕ} (n : ℕ) : Finset (Point d) := cube n 0

def type1Block {d : ℕ} (n s : ℕ) (w : Point d) : Finset (Point d) :=
  volume n ∩ cube s w

def type2Block {d : ℕ} (n s : ℕ) (C : Finset (Point d)) (a : Point d) : Finset (Point d) :=
  volume n ∩ translate a (clusterRegion s C)

@[simp] theorem mem_type1Block {d : ℕ} {n s : ℕ} {w y : Point d} :
    y ∈ type1Block n s w ↔ Near n y 0 ∧ Near s y w := by simp [type1Block,volume]

@[simp] theorem mem_type2Block {d : ℕ} {n s : ℕ} (hs : 0 < s)
    {C : Finset (Point d)} {a y : Point d} :
    y ∈ type2Block n s C a ↔ Near n y 0 ∧ cellOf s (y-a) ∈ C := by
  simp [type2Block,volume,mem_clusterRegion hs]

/-- The paper's type-1 admissibility condition `dist(w,G)≤3R/4`. -/
def admissibleCenter {d : ℕ} (good : Point d → Prop) (s : ℕ) (w : Point d) : Prop :=
  ∃ k, good k ∧ Near (6*s) w (center s k)

def type1Indices {d : ℕ} (good : Point d → Prop) (n s : ℕ) : Finset (Point d) := by
  classical
  exact (cube (n+s) 0).filter (fun w => admissibleCenter good s w ∧ (type1Block n s w).Nonempty)

def shifts {d : ℕ} (s : ℕ) : Finset (Point d) := cube s 0

/-- The component and shift are retained as distinct indices even when their
truncated vertex sets happen to coincide. -/
def type2Indices {d : ℕ} (good : Point d → Prop) (n s : ℕ) :
    Finset (Finset (Point d) × Point d) :=
  ((clusters good n s) ×ˢ shifts s).filter (fun p => (type2Block n s p.1 p.2).Nonempty)

theorem type1_index_of_mem {d : ℕ} {good : Point d → Prop} {n s : ℕ}
    {w y : Point d} (hw : admissibleCenter good s w) (hy : y ∈ type1Block n s w) :
    w ∈ type1Indices good n s := by
  classical
  apply Finset.mem_filter.mpr
  obtain ⟨hyV,hyw⟩ := mem_type1Block.mp hy
  refine ⟨mem_cube.mpr ?_,hw,⟨y,hy⟩⟩
  simpa [Nat.add_comm] using near_triangle (near_symm hyw) hyV

theorem type2_index_of_mem {d : ℕ} {good : Point d → Prop} {n s : ℕ}
    {C : Finset (Point d)} {a y : Point d} (hC : C ∈ clusters good n s)
    (ha : a ∈ shifts s) (hy : y ∈ type2Block n s C a) :
    (C,a) ∈ type2Indices good n s :=
  Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hC,ha⟩,⟨y,hy⟩⟩

theorem type1_size {d : ℕ} (n s : ℕ) (w : Point d) :
    (type1Block n s w).card ≤ (2*s+1)^d :=
  (Finset.card_le_card (Finset.inter_subset_right)).trans_eq (card_cube s w)

theorem clusterRegion_size {d : ℕ} (s : ℕ) (C : Finset (Point d)) :
    (clusterRegion s C).card ≤ C.card * (8*s)^d := by
  calc
    (clusterRegion s C).card ≤ ∑ k ∈ C, (cell s k).card := Finset.card_biUnion_le
    _ = C.card * (8*s)^d := by simp [card_cell]

theorem type2_size {d : ℕ} (n s : ℕ) (C : Finset (Point d)) (a : Point d) :
    (type2Block n s C a).card ≤ C.card * (8*s)^d := by
  calc
    (type2Block n s C a).card ≤ (translate a (clusterRegion s C)).card :=
      Finset.card_le_card Finset.inter_subset_right
    _ = (clusterRegion s C).card := card_translate a _
    _ ≤ C.card * (8*s)^d := clusterRegion_size s C

theorem type1_boundary_near {d : ℕ} {n s : ℕ} {w y : Point d}
    (hy : y ∈ boundary (volume n) (type1Block n s w)) : Near (s+1) y w := by
  obtain ⟨_,_,x,hx,hxy⟩ := mem_boundary.mp hy
  have hnear := (mem_type1Block.mp hx).2
  simpa [Nat.add_comm] using near_triangle (near_symm (adj_near hxy)) hnear

theorem type1_boundary_good {d : ℕ} {good : Point d → Prop} {n s : ℕ}
    (hs : 0 < s) {w y : Point d} (hw : w ∈ type1Indices good n s)
    (hy : y ∈ boundary (volume n) (type1Block n s w)) :
    ∃ k, good k ∧ Near (8*s) y (center s k) := by
  classical
  obtain ⟨_,⟨k,hgood,hnear⟩,_⟩ := Finset.mem_filter.mp hw
  refine ⟨k,hgood,near_mono (near_triangle (type1_boundary_near hy) hnear) (by omega)⟩

/-- Subtracting a permitted translation adds at most `s` to the distance. -/
theorem near_sub_shift {d : ℕ} {r s : ℕ} {x y a : Point d}
    (hxy : Near r x y) (ha : a ∈ shifts s) : Near (r+s) (x-a) y := by
  have ha' := mem_cube.mp ha
  intro j
  have h1 := hxy j
  have h2 := ha' j
  dsimp at h2 ⊢
  constructor <;> omega

theorem type2_boundary_good {d : ℕ} {good : Point d → Prop} {n s L : ℕ}
    (hs : 0 < s) (hevent : SmallClusters good n s L)
    {C : Finset (Point d)} {a y : Point d} (hi : (C,a) ∈ type2Indices good n s)
    (hy : y ∈ boundary (volume n) (type2Block n s C a)) :
    ∃ k, good k ∧ Near (8*s) y (center s k) := by
  obtain ⟨hp,_⟩ := Finset.mem_filter.mp hi
  obtain ⟨hC,ha⟩ := Finset.mem_product.mp hp
  have hcluster := (clusters_spec hs hevent hC).1
  obtain ⟨hyV,hynot,x,hx,hxy⟩ := mem_boundary.mp hy
  have hxC := (mem_type2Block hs).mp hx
  have hyC : cellOf s (y-a) ∉ C := by
    intro hc
    apply hynot
    exact (mem_type2Block hs).mpr ⟨mem_cube.mp hyV,hc⟩
  have hxy' : Near (8*s) (x-a) (y-a) := by
    have hh := adj_near hxy
    apply near_mono (r:=1) ?_ (by omega)
    intro j
    have := hh j
    dsimp
    constructor <;> omega
  have hstar := cells_starNear hs hxy'
  have hgood : good (cellOf s (y-a)) := by
    by_contra hbad
    exact hyC (isCluster_closed hcluster hxC.2 hbad hstar)
  refine ⟨cellOf s (y-a),hgood,?_⟩
  have hcell := cell_near_center (mem_own_cell hs (y-a))
  have ha' := mem_cube.mp ha
  apply near_mono (r:=5*s) ?_ (by omega)
  intro j
  have hc := hcell j
  have ht := ha' j
  dsimp at ht
  change center s (cellOf s (y-a)) j - (5*s:ℕ) ≤ y j ∧
    y j ≤ center s (cellOf s (y-a)) j + (5*s:ℕ)
  change center s (cellOf s (y-a)) j - (4*s:ℕ) ≤ y j-a j ∧
    y j-a j ≤ center s (cellOf s (y-a)) j + (4*s:ℕ) at hc
  constructor <;> omega

/-- A closure point is within one lattice step of a block vertex. -/
theorem closure_witness {d : ℕ} {V B : Finset (Point d)} {y : Point d}
    (hy : y ∈ B ∨ y ∈ boundary V B) : ∃ x ∈ B, Near 1 x y := by
  rcases hy with hy | hy
  · exact ⟨y,hy,near_refl 1 y⟩
  · obtain ⟨_,_,x,hx,hxy⟩ := mem_boundary.mp hy
    exact ⟨x,hx,adj_near hxy⟩

/-- At most one bad-cluster family can have the same point in any of its
translated block closures. This includes the finite-volume boundary. -/
theorem type2_closure_cluster_unique {d : ℕ} {good : Point d → Prop} {n s L : ℕ}
    (hs : 0 < s) (hevent : SmallClusters good n s L)
    {C D : Finset (Point d)} {a b y : Point d}
    (hi : (C,a) ∈ type2Indices good n s) (hj : (D,b) ∈ type2Indices good n s)
    (hyC : y ∈ type2Block n s C a ∨ y ∈ boundary (volume n) (type2Block n s C a))
    (hyD : y ∈ type2Block n s D b ∨ y ∈ boundary (volume n) (type2Block n s D b)) : C = D := by
  obtain ⟨hip,_⟩ := Finset.mem_filter.mp hi
  obtain ⟨hjp,_⟩ := Finset.mem_filter.mp hj
  obtain ⟨hC,ha⟩ := Finset.mem_product.mp hip
  obtain ⟨hD,hb⟩ := Finset.mem_product.mp hjp
  obtain ⟨x,hx,hxy⟩ := closure_witness hyC
  obtain ⟨z,hz,hzy⟩ := closure_witness hyD
  have hxC := ((mem_type2Block hs).mp hx).2
  have hzD := ((mem_type2Block hs).mp hz).2
  apply isCluster_eq_of_star (clusters_spec hs hevent hC).1 (clusters_spec hs hevent hD).1 hxC hzD
  apply cells_starNear hs
  have h1 := near_sub_shift hxy ha
  have h2 := near_sub_shift hzy hb
  exact near_mono (near_triangle h1 (near_symm h2)) (by omega)

def type1Cover {d : ℕ} (good : Point d → Prop) (n s : ℕ) (y : Point d) :
    Finset (Point d) :=
  (type1Indices good n s).filter (fun w => y ∈ type1Block n s w)

def type2Cover {d : ℕ} (good : Point d → Prop) (n s : ℕ) (y : Point d) :
    Finset (Finset (Point d) × Point d) :=
  (type2Indices good n s).filter (fun p => y ∈ type2Block n s p.1 p.2)

def I {d : ℕ} (good : Point d → Prop) (n s : ℕ) (y : Point d) : ℕ :=
  (type1Cover good n s y).card + (type2Cover good n s y).card

def type1Boundary {d : ℕ} (good : Point d → Prop) (n s : ℕ) (y : Point d) :
    Finset (Point d) :=
  (type1Indices good n s).filter (fun w => y ∈ boundary (volume n) (type1Block n s w))

def type2Boundary {d : ℕ} (good : Point d → Prop) (n s : ℕ) (y : Point d) :
    Finset (Finset (Point d) × Point d) :=
  (type2Indices good n s).filter (fun p => y ∈ boundary (volume n) (type2Block n s p.1 p.2))

def J {d : ℕ} (good : Point d → Prop) (n s : ℕ) (y : Point d) : ℕ :=
  (type1Boundary good n s y).card + (type2Boundary good n s y).card

theorem type1_cover_upper {d : ℕ} (good : Point d → Prop) (n s : ℕ) (y : Point d) :
    (type1Cover good n s y).card ≤ (2*s+1)^d := by
  have hsub : type1Cover good n s y ⊆ cube s y := by
    intro w hw
    exact mem_cube.mpr (near_symm ((mem_type1Block.mp (Finset.mem_filter.mp hw).2).2))
  exact (Finset.card_le_card hsub).trans_eq (card_cube s y)

theorem type2_cover_upper {d : ℕ} {good : Point d → Prop} {n s L : ℕ}
    (hs : 0 < s) (hevent : SmallClusters good n s L) (y : Point d) :
    (type2Cover good n s y).card ≤ (2*s+1)^d := by
  classical
  have hinj : Set.InjOn Prod.snd (type2Cover good n s y).toSet := by
    intro p hp q hq heq
    obtain ⟨hpI,hpB⟩ := Finset.mem_filter.mp hp
    obtain ⟨hqI,hqB⟩ := Finset.mem_filter.mp hq
    exact Prod.ext (type2_closure_cluster_unique hs hevent hpI hqI (Or.inl hpB) (Or.inl hqB)) heq
  have hsub : (type2Cover good n s y).image Prod.snd ⊆ shifts s := by
    intro a ha
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
    exact (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).2
  calc
    (type2Cover good n s y).card = ((type2Cover good n s y).image Prod.snd).card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (shifts s).card := Finset.card_le_card hsub
    _ = (2*s+1)^d := card_cube s 0

theorem covering_upper {d : ℕ} {good : Point d → Prop} {n s L : ℕ}
    (hs : 0 < s) (hevent : SmallClusters good n s L) (y : Point d) :
    I good n s y ≤ 2 * (2*s+1)^d := by
  unfold I
  have h1 := type1_cover_upper good n s y
  have h2 := type2_cover_upper hs hevent y
  omega

/-- The covering lower bound uses either all nearby good-center cubes or all
small translates of one actual bad component. -/
theorem covering_lower {d : ℕ} {good : Point d → Prop} {n s L : ℕ}
    (hs : 0 < s) (hevent : SmallClusters good n s L) {y : Point d}
    (hy : y ∈ volume n) : (2*s+1)^d ≤ I good n s y := by
  classical
  have hyV : Near n y 0 := mem_cube.mp hy
  by_cases hgood : ∃ k, good k ∧ Near (5*s) y (center s k)
  · obtain ⟨k,hk,hyk⟩ := hgood
    have hsub : cube s y ⊆ type1Cover good n s y := by
      intro w hw
      have hwy := mem_cube.mp hw
      have hwgood : admissibleCenter good s w :=
        ⟨k,hk,by simpa [show s+5*s=6*s by omega] using near_triangle hwy hyk⟩
      have hyB : y ∈ type1Block n s w := mem_type1Block.mpr ⟨hyV,near_symm hwy⟩
      exact Finset.mem_filter.mpr ⟨type1_index_of_mem hwgood hyB,hyB⟩
    have hcount := Finset.card_le_card hsub
    rw [card_cube] at hcount
    exact hcount.trans (Nat.le_add_right _ _)
  · let k := cellOf s y
    have hkroot : k ∈ relevantRoots n s := Finset.mem_image.mpr
      ⟨y,mem_cube.mpr (near_mono hyV (by omega)),rfl⟩
    have hbad (z : Point d) (hz : Near s z y) : ¬ good (cellOf s z) := by
      intro hgz
      apply hgood
      have hc := near_symm (cell_near_center (mem_own_cell hs z))
      have ht := near_triangle (near_symm hz) (near_symm hc)
      refine ⟨cellOf s z,hgz,?_⟩
      simpa [show s+4*s=5*s by omega] using ht
    have hkbad : ¬ good k := hbad y (near_refl s y)
    have hkfin := (hevent k (relevant_center hs hkroot)).1
    let C := clusterFin good k
    have hC : C ∈ clusters good n s := Finset.mem_image.mpr
      ⟨k,Finset.mem_filter.mpr ⟨hkroot,hkbad⟩,rfl⟩
    have hyB (a : Point d) (ha : a ∈ shifts s) : y ∈ type2Block n s C a := by
      apply (mem_type2Block hs).mpr
      refine ⟨hyV,(mem_clusterFin hkfin).mpr ?_⟩
      have hza : Near s (y-a) y := by
        simpa using near_sub_shift (near_refl 0 y) ha
      exact badReach_of_star hkbad (hbad (y-a) hza)
        (near_symm (cells_starNear hs (near_mono hza (by omega))))
    have hsub : (shifts s).image (fun a => (C,a)) ⊆ type2Cover good n s y := by
      intro p hp
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_filter.mpr ⟨type2_index_of_mem hC ha (hyB a ha),hyB a ha⟩
    have hcount := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)] at hcount
    change (cube s (0 : Point d)).card ≤ _ at hcount
    rw [card_cube] at hcount
    exact hcount.trans (Nat.le_add_left _ _)

/-- A product cube with one coordinate replaced by an arbitrary finite set. -/
def coordinateBox {d : ℕ} (s : ℕ) (y : Point d) (j : Fin d) (T : Finset ℤ) :
    Finset (Point d) :=
  Fintype.piFinset (fun k => if k=j then T else Finset.Icc (y k-(s:ℤ)) (y k+(s:ℤ)))

theorem mem_coordinateBox {d : ℕ} {s : ℕ} {y x : Point d} {j : Fin d} {T : Finset ℤ} :
    x ∈ coordinateBox s y j T ↔ x j ∈ T ∧
      ∀ k, k ≠ j → y k-(s:ℤ) ≤ x k ∧ x k ≤ y k+(s:ℤ) := by
  simp only [coordinateBox,Fintype.mem_piFinset]
  constructor
  · intro h
    refine ⟨by simpa using h j,?_⟩
    intro k hkj
    simpa [hkj] using h k
  · rintro ⟨hj,hother⟩ k
    by_cases hkj : k=j
    · subst k; simpa using hj
    · simpa [hkj] using hother k hkj

theorem card_coordinateBox {d : ℕ} (s : ℕ) (y : Point d) (j : Fin d) (T : Finset ℤ) :
    (coordinateBox s y j T).card = T.card * (2*s+1)^(d-1) := by
  classical
  unfold coordinateBox
  rw [Fintype.card_piFinset,←Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  rw [if_pos rfl]
  congr 1
  have hcoord (k : Fin d) (hk : k ∈ (Finset.univ : Finset (Fin d)).erase j) :
      (if k=j then T else Finset.Icc (y k-(s:ℤ)) (y k+(s:ℤ))).card = 2*s+1 := by
    have hkj := (Finset.mem_erase.mp hk).1
    rw [if_neg hkj,Int.card_Icc]
    omega
  rw [Finset.prod_congr rfl hcoord]
  simp

/-- Centers of cubes whose external vertex boundary contains `y`. -/
def cubeBoundaryCenters {d : ℕ} (s : ℕ) (y : Point d) : Finset (Point d) :=
  Finset.univ.biUnion (fun j : Fin d =>
    coordinateBox s y j {y j-(s:ℤ)-1} ∪ coordinateBox s y j {y j+(s:ℤ)+1})

theorem cubeBoundaryCenters_card {d : ℕ} (s : ℕ) (y : Point d) :
    (cubeBoundaryCenters s y).card ≤ 2*d*(2*s+1)^(d-1) := by
  calc
    (cubeBoundaryCenters s y).card ≤ ∑ j : Fin d,
        (coordinateBox s y j {y j-(s:ℤ)-1} ∪ coordinateBox s y j {y j+(s:ℤ)+1}).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ j : Fin d, ((coordinateBox s y j {y j-(s:ℤ)-1}).card +
        (coordinateBox s y j {y j+(s:ℤ)+1}).card) :=
      Finset.sum_le_sum (fun _ _ => Finset.card_union_le _ _)
    _ = 2*d*(2*s+1)^(d-1) := by simp [card_coordinateBox]; ring

theorem type1_boundary_center {d : ℕ} {n s : ℕ} {w y : Point d}
    (hy : y ∈ boundary (volume n) (type1Block n s w)) : w ∈ cubeBoundaryCenters s y := by
  obtain ⟨hyV,hynot,x,hx,hxy⟩ := mem_boundary.mp hy
  have hxw := (mem_type1Block.mp hx).2
  have hynotcube : ¬ Near s y w := by
    intro h
    exact hynot (mem_type1Block.mpr ⟨mem_cube.mp hyV,h⟩)
  obtain ⟨j,hj,hother⟩ := hxy
  have hrest (k : Fin d) (hkj : k ≠ j) : y k-(s:ℤ) ≤ w k ∧ w k ≤ y k+(s:ℤ) := by
    have h := hxw k
    have hxy := hother k hkj
    constructor <;> omega
  have hjnot : ¬ (w j-(s:ℤ) ≤ y j ∧ y j ≤ w j+(s:ℤ)) := by
    intro hjgood
    apply hynotcube
    intro k
    by_cases hkj : k=j
    · subst k; exact hjgood
    · have hr := hrest k hkj
      constructor <;> omega
  apply Finset.mem_biUnion.mpr
  refine ⟨j,Finset.mem_univ _,?_⟩
  rcases hj with hj | hj
  · apply Finset.mem_union_left
    apply mem_coordinateBox.mpr
    refine ⟨Finset.mem_singleton.mpr ?_,hrest⟩
    have h := hxw j
    omega
  · apply Finset.mem_union_right
    apply mem_coordinateBox.mpr
    refine ⟨Finset.mem_singleton.mpr ?_,hrest⟩
    have h := hxw j
    omega

theorem type1_boundary_count {d : ℕ} (good : Point d → Prop) (n s : ℕ) (y : Point d) :
    (type1Boundary good n s y).card ≤ 2*d*(2*s+1)^(d-1) :=
  (Finset.card_le_card (fun _ hw => type1_boundary_center (Finset.mem_filter.mp hw).2)).trans
    (cubeBoundaryCenters_card s y)

/-- A residue class contains at most one permitted shift coordinate because
`2s < R`. This supplies the surface-order translation count. -/
theorem shift_residue_inj {s : ℕ} (hs : 0 < s) (t : ℤ) {a b : ℤ}
    (ha : a ∈ Finset.Icc (-(s:ℤ)) (s:ℤ)) (hb : b ∈ Finset.Icc (-(s:ℤ)) (s:ℤ))
    (hab : (t-a+(4*s:ℕ)) % (8*s:ℕ) = (t-b+(4*s:ℕ)) % (8*s:ℕ)) : a=b := by
  have haux {a b : ℤ} (ha : a ∈ Finset.Icc (-(s:ℤ)) (s:ℤ))
      (hb : b ∈ Finset.Icc (-(s:ℤ)) (s:ℤ)) (hle : a ≤ b)
      (heq : (t-a+(4*s:ℕ)) % (8*s:ℕ) = (t-b+(4*s:ℕ)) % (8*s:ℕ)) : a=b := by
    have hzero := Int.emod_eq_emod_iff_emod_sub_eq_zero.mp heq
    have he : t-a+(4*s:ℕ) - (t-b+(4*s:ℕ)) = b-a := by ring
    rw [he] at hzero
    have ha' := Finset.mem_Icc.mp ha
    have hb' := Finset.mem_Icc.mp hb
    have hsmall : b-a < (8*s:ℕ) := by omega
    rw [Int.emod_eq_of_lt (by omega) hsmall] at hzero
    omega
  rcases le_total a b with h | h
  · exact haux ha hb h hab
  · exact (haux hb ha h hab.symm).symm

def boundaryShiftCoord (s : ℕ) (t : ℤ) : Finset ℤ :=
  ((Finset.Icc (-(s:ℤ)) (s:ℤ)).filter (fun a => (t-a+(4*s:ℕ)) % (8*s:ℕ) = 0)) ∪
  ((Finset.Icc (-(s:ℤ)) (s:ℤ)).filter (fun a => (t-a+(4*s:ℕ)) % (8*s:ℕ) = (8*s:ℕ)-1))

theorem boundaryShiftCoord_card {s : ℕ} (hs : 0 < s) (t : ℤ) :
    (boundaryShiftCoord s t).card ≤ 2 := by
  have hfiber (r : ℤ) :
      ((Finset.Icc (-(s:ℤ)) (s:ℤ)).filter (fun a => (t-a+(4*s:ℕ)) % (8*s:ℕ) = r)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨haI,haR⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbI,hbR⟩ := Finset.mem_filter.mp hb
    exact shift_residue_inj hs t haI hbI (haR.trans hbR.symm)
  exact (Finset.card_union_le _ _).trans (by have h1:=hfiber 0; have h2:=hfiber ((8*s:ℕ)-1); omega)

/-- The possible shifts putting `y` on a boundary cell layer. -/
def boundaryShifts {d : ℕ} (s : ℕ) (y : Point d) : Finset (Point d) :=
  Finset.univ.biUnion (fun j : Fin d => coordinateBox s 0 j (boundaryShiftCoord s (y j)))

theorem boundaryShifts_card {d : ℕ} {s : ℕ} (hs : 0 < s) (y : Point d) :
    (boundaryShifts s y).card ≤ 2*d*(2*s+1)^(d-1) := by
  calc
    (boundaryShifts s y).card ≤ ∑ j : Fin d,
        (coordinateBox s 0 j (boundaryShiftCoord s (y j))).card := Finset.card_biUnion_le
    _ = ∑ j : Fin d, (boundaryShiftCoord s (y j)).card * (2*s+1)^(d-1) := by simp [card_coordinateBox]
    _ ≤ ∑ _j : Fin d, 2*(2*s+1)^(d-1) :=
      Finset.sum_le_sum (fun j _ => Nat.mul_le_mul_right _ (boundaryShiftCoord_card hs (y j)))
    _ = 2*d*(2*s+1)^(d-1) := by simp; ring

theorem emod_pred_of_succ_zero {a R : ℤ} (hR : 0 < R) (hzero : (a+1)%R=0) :
    a%R=R-1 := by
  have hn := Int.emod_nonneg a (ne_of_gt hR)
  have hl := Int.emod_lt_of_pos a hR
  have hzero' : (a%R+1)%R=0 := by simpa only [Int.emod_add_emod] using hzero
  by_contra hne
  have hsmall : a%R+1 < R := by omega
  rw [Int.emod_eq_of_lt (by omega) hsmall] at hzero'
  omega

/-- An external boundary point of a union of complete cells must lie on the
first or last layer of its own coarse cell in one coordinate. -/
theorem type2_boundary_layer {d : ℕ} {n s : ℕ} (hs : 0 < s)
    {C : Finset (Point d)} {a y : Point d}
    (hy : y ∈ boundary (volume n) (type2Block n s C a)) :
    ∃ j, (y j-a j+(4*s:ℕ)) % (8*s:ℕ)=0 ∨
      (y j-a j+(4*s:ℕ)) % (8*s:ℕ)=(8*s:ℕ)-1 := by
  obtain ⟨hyV,hynot,x,hx,hxy⟩ := mem_boundary.mp hy
  have hxC := ((mem_type2Block hs).mp hx).2
  have hyC : cellOf s (y-a) ∉ C := by
    intro hc
    exact hynot ((mem_type2Block hs).mpr ⟨mem_cube.mp hyV,hc⟩)
  obtain ⟨j,hj,hother⟩ := hxy
  have hneq : (y j-a j+(4*s:ℕ)) / (8*s:ℕ) ≠
      (x j-a j+(4*s:ℕ)) / (8*s:ℕ) := by
    intro hjeq
    apply hyC
    have heq : cellOf s (y-a) = cellOf s (x-a) := by
      funext k
      by_cases hkj : k=j
      · subst k; exact hjeq
      · dsimp [cellOf]
        rw [hother k hkj]
    rwa [heq]
  have hR : (0:ℤ) < (8*s:ℕ) := by positivity
  refine ⟨j,?_⟩
  rcases hj with hj | hj
  · left
    by_contra hmod
    apply hneq
    exact LatticeGeometry.ediv_eq_of_successive hR (by omega) hmod
  · right
    have hmod : (x j-a j+(4*s:ℕ)) % (8*s:ℕ)=0 := by
      by_contra hmod
      apply hneq
      exact (LatticeGeometry.ediv_eq_of_successive hR (by omega) hmod).symm
    apply emod_pred_of_succ_zero hR
    have heq : y j-a j+(4*s:ℕ)+1 = x j-a j+(4*s:ℕ) := by omega
    rw [heq]
    exact hmod

theorem type2_boundary_shift {d : ℕ} {n s : ℕ} (hs : 0 < s)
    {C : Finset (Point d)} {a y : Point d} (ha : a ∈ shifts s)
    (hy : y ∈ boundary (volume n) (type2Block n s C a)) : a ∈ boundaryShifts s y := by
  obtain ⟨j,hj⟩ := type2_boundary_layer hs hy
  have ha' := mem_cube.mp ha
  apply Finset.mem_biUnion.mpr
  refine ⟨j,Finset.mem_univ _,mem_coordinateBox.mpr ⟨?_,?_⟩⟩
  · have haj : a j ∈ Finset.Icc (-(s:ℤ)) (s:ℤ) := by
      have h := ha' j
      simpa using h
    rcases hj with hj | hj
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨haj,hj⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨haj,hj⟩)
  · intro k _
    simpa using ha' k

theorem type2_boundary_count {d : ℕ} {good : Point d → Prop} {n s L : ℕ}
    (hs : 0 < s) (hevent : SmallClusters good n s L) (y : Point d) :
    (type2Boundary good n s y).card ≤ 2*d*(2*s+1)^(d-1) := by
  classical
  have hinj : Set.InjOn Prod.snd (type2Boundary good n s y).toSet := by
    intro p hp q hq heq
    obtain ⟨hpI,hpB⟩ := Finset.mem_filter.mp hp
    obtain ⟨hqI,hqB⟩ := Finset.mem_filter.mp hq
    exact Prod.ext (type2_closure_cluster_unique hs hevent hpI hqI (Or.inr hpB) (Or.inr hqB)) heq
  have hsub : (type2Boundary good n s y).image Prod.snd ⊆ boundaryShifts s y := by
    intro a ha
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hpI,hpB⟩ := Finset.mem_filter.mp hp
    have hshift := (Finset.mem_product.mp (Finset.mem_filter.mp hpI).1).2
    exact type2_boundary_shift hs hshift hpB
  calc
    (type2Boundary good n s y).card = ((type2Boundary good n s y).image Prod.snd).card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (boundaryShifts s y).card := Finset.card_le_card hsub
    _ ≤ 2*d*(2*s+1)^(d-1) := boundaryShifts_card hs y

/-- The complete boundary count of Lemma 3.3, including both types of blocks. -/
theorem boundary_count {d : ℕ} {good : Point d → Prop} {n s L : ℕ}
    (hs : 0 < s) (hevent : SmallClusters good n s L) (y : Point d) :
    J good n s y ≤ 4*d*(2*s+1)^(d-1) := by
  have h1 := type1_boundary_count good n s y
  have h2 := type2_boundary_count hs hevent y
  unfold J
  nlinarith

/-- No full bad component giving a nonempty permitted translate is omitted
from the finite index family. -/
theorem type2_index_complete {d : ℕ} {good : Point d → Prop} {n s L : ℕ}
    (hs : 0 < s) (hevent : SmallClusters good n s L) {C : Finset (Point d)}
    (hC : IsCluster good C) {a : Point d} (ha : a ∈ shifts s)
    (hB : (type2Block n s C a).Nonempty) : (C,a) ∈ type2Indices good n s := by
  classical
  obtain ⟨y,hy⟩ := hB
  obtain ⟨hyV,hyC⟩ := (mem_type2Block hs).mp hy
  let k := cellOf s (y-a)
  have hkroot : k ∈ relevantRoots n s := by
    apply Finset.mem_image.mpr
    refine ⟨y-a,mem_cube.mpr ?_,rfl⟩
    exact near_sub_shift hyV ha
  have hkbad : ¬ good k := isCluster_bad hC hyC
  have hkfin := (hevent k (relevant_center hs hkroot)).1
  let D := clusterFin good k
  have hD : D ∈ clusters good n s := Finset.mem_image.mpr
    ⟨k,Finset.mem_filter.mpr ⟨hkroot,hkbad⟩,rfl⟩
  have hkD : k ∈ D := (mem_clusterFin hkfin).mpr (badReach_refl hkbad)
  have heq : C=D := isCluster_eq_of_star hC (clusters_spec hs hevent hD).1 hyC hkD (near_refl 1 k)
  exact type2_index_of_mem (by rwa [heq]) ha hy

/-- The finite indexed family used by the physical block kernel. Equal vertex
sets arising from different centers or translations remain distinct indices. -/
abbrev BlockIndex {d : ℕ} (good : Point d → Prop) (n s : ℕ) :=
  Sum ↥(type1Indices good n s) ↥(type2Indices good n s)

def block {d : ℕ} {good : Point d → Prop} {n s : ℕ} :
    BlockIndex good n s → Finset (Point d)
  | Sum.inl w => type1Block n s w.val
  | Sum.inr p => type2Block n s p.val.1 p.val.2

theorem block_nonempty {d : ℕ} {good : Point d → Prop} {n s : ℕ}
    (i : BlockIndex good n s) : (block i).Nonempty := by
  classical
  cases i with
  | inl w => exact (Finset.mem_filter.mp w.property).2.2
  | inr p => exact (Finset.mem_filter.mp p.property).2

theorem block_subset_volume {d : ℕ} {good : Point d → Prop} {n s : ℕ}
    (i : BlockIndex good n s) : block i ⊆ volume n := by
  cases i <;> exact Finset.inter_subset_left

/-- Coverage `I_y` is literally the cardinality of the family indices containing `y`. -/
theorem card_block_cover {d : ℕ} (good : Point d → Prop) (n s : ℕ) (y : Point d) :
    (Finset.univ.filter (fun i : BlockIndex good n s => y ∈ block i)).card = I good n s y := by
  classical
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter,Fintype.sum_sum_type,block,I,
    type1Cover,type2Cover]
  congr 1
  · exact Finset.sum_coe_sort (type1Indices good n s) (fun w : Point d => if y ∈ type1Block n s w then (1:ℕ) else 0)
  · exact Finset.sum_coe_sort (type2Indices good n s) (fun p : Finset (Point d) × Point d => if y ∈ type2Block n s p.1 p.2 then (1:ℕ) else 0)

/-- The boundary count `J_y` is likewise the actual index cardinality. -/
theorem card_block_boundary {d : ℕ} (good : Point d → Prop) (n s : ℕ) (y : Point d) :
    (Finset.univ.filter (fun i : BlockIndex good n s => y ∈ boundary (volume n) (block i))).card =
      J good n s y := by
  classical
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter,Fintype.sum_sum_type,block,J,
    type1Boundary,type2Boundary]
  congr 1
  · exact Finset.sum_coe_sort (type1Indices good n s) (fun w : Point d => if y ∈ boundary (volume n) (type1Block n s w) then (1:ℕ) else 0)
  · exact Finset.sum_coe_sort (type2Indices good n s) (fun p : Finset (Point d) × Point d => if y ∈ boundary (volume n) (type2Block n s p.1 p.2) then (1:ℕ) else 0)

theorem block_size_bound {d : ℕ} {good : Point d → Prop} {n s L : ℕ}
    (hs : 0 < s) (hL : 1 ≤ L) (hevent : SmallClusters good n s L)
    (i : BlockIndex good n s) : (block i).card ≤ L*(8*s)^d := by
  cases i with
  | inl w =>
    calc
      (block (Sum.inl w)).card ≤ (2*s+1)^d := type1_size n s w.val
      _ ≤ (8*s)^d := Nat.pow_le_pow_left (by omega) d
      _ ≤ L*(8*s)^d := by simpa using Nat.mul_le_mul_right ((8*s)^d) hL
  | inr p =>
    obtain ⟨hp,_⟩ := Finset.mem_filter.mp p.property
    have hC := (clusters_spec hs hevent (Finset.mem_product.mp hp).1).2
    exact (type2_size n s p.val.1 p.val.2).trans (Nat.mul_le_mul_right _ hC)

def maxBlockSize {d : ℕ} (good : Point d → Prop) (n s : ℕ) : ℕ :=
  Finset.univ.sup (fun i : BlockIndex good n s => (block i).card)

theorem maxBlockSize_bound {d : ℕ} {good : Point d → Prop} {n s L : ℕ}
    (hs : 0 < s) (hL : 1 ≤ L) (hevent : SmallClusters good n s L) :
    maxBlockSize good n s ≤ L*(8*s)^d :=
  Finset.sup_le (fun i _ => block_size_bound hs hL hevent i)

theorem block_boundary_good {d : ℕ} {good : Point d → Prop} {n s L : ℕ}
    (hs : 0 < s) (hevent : SmallClusters good n s L)
    (i : BlockIndex good n s) {y : Point d} (hy : y ∈ boundary (volume n) (block i)) :
    ∃ k, good k ∧ Near (8*s) y (center s k) := by
  cases i with
  | inl w => exact type1_boundary_good hs w.property hy
  | inr p => exact type2_boundary_good hs hevent p.property hy

/-- The source's bounds in units of `R=8s`, with explicit dimension constants.
The natural inequality `R^d≤4^d I_y` is the lower bound with `c=4^{-d}`. -/
theorem covering_scaled {d : ℕ} {good : Point d → Prop} {n s L : ℕ}
    (hs : 0 < s) (hevent : SmallClusters good n s L) {y : Point d} (hy : y ∈ volume n) :
    (8*s)^d ≤ 4^d * I good n s y ∧
      I good n s y ≤ 2*(8*s)^d ∧ J good n s y ≤ 4*d*(8*s)^(d-1) := by
  have hlo := covering_lower hs hevent hy
  have hhi := covering_upper hs hevent y
  have hJ := boundary_count hs hevent y
  have hbase : 2*s+1 ≤ 8*s := by omega
  refine ⟨?_,hhi.trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hbase d)),
    hJ.trans (Nat.mul_le_mul_left (4*d) (Nat.pow_le_pow_left hbase (d-1)))⟩
  calc
    (8*s)^d ≤ (4*(2*s+1))^d := Nat.pow_le_pow_left (by omega) d
    _ = 4^d * (2*s+1)^d := Nat.mul_pow _ _ _
    _ ≤ 4^d * I good n s y := Nat.mul_le_mul_left _ hlo

/-- Full deterministic Lemma 3.3 for the actual indexed covering. Its only
random-environment input is the finite relevant bad-cluster event from Lemma 3.2. -/
theorem lemma_3_3 {d : ℕ} {good : Point d → Prop} {n s L : ℕ}
    (hs : 0 < s) (hL : 1 ≤ L) (hevent : SmallClusters good n s L) :
    maxBlockSize good n s ≤ L*(8*s)^d ∧
    (∀ y ∈ volume n,
      (8*s)^d ≤ 4^d * I good n s y ∧
        I good n s y ≤ 2*(8*s)^d ∧ J good n s y ≤ 4*d*(8*s)^(d-1)) ∧
    ∀ (i : BlockIndex good n s) y,
      y ∈ boundary (volume n) (block i) → ∃ k, good k ∧ Near (8*s) y (center s k) :=
  ⟨maxBlockSize_bound hs hL hevent,
    fun _ hy => covering_scaled hs hevent hy,
    fun i _ hy => block_boundary_good hs hevent i hy⟩

end Paper09.BlockCovering
