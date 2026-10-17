import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.Fin.VecNotation
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.DeriveFintype

/-!
The graph and the ordered cubical chains in §2 of the paper.

A list position is a particle label.  In particular none of the constructions
below quotients by permutations.  The ambient free module uses lists, so the
four-particle groups are its submodules supported on the valid length-four
lists of the indicated degree.
-/
namespace Paper23
namespace Cubical

abbrev CoreVertex := Fin 6
abbrev CoreEdge := Fin 13
abbrev Vertex := Fin 32
abbrev Edge := Fin 39

/-- The ordered and oriented thirteen-edge list of equation (1). -/
def coreEndpoints : CoreEdge → CoreVertex × CoreVertex := ![
  (0,1), (0,1), (0,1), (0,2), (0,3), (1,4), (1,5),
  (2,3), (2,4), (2,5), (3,4), (3,5), (4,5)]

/-- Each core edge is replaced by the path `u, 6+2e, 7+2e, v`. -/
def endpoints (e : Edge) : Vertex × Vertex :=
  let k : CoreEdge := ⟨e.val / 3, by omega⟩
  let u : Vertex := ⟨(coreEndpoints k).1.val, by omega⟩
  let v : Vertex := ⟨(coreEndpoints k).2.val, by omega⟩
  let x : Vertex := ⟨6 + 2 * k.val, by omega⟩
  let y : Vertex := ⟨7 + 2 * k.val, by omega⟩
  if e.val % 3 = 0 then (u,x)
  else if e.val % 3 = 1 then (x,y) else (y,v)

inductive GraphCell where
  | vertex (v : Vertex)
  | edge (e : Edge)
  deriving DecidableEq, Fintype

/-- Vertex set of the closure of a graph cell. This also tests disjointness
of edge closures: the graph has no loops, and distinct open edges meet only
at an endpoint. Edge identity is retained by `GraphCell.edge`. -/
def GraphCell.vertices : GraphCell → Finset Vertex
  | .vertex v => {v}
  | .edge e => {(endpoints e).1, (endpoints e).2}

def GraphCell.dimension : GraphCell → ℕ
  | .vertex _ => 0
  | .edge _ => 1

abbrev RawCube := List GraphCell

def degree (c : RawCube) : ℕ := (c.map GraphCell.dimension).sum

def ClosureDisjoint (a b : GraphCell) : Prop := Disjoint a.vertices b.vertices

instance (a b : GraphCell) : Decidable (ClosureDisjoint a b) := inferInstanceAs
  (Decidable (Disjoint a.vertices b.vertices))

/-- Exactly the products of four graph cells with disjoint closures. -/
def IsCube (c : RawCube) : Prop := c.length = 4 ∧ c.Pairwise ClosureDisjoint

abbrev Cube := {c : RawCube // IsCube c}
abbrev CubeInDegree (q : ℕ) := {c : Cube // degree c.val = q}

abbrev RawChain := RawCube →₀ ℤ

/-- The integral cubical group is free on the labelled degree-q cubes. -/
abbrev Chain (q : ℕ) := CubeInDegree q →₀ ℤ

/-- The equivalent supported-submodule presentation inside the ambient group. -/
def Chains (q : ℕ) : Submodule ℤ RawChain :=
  Finsupp.supported ℤ ℤ {c | IsCube c ∧ degree c = q}

noncomputable def basis (c : RawCube) : RawChain := Finsupp.single c 1

noncomputable def prepend (a : GraphCell) : RawChain →ₗ[ℤ] RawChain :=
  Finsupp.lmapDomain ℤ ℤ (List.cons a)

@[simp] theorem prepend_basis (a : GraphCell) (c : RawCube) :
    prepend a (basis c) = basis (a :: c) := by
  simp [prepend, basis, Finsupp.lmapDomain_apply]

/-- Boundary in particle-label order, used as an auxiliary coordinate system. -/
noncomputable def labelBoundaryBasis : RawCube → RawChain
  | [] => 0
  | .vertex v :: c => prepend (.vertex v) (labelBoundaryBasis c)
  | .edge e :: c => basis (.vertex (endpoints e).2 :: c) -
      basis (.vertex (endpoints e).1 :: c) - prepend (.edge e) (labelBoundaryBasis c)

noncomputable def labelBoundary : RawChain →ₗ[ℤ] RawChain :=
  Finsupp.linearCombination ℤ labelBoundaryBasis

@[simp] theorem labelBoundary_basis (c : RawCube) :
    labelBoundary (basis c) = labelBoundaryBasis c := by
  simp [labelBoundary, basis]

@[simp] theorem labelBoundaryBasis_nil : labelBoundaryBasis [] = 0 := rfl
@[simp] theorem labelBoundaryBasis_vertex (v : Vertex) (c : RawCube) :
    labelBoundaryBasis (.vertex v :: c) = prepend (.vertex v) (labelBoundaryBasis c) := rfl
@[simp] theorem labelBoundaryBasis_edge (e : Edge) (c : RawCube) :
    labelBoundaryBasis (.edge e :: c) = basis (.vertex (endpoints e).2 :: c) -
      basis (.vertex (endpoints e).1 :: c) - prepend (.edge e) (labelBoundaryBasis c) := rfl

@[simp] theorem labelBoundary_prepend_vertex (v : Vertex) (x : RawChain) :
    labelBoundary (prepend (.vertex v) x) = prepend (.vertex v) (labelBoundary x) := by
  have h : labelBoundary.comp (prepend (.vertex v)) =
      (prepend (.vertex v)).comp labelBoundary := by
    apply Finsupp.lhom_ext
    intro c n
    simp [labelBoundary, prepend, Finsupp.lmapDomain_apply]
  exact LinearMap.congr_fun h x

@[simp] theorem labelBoundary_prepend_edge (e : Edge) (x : RawChain) :
    labelBoundary (prepend (.edge e) x) =
      prepend (.vertex (endpoints e).2) x - prepend (.vertex (endpoints e).1) x -
      prepend (.edge e) (labelBoundary x) := by
  have h : labelBoundary.comp (prepend (.edge e)) =
      prepend (.vertex (endpoints e).2) - prepend (.vertex (endpoints e).1) -
      (prepend (.edge e)).comp labelBoundary := by
    apply Finsupp.lhom_ext
    intro c n
    simp [labelBoundary, prepend, Finsupp.lmapDomain_apply, smul_sub, basis]
  exact LinearMap.congr_fun h x

/-- The boundary relation is proved from the endpoint formula, with no
hypothesis asserting that it is a chain complex. -/
theorem labelBoundary_squared_basis (c : RawCube) :
    labelBoundary (labelBoundaryBasis c) = 0 := by
  induction c with
  | nil => simp
  | cons a c ih =>
    cases a with
    | vertex v => simp [ih]
    | edge e => simp [ih, map_sub]

theorem labelBoundary_squared (x : RawChain) :
    labelBoundary (labelBoundary x) = 0 := by
  have h : labelBoundary.comp labelBoundary = 0 := by
    apply Finsupp.lhom_ext
    intro c n
    change labelBoundary (labelBoundary (Finsupp.single c n)) = 0
    have hs : Finsupp.single c n = n • basis c := by simp [basis]
    rw [hs, map_smul, map_smul, labelBoundary_basis, labelBoundary_squared_basis, smul_zero]
  exact LinearMap.congr_fun h x

/-- Number of moving graph edges strictly smaller than e. -/
def smaller (e : Edge) (c : RawCube) : ℕ :=
  (c.filter fun a => match a with
    | .vertex _ => false
    | .edge f => decide (f < e)).length

/-- Sign of the permutation from label order to increasing moving-edge order.
Equal edges are kept in label order; they cannot occur in a valid cube. -/
def orientation : RawCube → ℤ :=
  List.rec 1 fun a c ih => match a with
    | .vertex _ => ih
    | .edge e => (-1) ^ smaller e c * ih

@[simp] theorem orientation_squared (c : RawCube) : orientation c * orientation c = 1 := by
  induction c with
  | nil => rfl
  | cons a c ih =>
    cases a with
    | vertex v => exact ih
    | edge e =>
      simp only [orientation]
      calc
        ((-1 : ℤ) ^ smaller e c * orientation c) *
            ((-1) ^ smaller e c * orientation c) =
            ((-1 : ℤ) ^ smaller e c * (-1) ^ smaller e c) *
              (orientation c * orientation c) := by ring
        _ = 1 := by rw [← mul_pow]; simp [ih]

noncomputable def reorient : RawChain →ₗ[ℤ] RawChain :=
  Finsupp.linearCombination ℤ fun c => orientation c • basis c

@[simp] theorem reorient_basis (c : RawCube) :
    reorient (basis c) = orientation c • basis c := by simp [reorient, basis]

@[simp] theorem reorient_squared (x : RawChain) : reorient (reorient x) = x := by
  have h : reorient.comp reorient = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro c n
    change reorient (reorient (Finsupp.single c n)) = Finsupp.single c n
    have hs : Finsupp.single c n = n • basis c := by simp [basis]
    rw [hs, map_smul, map_smul, reorient_basis, map_smul, reorient_basis,
      smul_smul, smul_smul, mul_assoc, orientation_squared, mul_one]
  exact LinearMap.congr_fun h x

/-- The boundary with the paper's increasing-moving-edge orientation. -/
noncomputable def boundary : RawChain →ₗ[ℤ] RawChain :=
  reorient.comp (labelBoundary.comp reorient)

/-- The actual endpoint differential satisfies d²=0, including before the
restriction to the disjoint-closure four-particle subcomplex. -/
theorem boundary_squared (x : RawChain) : boundary (boundary x) = 0 := by
  simp [boundary, labelBoundary_squared]


@[simp] theorem degree_nil : degree [] = 0 := rfl
@[simp] theorem degree_vertex (v : Vertex) (c : RawCube) :
    degree (.vertex v :: c) = degree c := by simp [degree, GraphCell.dimension]
@[simp] theorem degree_edge (e : Edge) (c : RawCube) :
    degree (.edge e :: c) = 1 + degree c := by simp [degree, GraphCell.dimension]
@[simp] theorem smaller_nil (e : Edge) : smaller e [] = 0 := rfl
@[simp] theorem smaller_vertex (e : Edge) (v : Vertex) (c : RawCube) :
    smaller e (.vertex v :: c) = smaller e c := by simp [smaller]
@[simp] theorem smaller_edge (e f : Edge) (c : RawCube) :
    smaller e (.edge f :: c) = (if f < e then 1 else 0) + smaller e c := by
  by_cases h : f < e <;> simp [smaller, h, Nat.add_comm]
@[simp] theorem smaller_append (e : Edge) (a b : RawCube) :
    smaller e (a ++ b) = smaller e a + smaller e b := by simp [smaller]

/-- Sign contributed by all moving edges smaller than e. -/
def movingSign (e : Edge) (c : RawCube) : ℤ := (-1) ^ smaller e c

@[simp] theorem movingSign_squared (e : Edge) (c : RawCube) :
    movingSign e c * movingSign e c = 1 := by rw [movingSign, ← mul_pow]; simp
@[simp] theorem movingSign_append (e : Edge) (a b : RawCube) :
    movingSign e (a ++ b) = movingSign e a * movingSign e b := by
  simp [movingSign, pow_add]
@[simp] theorem movingSign_vertex (e : Edge) (v : Vertex) (c : RawCube) :
    movingSign e (.vertex v :: c) = movingSign e c := by simp [movingSign]
@[simp] theorem movingSign_edge (e f : Edge) (c : RawCube) :
    movingSign e (.edge f :: c) = (if f < e then -1 else 1) * movingSign e c := by
  by_cases h : f < e <;> simp [movingSign, pow_add, h]

/-- Removing the moving coordinate e changes orientations by exactly its
rank among moving edges.  The prefix contains earlier particle labels. -/
theorem orientation_face_sign (pre post : RawCube) (e : Edge) (v : Vertex)
    (hne : GraphCell.edge e ∉ pre) :
    orientation (pre ++ .edge e :: post) * orientation (pre ++ .vertex v :: post) *
      (-1 : ℤ) ^ degree pre = movingSign e (pre ++ post) := by
  induction pre with
  | nil =>
    simp only [List.nil_append, degree_nil, pow_zero, mul_one, orientation]
    change (-1 : ℤ) ^ smaller e post * orientation post * orientation post = movingSign e post
    rw [mul_assoc, orientation_squared, mul_one]
    rfl
  | cons a pre ih =>
    have hpre : GraphCell.edge e ∉ pre := fun h => hne (by simp [h])
    specialize ih hpre
    cases a with
    | vertex w => simpa [orientation] using ih
    | edge f =>
      have hef : e ≠ f := by
        intro h
        apply hne
        simp [h]
      have hsign : (if e < f then (-1 : ℤ) else 1) * (-1) =
          (if f < e then (-1 : ℤ) else 1) := by
        rcases lt_or_gt_of_ne hef with h | h <;> simp [h, not_lt_of_gt h]
      change
        (movingSign f (pre ++ .edge e :: post) * orientation (pre ++ .edge e :: post)) *
        (movingSign f (pre ++ .vertex v :: post) * orientation (pre ++ .vertex v :: post)) *
        (-1 : ℤ) ^ (1 + degree pre) = movingSign e (.edge f :: (pre ++ post))
      simp only [movingSign_append, movingSign_edge, movingSign_vertex, pow_add, pow_one]
      calc
        _ = (movingSign f pre * movingSign f pre) *
              (movingSign f post * movingSign f post) *
              ((if e < f then (-1 : ℤ) else 1) * (-1)) *
              (orientation (pre ++ .edge e :: post) *
                orientation (pre ++ .vertex v :: post) * (-1 : ℤ) ^ degree pre) := by ring
        _ = _ := by rw [movingSign_squared, movingSign_squared, hsign, ih, movingSign_append]; ring

/-- Each face, expressed in the increasing-edge basis, has the coefficient
`(-1)^(number of smaller moving edges)` in equation (3). -/
theorem reorient_face_term (pre post : RawCube) (e : Edge)
    (hne : GraphCell.edge e ∉ pre) :
    reorient (orientation (pre ++ .edge e :: post) •
      ((-1 : ℤ) ^ degree pre •
        (basis (pre ++ .vertex (endpoints e).2 :: post) -
         basis (pre ++ .vertex (endpoints e).1 :: post)))) =
    movingSign e (pre ++ post) •
        (basis (pre ++ .vertex (endpoints e).2 :: post) -
         basis (pre ++ .vertex (endpoints e).1 :: post)) := by
  simp only [map_smul, map_sub, reorient_basis, smul_sub, smul_smul]
  have hp := orientation_face_sign pre post e (endpoints e).2 hne
  have hm := orientation_face_sign pre post e (endpoints e).1 hne
  have hp' : orientation (pre ++ .edge e :: post) *
      (-1 : ℤ)^degree pre * orientation (pre ++ .vertex (endpoints e).2 :: post) =
      movingSign e (pre ++ post) := by
    calc
      _ = orientation (pre ++ .edge e :: post) *
          orientation (pre ++ .vertex (endpoints e).2 :: post) * (-1 : ℤ)^degree pre := by ring
      _ = _ := hp
  have hm' : orientation (pre ++ .edge e :: post) *
      (-1 : ℤ)^degree pre * orientation (pre ++ .vertex (endpoints e).1 :: post) =
      movingSign e (pre ++ post) := by
    calc
      _ = orientation (pre ++ .edge e :: post) *
          orientation (pre ++ .vertex (endpoints e).1 :: post) * (-1 : ℤ)^degree pre := by ring
      _ = _ := hm
  rw [hp', hm']


/-- A face replaces one edge by one endpoint, preserving its particle label. -/
inductive Face : RawCube → RawCube → Prop
  | initial (e : Edge) (c : RawCube) :
      Face (.vertex (endpoints e).1 :: c) (.edge e :: c)
  | terminal (e : Edge) (c : RawCube) :
      Face (.vertex (endpoints e).2 :: c) (.edge e :: c)
  | cons (a : GraphCell) {f c : RawCube} : Face f c → Face (a :: f) (a :: c)

@[simp] theorem endpoint_initial_subset (e : Edge) :
    (GraphCell.vertex (endpoints e).1).vertices ⊆ (GraphCell.edge e).vertices := by
  simp [GraphCell.vertices]
@[simp] theorem endpoint_terminal_subset (e : Edge) :
    (GraphCell.vertex (endpoints e).2).vertices ⊆ (GraphCell.edge e).vertices := by
  simp [GraphCell.vertices]

theorem Face.length_eq {f c : RawCube} (h : Face f c) : f.length = c.length := by
  induction h with
  | initial => rfl
  | terminal => rfl
  | cons a h ih => simpa using ih

theorem Face.degree_eq {f c : RawCube} (h : Face f c) : degree f + 1 = degree c := by
  induction h with
  | initial => simp; omega
  | terminal => simp; omega
  | cons a h ih => cases a <;> simp_all <;> omega

/-- Every new cell has its closure inside that of the corresponding old cell. -/
theorem Face.cell_subset {f c : RawCube} (h : Face f c) :
    ∀ a ∈ f, ∃ b ∈ c, a.vertices ⊆ b.vertices := by
  induction h with
  | initial e c =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨.edge e, by simp, endpoint_initial_subset e⟩
    · exact ⟨a, by simp [ha], Finset.Subset.refl _⟩
  | terminal e c =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨.edge e, by simp, endpoint_terminal_subset e⟩
    · exact ⟨a, by simp [ha], Finset.Subset.refl _⟩
  | cons b h ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨a, by simp, Finset.Subset.refl _⟩
    · obtain ⟨d, hd, had⟩ := ih a ha
      exact ⟨d, by simp [hd], had⟩

theorem Face.pairwise {f c : RawCube} (h : Face f c)
    (hc : c.Pairwise ClosureDisjoint) : f.Pairwise ClosureDisjoint := by
  induction h with
  | initial e c =>
    rcases List.pairwise_cons.mp hc with ⟨hh, ht⟩
    apply List.pairwise_cons.mpr
    refine ⟨?_, ht⟩
    intro a ha
    exact Finset.disjoint_of_subset_left (endpoint_initial_subset e) (hh a ha)
  | terminal e c =>
    rcases List.pairwise_cons.mp hc with ⟨hh, ht⟩
    apply List.pairwise_cons.mpr
    refine ⟨?_, ht⟩
    intro a ha
    exact Finset.disjoint_of_subset_left (endpoint_terminal_subset e) (hh a ha)
  | cons a h ih =>
    rcases List.pairwise_cons.mp hc with ⟨hh, ht⟩
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih ht⟩
    intro b hb
    obtain ⟨d, hd, hbd⟩ := h.cell_subset b hb
    exact Finset.disjoint_of_subset_right hbd (hh d hd)

theorem Face.isCube {f c : RawCube} (h : Face f c) (hc : IsCube c) : IsCube f :=
  ⟨h.length_eq.trans hc.1, h.pairwise hc.2⟩

/-- Restriction to a set of basis elements can be proved on generators. -/
theorem map_mem_supported {s : Set RawCube} (T : Submodule ℤ RawChain)
    (L : RawChain →ₗ[ℤ] RawChain)
    (h : ∀ c ∈ s, L (basis c) ∈ T) (x : RawChain)
    (hx : x ∈ Finsupp.supported ℤ ℤ s) : L x ∈ T := by
  classical
  rw [← x.sum_single]
  simp only [Finsupp.sum, map_sum]
  apply Submodule.sum_mem
  intro c hc
  have hs : Finsupp.single c (x c) = x c • basis c := by simp [basis]
  rw [hs, map_smul]
  exact T.smul_mem (x c) (h c (hx hc))

theorem prepend_mem_supported {s t : Set RawCube} (a : GraphCell)
    (h : ∀ c ∈ s, a :: c ∈ t) (x : RawChain)
    (hx : x ∈ Finsupp.supported ℤ ℤ s) :
    prepend a x ∈ Finsupp.supported ℤ ℤ t := by
  apply map_mem_supported _ _ ?_ x hx
  intro c hc
  rw [prepend_basis]
  exact Finsupp.single_mem_supported ℤ 1 (h c hc)

/-- The support of the endpoint boundary consists only of actual faces. -/
theorem labelBoundaryBasis_faces (c : RawCube) :
    labelBoundaryBasis c ∈ Finsupp.supported ℤ ℤ {f | Face f c} := by
  induction c with
  | nil => exact (Finsupp.supported ℤ ℤ _).zero_mem
  | cons a c ih =>
    cases a with
    | vertex v =>
      apply prepend_mem_supported (.vertex v) ?_ _ ih
      intro f hf
      exact Face.cons _ hf
    | edge e =>
      apply Submodule.sub_mem
      · apply Submodule.sub_mem
        · exact Finsupp.single_mem_supported ℤ 1 (Face.terminal e c)
        · exact Finsupp.single_mem_supported ℤ 1 (Face.initial e c)
      · apply prepend_mem_supported (.edge e) ?_ _ ih
        intro f hf
        exact Face.cons _ hf

theorem reorient_mem_supported {s : Set RawCube} (x : RawChain)
    (hx : x ∈ Finsupp.supported ℤ ℤ s) :
    reorient x ∈ Finsupp.supported ℤ ℤ s := by
  apply map_mem_supported _ _ ?_ x hx
  intro c hc
  rw [reorient_basis]
  exact (Finsupp.supported ℤ ℤ s).smul_mem _ (Finsupp.single_mem_supported ℤ 1 hc)

theorem boundary_basis_faces (c : RawCube) :
    boundary (basis c) ∈ Finsupp.supported ℤ ℤ {f | Face f c} := by
  simp only [boundary, LinearMap.comp_apply, reorient_basis, map_smul, labelBoundary_basis]
  exact (Finsupp.supported ℤ ℤ _).smul_mem _
    (reorient_mem_supported _ (labelBoundaryBasis_faces c))

/-- The explicit boundary preserves disjointness and the four labels, and
reduces degree by one. -/
theorem boundary_mem_chains (q : ℕ) (x : RawChain) (hx : x ∈ Chains (q+1)) :
    boundary x ∈ Chains q := by
  apply map_mem_supported _ _ ?_ x hx
  intro c hc
  change IsCube c ∧ degree c = q+1 at hc
  apply Finsupp.supported_mono ?_ (boundary_basis_faces c)
  intro f hf
  exact ⟨hf.isCube hc.1, by have hd := hf.degree_eq; omega⟩

/-- The cellular boundary on the actual ordered four-particle cubical groups. -/
noncomputable def differential (q : ℕ) : Chains (q+1) →ₗ[ℤ] Chains q :=
  (boundary.comp (Chains (q+1)).subtype).codRestrict (Chains q)
    (fun x => boundary_mem_chains q x.val x.property)

/-- The chain-complex relation on the disjoint-closure subcomplex. -/
theorem differential_squared (q : ℕ) (x : Chains (q+2)) :
    differential q (differential (q+1) x) = 0 := by
  apply Subtype.ext
  exact boundary_squared x.val


/-- A moving coordinate together with the particle labels before and after it. -/
structure FaceData where
  pre : RawCube
  edge : Edge
  post : RawCube

def FaceData.cube (t : FaceData) : RawCube := t.pre ++ .edge t.edge :: t.post

def FaceData.lower (t : FaceData) : RawCube :=
  t.pre ++ .vertex (endpoints t.edge).1 :: t.post

def FaceData.upper (t : FaceData) : RawCube :=
  t.pre ++ .vertex (endpoints t.edge).2 :: t.post

def FaceData.prepend (a : GraphCell) (t : FaceData) : FaceData :=
  ⟨a :: t.pre, t.edge, t.post⟩

def faces : RawCube → List FaceData :=
  List.rec [] fun a c ih => match a with
    | .vertex v => ih.map (FaceData.prepend (.vertex v))
    | .edge e => ⟨[], e, c⟩ :: ih.map (FaceData.prepend (.edge e))

@[simp] theorem faces_vertex (v : Vertex) (c : RawCube) :
    faces (.vertex v :: c) = (faces c).map (FaceData.prepend (.vertex v)) := rfl

@[simp] theorem faces_edge (e : Edge) (c : RawCube) :
    faces (.edge e :: c) = ⟨[], e, c⟩ :: (faces c).map (FaceData.prepend (.edge e)) := rfl

noncomputable def FaceData.labelTerm (t : FaceData) : RawChain :=
  (-1 : ℤ) ^ degree t.pre • (basis t.upper - basis t.lower)

noncomputable def FaceData.movingTerm (t : FaceData) : RawChain :=
  movingSign t.edge (t.pre ++ t.post) • (basis t.upper - basis t.lower)

@[simp] theorem labelTerm_prepend_vertex (v : Vertex) (t : FaceData) :
    (t.prepend (.vertex v)).labelTerm = prepend (.vertex v) t.labelTerm := by
  simp [FaceData.labelTerm, FaceData.prepend, FaceData.upper, FaceData.lower,
    map_smul, map_sub]

@[simp] theorem labelTerm_prepend_edge (e : Edge) (t : FaceData) :
    (t.prepend (.edge e)).labelTerm = -prepend (.edge e) t.labelTerm := by
  simp [FaceData.labelTerm, FaceData.prepend, FaceData.upper, FaceData.lower,
    map_smul, map_sub, pow_add, mul_smul]

/-- The recursive endpoint boundary is the sum over all moving coordinates. -/
theorem labelBoundaryBasis_eq_faces (c : RawCube) :
    labelBoundaryBasis c = ((faces c).map FaceData.labelTerm).sum := by
  induction c with
  | nil => simp [faces]
  | cons a c ih =>
    cases a with
    | vertex v =>
      simp only [faces_vertex, labelBoundaryBasis_vertex, List.map_map]
      rw [ih, map_list_sum]
      simp only [List.map_map, Function.comp_def, labelTerm_prepend_vertex]
    | edge e =>
      simp only [faces_edge, labelBoundaryBasis_edge, List.map_cons, List.sum_cons, List.map_map]
      have h0 : (FaceData.mk [] e c).labelTerm =
          basis (.vertex (endpoints e).2 :: c) - basis (.vertex (endpoints e).1 :: c) := by
        simp [FaceData.labelTerm, FaceData.upper, FaceData.lower]
      rw [h0, ih, map_list_sum]
      simp only [Function.comp_def, labelTerm_prepend_edge]
      have hn : (List.map (fun x : FaceData => -prepend (.edge e) x.labelTerm) (faces c)).sum =
          -(List.map (fun x : FaceData => prepend (.edge e) x.labelTerm) (faces c)).sum := by
        induction faces c with
        | nil => simp
        | cons t l hl => simp [hl, add_comm]
      rw [hn, List.map_map]
      simp [Function.comp_def, sub_eq_add_neg]

theorem faces_spec {c : RawCube} {t : FaceData} (ht : t ∈ faces c) : t.cube = c := by
  induction c generalizing t with
  | nil => simp [faces] at ht
  | cons a c ih =>
    cases a with
    | vertex v =>
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
      simpa [FaceData.cube, FaceData.prepend] using congrArg (List.cons (.vertex v)) (ih hu)
    | edge e =>
      rcases List.mem_cons.mp ht with rfl | ht
      · rfl
      · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
        simpa [FaceData.cube, FaceData.prepend] using congrArg (List.cons (.edge e)) (ih hu)

theorem edge_not_mem_prefix {pre post : RawCube} {e : Edge}
    (hc : (pre ++ .edge e :: post).Pairwise ClosureDisjoint) :
    GraphCell.edge e ∉ pre := by
  intro he
  have hd : ClosureDisjoint (.edge e) (.edge e) :=
    (List.pairwise_append.mp hc).2.2 (.edge e) he (.edge e) (by simp)
  have hmem : (endpoints e).1 ∈ (GraphCell.edge e).vertices := by simp [GraphCell.vertices]
  exact Finset.disjoint_left.mp hd hmem hmem

theorem reorient_faceTerm {c : RawCube} (hc : c.Pairwise ClosureDisjoint)
    {t : FaceData} (ht : t ∈ faces c) :
    reorient (orientation c • t.labelTerm) = t.movingTerm := by
  have hspec := faces_spec ht
  rw [← hspec] at hc ⊢
  exact reorient_face_term t.pre t.post t.edge (edge_not_mem_prefix hc)

/-- Equation (3) of the paper, for every labelled disjoint-closure cube.
The index `smaller` is the zero-based position of its moving edge in the
increasing-edge ordering. Faces retain all the original list positions. -/
theorem boundary_basis_eq_moving_faces (c : RawCube) (hc : c.Pairwise ClosureDisjoint) :
    boundary (basis c) = ((faces c).map FaceData.movingTerm).sum := by
  simp only [boundary, LinearMap.comp_apply, reorient_basis, map_smul,
    labelBoundary_basis, labelBoundaryBasis_eq_faces]
  rw [← map_smul, List.smul_sum, map_list_sum]
  simp only [List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  exact reorient_faceTerm hc ht

end Cubical
end Paper23
