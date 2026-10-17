import Paper23.CertificateCocycleSoundness

/-! Explicit finite cofaces, with signs certified against the original boundary. -/
namespace Paper23.CertificateChecks
open Cubical

/-- Incident edges, computed from the exact subdivided source graph and checked below. -/
def incidentEdges : Vertex → List Edge := ![
  [0,3,6,9,12],
  [2,5,8,15,18],
  [11,21,24,27],
  [14,23,30,33],
  [17,26,32,36],
  [20,29,35,38],
  [0,1],
  [1,2],
  [3,4],
  [4,5],
  [6,7],
  [7,8],
  [9,10],
  [10,11],
  [12,13],
  [13,14],
  [15,16],
  [16,17],
  [18,19],
  [19,20],
  [21,22],
  [22,23],
  [24,25],
  [25,26],
  [27,28],
  [28,29],
  [30,31],
  [31,32],
  [33,34],
  [34,35],
  [36,37],
  [37,38]]

theorem incidentEdges_membership : ∀ (v : Vertex) (e : Edge),
    e ∈ incidentEdges v ↔ (endpoints e).1 = v ∨ (endpoints e).2 = v := by decide +kernel

theorem incidentEdges_nodup : ∀ v : Vertex, (incidentEdges v).Nodup := by decide +kernel

theorem list_map_sum_toFinset {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (l : List α) (f : α → M) (hn : l.Nodup) :
    (l.map f).sum = ∑ a ∈ l.toFinset, f a := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rcases List.nodup_cons.mp hn with ⟨ha,hl⟩
    simp [ih hl,ha]

/-- The full transpose sum can be evaluated on the certified incident list. -/
theorem vertexCofaces_incident (v : Vertex) (c : RawCube) :
    ((incidentEdges v).map fun e => vertexIncidence v e • basis (.edge e :: c)).sum =
      vertexCofaces v c := by
  classical
  rw [list_map_sum_toFinset _ _ (incidentEdges_nodup v)]
  unfold vertexCofaces
  apply Finset.sum_subset (Finset.subset_univ _)
  intro e he hnot
  have hn : e ∉ incidentEdges v := by simpa using hnot
  have hinc := mt (incidentEdges_membership v e).mpr hn
  have hs : (endpoints e).1 ≠ v := fun h => hinc (Or.inl h)
  have ht : (endpoints e).2 ≠ v := fun h => hinc (Or.inr h)
  simp [vertexIncidence,hs,ht]

structure CoFaceSlot where
  pre : RawCube
  vertex : Vertex
  post : RawCube

def CoFaceSlot.cube (t : CoFaceSlot) : RawCube := t.pre ++ .vertex t.vertex :: t.post

def CoFaceSlot.expanded (t : CoFaceSlot) (e : Edge) : RawCube :=
  t.pre ++ .edge e :: t.post

def CoFaceSlot.prepend (a : GraphCell) (t : CoFaceSlot) : CoFaceSlot :=
  ⟨a :: t.pre,t.vertex,t.post⟩

def cofaceSlots (c : RawCube) : List CoFaceSlot :=
  List.rec [] (fun a c rec =>
    match a with
    | .vertex v => ⟨[],v,c⟩ :: rec.map (CoFaceSlot.prepend (.vertex v))
    | .edge e => rec.map (CoFaceSlot.prepend (.edge e))) c

theorem cofaceSlots_nil : cofaceSlots [] = [] := rfl

theorem cofaceSlots_vertex (v : Vertex) (c : RawCube) :
    cofaceSlots (.vertex v :: c) =
      ⟨[],v,c⟩ :: (cofaceSlots c).map (CoFaceSlot.prepend (.vertex v)) := rfl

theorem cofaceSlots_edge (e : Edge) (c : RawCube) :
    cofaceSlots (.edge e :: c) = (cofaceSlots c).map (CoFaceSlot.prepend (.edge e)) := rfl

noncomputable def CoFaceSlot.labelTerm (t : CoFaceSlot) : RawChain :=
  ∑ e : Edge, (((-1 : ℤ)^degree t.pre) * vertexIncidence t.vertex e) • basis (t.expanded e)

@[simp] theorem coface_labelTerm_prepend_vertex (v : Vertex) (t : CoFaceSlot) :
    (t.prepend (.vertex v)).labelTerm = prepend (.vertex v) t.labelTerm := by
  simp [CoFaceSlot.labelTerm,CoFaceSlot.prepend,CoFaceSlot.expanded,map_sum,map_smul]

@[simp] theorem coface_labelTerm_prepend_edge (e : Edge) (t : CoFaceSlot) :
    (t.prepend (.edge e)).labelTerm = -prepend (.edge e) t.labelTerm := by
  simp [CoFaceSlot.labelTerm,CoFaceSlot.prepend,CoFaceSlot.expanded,map_sum,map_smul,
    pow_add,mul_smul,Finset.sum_neg_distrib]

@[simp] theorem coface_labelTerm_head (v : Vertex) (c : RawCube) :
    (CoFaceSlot.mk [] v c).labelTerm = vertexCofaces v c := by
  simp [CoFaceSlot.labelTerm,CoFaceSlot.expanded,vertexCofaces]

/-- Full endpoint coface expansion in the auxiliary label orientation. -/
theorem labelCoBoundaryBasis_eq_slots (c : RawCube) :
    labelCoBoundaryBasis c = ((cofaceSlots c).map CoFaceSlot.labelTerm).sum := by
  induction c with
  | nil => simp [labelCoBoundaryBasis,cofaceSlots]
  | cons a c ih =>
    cases a with
    | vertex v =>
      simp [labelCoBoundaryBasis,cofaceSlots_vertex,List.map_map,Function.comp_def,ih,map_list_sum]
    | edge e =>
      simp only [labelCoBoundaryBasis,cofaceSlots_edge,List.map_map,Function.comp_def,
        coface_labelTerm_prepend_edge,ih]
      simpa only [LinearMap.neg_apply,List.map_map,Function.comp_def] using
        (map_list_sum (-(prepend (.edge e))) ((cofaceSlots c).map CoFaceSlot.labelTerm))

theorem cofaceSlots_spec {c : RawCube} {t : CoFaceSlot} (ht : t ∈ cofaceSlots c) :
    t.cube = c := by
  induction c generalizing t with
  | nil => simp [cofaceSlots] at ht
  | cons a c ih =>
    cases a with
    | vertex v =>
      rcases List.mem_cons.mp ht with rfl | ht
      · rfl
      · obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
        simpa [CoFaceSlot.cube,CoFaceSlot.prepend] using congrArg (List.cons (.vertex v)) (ih hu)
    | edge e =>
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
      simpa [CoFaceSlot.cube,CoFaceSlot.prepend] using congrArg (List.cons (.edge e)) (ih hu)

/-- A sparse list sum may omit all edges where its summand is zero. -/
theorem sum_incident_of_zero (v : Vertex) (f : Edge → RawChain)
    (hzero : ∀ e, e ∉ incidentEdges v → f e = 0) :
    ((incidentEdges v).map f).sum = ∑ e : Edge, f e := by
  classical
  rw [list_map_sum_toFinset _ _ (incidentEdges_nodup v)]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro e he hn
  exact hzero e (by simpa using hn)

theorem vertexIncidence_zero_of_not_mem (v : Vertex) (e : Edge)
    (hn : e ∉ incidentEdges v) : vertexIncidence v e = 0 := by
  have hinc := mt (incidentEdges_membership v e).mpr hn
  have hs : (endpoints e).1 ≠ v := fun h => hinc (Or.inl h)
  have ht : (endpoints e).2 ≠ v := fun h => hinc (Or.inr h)
  simp [vertexIncidence,hs,ht]

/-- The exact paper orientation on each valid coface, after projection.
Invalid products contribute zero to the original configuration complex. -/
theorem projected_slot_edge (t : CoFaceSlot) (e : Edge) :
    restrictCubes 3 (reorient (orientation t.cube •
      (((-1 : ℤ)^degree t.pre) * vertexIncidence t.vertex e) • basis (t.expanded e))) =
    if IsCube (t.expanded e) ∧ degree (t.expanded e) = 3 then
      (vertexIncidence t.vertex e * movingSign e t.cube) • basis (t.expanded e) else 0 := by
  classical
  simp only [map_smul,reorient_basis,restrictCubes_basis,smul_smul]
  by_cases hv : IsCube (t.expanded e) ∧ degree (t.expanded e) = 3
  · simp only [if_pos hv]
    have hpre : GraphCell.edge e ∉ t.pre := edge_not_mem_prefix hv.1.2
    have hs := orientation_face_sign t.pre t.post e t.vertex hpre
    have he : (orientation t.cube *
        (((-1 : ℤ)^degree t.pre) * vertexIncidence t.vertex e)) * orientation (t.expanded e) =
        vertexIncidence t.vertex e * movingSign e t.cube := by
      calc
        _ = (orientation (t.expanded e) * orientation t.cube * (-1 : ℤ)^degree t.pre) *
            vertexIncidence t.vertex e := by ring
        _ = _ := by
          change (orientation (t.pre ++ .edge e :: t.post) *
            orientation (t.pre ++ .vertex t.vertex :: t.post) * (-1 : ℤ)^degree t.pre) * _ = _
          rw [hs]
          simp only [CoFaceSlot.cube,movingSign_append,movingSign_vertex]
          ring
    rw [he]
  · simp [hv]

/-- Computable original-coordinate cofaces of one stationary particle. -/
def codeSlot (t : CoFaceSlot) : List (ℕ × ℤ) :=
  (incidentEdges t.vertex).filterMap fun e =>
    if IsCube (t.expanded e) ∧ degree (t.expanded e) = 3 then
      some (encodeCube (t.expanded e), vertexIncidence t.vertex e * movingSign e t.cube)
    else none

/-- Numerical sparse cofaces denote the actual projected transpose. -/
theorem codeSlot_sound (t : CoFaceSlot) (hlen : t.cube.length = 4) :
    codeChain (codeSlot t) = restrictCubes 3 (reorient (orientation t.cube • t.labelTerm)) := by
  have hd : ∀ e, (t.expanded e).length = 4 := by
    intro e
    simpa [CoFaceSlot.cube,CoFaceSlot.expanded] using hlen
  have hlist : ∀ l : List Edge,
      codeChain (l.filterMap fun e =>
        if IsCube (t.expanded e) ∧ degree (t.expanded e) = 3 then
          some (encodeCube (t.expanded e), vertexIncidence t.vertex e * movingSign e t.cube)
        else none) =
      (l.map fun e => if IsCube (t.expanded e) ∧ degree (t.expanded e) = 3 then
        (vertexIncidence t.vertex e * movingSign e t.cube) • basis (t.expanded e) else 0).sum := by
    intro l
    induction l with
    | nil => rfl
    | cons e l ih =>
      by_cases hv : IsCube (t.expanded e) ∧ degree (t.expanded e) = 3
      · simp [hv,codeChain_cons,decodeCube_encodeCube _ (hd e),ih]
      · simp [hv,ih]
  rw [codeSlot,hlist]
  unfold CoFaceSlot.labelTerm
  rw [Finset.smul_sum,map_sum,map_sum]
  simp_rw [projected_slot_edge]
  apply sum_incident_of_zero
  intro e he
  simp [vertexIncidence_zero_of_not_mem t.vertex e he]

/-- Finite projected transpose expansion in the original four labelled coordinates. -/
def codeCofaces (c : RawCube) : List (ℕ × ℤ) :=
  (cofaceSlots c).flatMap codeSlot

theorem codeCofaces_sound (c : RawCube) (hlen : c.length = 4) :
    codeChain (codeCofaces c) = restrictCubes 3 (coBoundaryBasis c) := by
  rw [codeCofaces,codeChain_flatMap,coBoundaryBasis,labelCoBoundaryBasis_eq_slots]
  rw [← map_smul,List.smul_sum]
  simp only [map_list_sum,List.map_map,Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  have hs := cofaceSlots_spec ht
  rw [← hs]
  exact codeSlot_sound t (by rw [hs]; exact hlen)

end Paper23.CertificateChecks

