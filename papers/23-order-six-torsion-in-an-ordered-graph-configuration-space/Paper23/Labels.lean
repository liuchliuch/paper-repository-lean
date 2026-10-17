import Paper23.Cubical
import Mathlib.Data.List.Sort
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Group.End
import Mathlib.Data.Fintype.Perm

/-!
The canonical-cell and particle-label encoding of §2, paragraph 4.
A permutation sends canonical coordinate i to particle p(i), exactly as in
`[p;c]` in the paper. No quotient by the particle permutation group is taken.
-/
namespace Paper23.Labels
open Cubical

abbrev S4 := Equiv.Perm (Fin 4)
abbrev Tuple := Fin 4 → GraphCell

/-- The paper's vertex and edge token order. -/
def token : GraphCell → ℕ
  | .vertex v => v.val
  | .edge e => 32 + e.val

theorem token_injective : Function.Injective token := by
  intro a b h
  cases a with
  | vertex v =>
    cases b with
    | vertex w => congr 1; exact Fin.ext h
    | edge e => simp only [token] at h; omega
  | edge e =>
    cases b with
    | vertex v => simp only [token] at h; omega
    | edge f => congr 1; apply Fin.ext; simpa [token] using h

instance : LinearOrder GraphCell := LinearOrder.lift' token token_injective

/-- Coordinates of a valid cube, indexed by its four particle labels. -/
def tuple (c : Cube) : Tuple := fun i => c.val.get (Fin.cast c.property.1.symm i)

@[simp] theorem ofFn_tuple (c : Cube) : List.ofFn (tuple c) = c.val := by
  rw [← List.ofFn_get c.val]
  exact (List.ofFn_congr c.property.1 c.val.get).symm

theorem closureDisjoint_ne {a b : GraphCell} (h : ClosureDisjoint a b) : a ≠ b := by
  intro hab
  subst b
  have hv : a.vertices.Nonempty := by cases a <;> simp [GraphCell.vertices]
  obtain ⟨v, hv⟩ := hv
  exact Finset.disjoint_left.mp h hv hv

theorem cube_nodup (c : Cube) : c.val.Nodup :=
  (c.property.2.imp fun h => closureDisjoint_ne h)

theorem tuple_injective (c : Cube) : Function.Injective (tuple c) := by
  intro i j h
  have hh := List.nodup_iff_injective_get.mp (cube_nodup c) h
  exact (finCongr c.property.1.symm).injective hh

theorem tuple_mem (c : Cube) (i : Fin 4) : tuple c i ∈ c.val := List.get_mem _ _

def ofTuple (f : Tuple) (h : (List.ofFn f).Pairwise ClosureDisjoint) : Cube :=
  ⟨List.ofFn f, by simp, h⟩

@[simp] theorem tuple_ofTuple (f : Tuple) (h : (List.ofFn f).Pairwise ClosureDisjoint) :
    tuple (ofTuple f h) = f := by
  funext i
  fin_cases i <;> simp [tuple, ofTuple]

theorem tuple_ext {c d : Cube} (h : tuple c = tuple d) : c = d := by
  apply Subtype.ext
  rw [← ofFn_tuple c, ← ofFn_tuple d, h]

/-- Relabelling sends the cell formerly at label i to label p(i). -/
def relabelTuple (p : S4) (f : Tuple) : Tuple := f ∘ p.symm

/-- A permutation reorders particle coordinates and preserves disjoint closures. -/
def relabel (p : S4) (c : Cube) : Cube :=
  ofTuple (relabelTuple p (tuple c)) <| by
    have hp := Equiv.Perm.ofFn_comp_perm (p.symm : S4) (tuple c)
    rw [ofFn_tuple] at hp
    exact hp.symm.pairwise c.property.2 (fun h => Disjoint.symm h)

@[simp] theorem tuple_relabel (p : S4) (c : Cube) :
    tuple (relabel p c) = relabelTuple p (tuple c) := tuple_ofTuple _ _

theorem relabel_perm (p : S4) (c : Cube) : (relabel p c).val.Perm c.val := by
  change (List.ofFn (tuple c ∘ p.symm)).Perm c.val
  have hp := Equiv.Perm.ofFn_comp_perm (p.symm : S4) (tuple c)
  rw [ofFn_tuple] at hp
  exact hp

@[simp] theorem relabel_one (c : Cube) : relabel 1 c = c := by
  apply tuple_ext
  simp [relabelTuple]

@[simp] theorem relabel_mul (p q : S4) (c : Cube) :
    relabel (p*q) c = relabel p (relabel q c) := by
  apply tuple_ext
  funext i
  simp only [tuple_relabel, relabelTuple, Function.comp_apply]
  change tuple c ((p*q)⁻¹ i) = tuple c (q⁻¹ (p⁻¹ i))
  simp only [mul_inv_rev, Equiv.Perm.mul_apply]

theorem relabel_degree (p : S4) (c : Cube) : degree (relabel p c).val = degree c.val :=
  ((relabel_perm p c).map GraphCell.dimension).sum_eq

theorem relabel_free {p q : S4} {c : Cube} (h : relabel p c = relabel q c) : p = q := by
  have ht := congrArg tuple h
  have hi : p.symm = q.symm := by
    apply Equiv.ext
    intro i
    apply tuple_injective c
    simpa only [tuple_relabel, relabelTuple, Function.comp_apply] using congrFun ht i
  exact inv_injective hi

/-- A canonical cube has increasing graph tokens; its cells remain distinct
because their closures are disjoint. -/
abbrev Canonical := {c : Cube // c.val.Sorted (· ≤ ·)}

def canonical (c : Cube) : Canonical :=
  ⟨⟨c.val.mergeSort (· ≤ ·), by
      constructor
      · rw [(List.mergeSort_perm c.val (· ≤ ·)).length_eq]; exact c.property.1
      · exact (List.mergeSort_perm c.val (· ≤ ·)).symm.pairwise c.property.2
          (fun h => Disjoint.symm h)⟩,
    List.sorted_mergeSort' (· ≤ ·) c.val⟩

theorem canonical_perm (c : Cube) : (canonical c).val.val.Perm c.val :=
  List.mergeSort_perm c.val (· ≤ ·)

theorem canonical_unique {c d : Canonical} (h : c.val.val.Perm d.val.val) : c = d := by
  apply Subtype.ext
  apply Subtype.ext
  exact List.eq_of_perm_of_sorted h c.property d.property

theorem canonical_strict (c : Canonical) : c.val.val.Pairwise (fun a b => token a < token b) := by
  have h := c.property.and c.val.property.2
  apply h.imp
  intro a b hab
  have hle : token a ≤ token b := hab.1
  have hne : token a ≠ token b := fun h => closureDisjoint_ne hab.2 (token_injective h)
  omega

/-- The bijection from coordinate indices to the four distinct graph cells. -/
def coordinates (c : Cube) : Fin 4 ≃ {a // a ∈ c.val} :=
  (finCongr c.property.1.symm).trans (List.Nodup.getEquiv c.val (cube_nodup c))

@[simp] theorem coordinates_val (c : Cube) (i : Fin 4) : (coordinates c i).val = tuple c i := rfl

def permMembers {c d : Cube} (h : c.val.Perm d.val) :
    {a // a ∈ c.val} ≃ {a // a ∈ d.val} where
  toFun a := ⟨a.val, h.mem_iff.mp a.property⟩
  invFun a := ⟨a.val, h.mem_iff.mpr a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The label assignment p(i) attached to the i-th canonical token. -/
def assignment (c : Cube) : S4 :=
  (coordinates (canonical c).val).trans
    ((permMembers (canonical_perm c)).trans (coordinates c).symm)

theorem assignment_spec (c : Cube) (i : Fin 4) :
    tuple c (assignment c i) = tuple (canonical c).val i := by
  change ((coordinates c) ((coordinates c).symm _)).val = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- Canonical coordinates with their assigned particle labels decode to the
original ordered cube. -/
theorem reconstruct (c : Cube) : relabel (assignment c) (canonical c).val = c := by
  apply tuple_ext
  funext i
  simp only [tuple_relabel, relabelTuple, Function.comp_apply]
  exact (assignment_spec c ((assignment c).symm i)).symm.trans (by simp)

theorem canonical_relabel (p : S4) (c : Cube) : canonical (relabel p c) = canonical c := by
  apply canonical_unique
  exact (canonical_perm (relabel p c)).trans ((relabel_perm p c).trans (canonical_perm c).symm)

/-- Existence and uniqueness of the [p;c] representation in §2. -/
theorem canonical_encoding_unique (c : Cube) :
    ∃! x : Canonical × S4, relabel x.2 x.1.val = c := by
  refine ⟨⟨canonical c, assignment c⟩, reconstruct c, ?_⟩
  intro x hx
  have hc : x.1 = canonical c := by
    apply canonical_unique
    have hp0 := (relabel_perm x.2 x.1.val).symm
    rw [hx] at hp0
    exact hp0.trans (canonical_perm c).symm
  have hp : x.2 = assignment c := by
    apply relabel_free (c := (canonical c).val)
    calc
      relabel x.2 (canonical c).val = relabel x.2 x.1.val := by rw [hc]
      _ = c := hx
      _ = relabel (assignment c) (canonical c).val := (reconstruct c).symm

  exact Prod.ext hc hp

/-- The labels and the canonical cells form a genuine product basis. -/
noncomputable def canonicalEquiv : Cube ≃ Canonical × S4 where
  toFun c := ⟨canonical c, assignment c⟩
  invFun x := relabel x.2 x.1.val
  left_inv c := reconstruct c
  right_inv x := (canonical_encoding_unique (relabel x.2 x.1.val)).unique (reconstruct _) rfl

@[simp] theorem card_S4 : Fintype.card S4 = 24 := by
  rw [Fintype.card_perm]
  rfl

/-- Relabelling a coordinate replacement replaces the correspondingly relabelled
particle. This is the `p ∘ q` update rule of §2, paragraph 4. -/
theorem relabelTuple_update (p : S4) (f : Tuple) (i : Fin 4) (a : GraphCell) :
    relabelTuple p (Function.update f i a) =
      Function.update (relabelTuple p f) (p i) a := by
  funext j
  by_cases h : j = p i
  · subst j
    simp only [relabelTuple, Function.comp_apply, Function.update_self]
    rw [p.symm_apply_apply, Function.update_self]
  · have hi : p.symm j ≠ i := by
      intro hh
      apply h
      calc
        j = p (p.symm j) := (p.apply_symm_apply j).symm
        _ = p i := congrArg p hh
    simp [relabelTuple, Function.comp_def, h, hi]

@[simp] theorem ofFn_four (f : Tuple) : List.ofFn f = [f 0, f 1, f 2, f 3] := rfl

/-- Coordinate replacement is an actual endpoint face in the list-based
cubical complex, with the label position unchanged. -/
theorem initialFace_tuple (f : Tuple) (i : Fin 4) (e : Edge) (h : f i = .edge e) :
    Face (List.ofFn (Function.update f i (.vertex (endpoints e).1))) (List.ofFn f) := by
  fin_cases i
  · change f 0 = .edge e at h
    simpa [h] using Face.initial e [f 1, f 2, f 3]
  · change f 1 = .edge e at h
    simpa [h] using Face.cons (f 0) (Face.initial e [f 2, f 3])
  · change f 2 = .edge e at h
    simpa [h] using Face.cons (f 0) (Face.cons (f 1) (Face.initial e [f 3]))
  · change f 3 = .edge e at h
    simpa [h] using Face.cons (f 0) (Face.cons (f 1) (Face.cons (f 2) (Face.initial e [])))

theorem terminalFace_tuple (f : Tuple) (i : Fin 4) (e : Edge) (h : f i = .edge e) :
    Face (List.ofFn (Function.update f i (.vertex (endpoints e).2))) (List.ofFn f) := by
  fin_cases i
  · change f 0 = .edge e at h
    simpa [h] using Face.terminal e [f 1, f 2, f 3]
  · change f 1 = .edge e at h
    simpa [h] using Face.cons (f 0) (Face.terminal e [f 2, f 3])
  · change f 2 = .edge e at h
    simpa [h] using Face.cons (f 0) (Face.cons (f 1) (Face.terminal e [f 3]))
  · change f 3 = .edge e at h
    simpa [h] using Face.cons (f 0) (Face.cons (f 1) (Face.cons (f 2) (Face.terminal e [])))

theorem relabel_initialFace (p : S4) (f : Tuple) (i : Fin 4) (e : Edge)
    (h : f i = .edge e) :
    Face (List.ofFn (relabelTuple p (Function.update f i (.vertex (endpoints e).1))))
      (List.ofFn (relabelTuple p f)) := by
  rw [relabelTuple_update]
  apply initialFace_tuple _ (p i) e
  simpa [relabelTuple, Function.comp_def] using h

theorem relabel_terminalFace (p : S4) (f : Tuple) (i : Fin 4) (e : Edge)
    (h : f i = .edge e) :
    Face (List.ofFn (relabelTuple p (Function.update f i (.vertex (endpoints e).2))))
      (List.ofFn (relabelTuple p f)) := by
  rw [relabelTuple_update]
  apply terminalFace_tuple _ (p i) e
  simpa [relabelTuple, Function.comp_def] using h

/-- Sorting only changes canonical positions. The particle assignment after
reordering positions by q is exactly p composed with q, without a label sign. -/
theorem assignment_comp (p q : S4) (i : Fin 4) : (p*q) i = p (q i) := rfl

end Paper23.Labels

