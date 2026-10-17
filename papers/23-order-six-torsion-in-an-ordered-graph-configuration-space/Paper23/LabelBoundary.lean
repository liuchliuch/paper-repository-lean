import Paper23.Labels
import Mathlib.Algebra.BigOperators.Fin

/-! Relabelling is a chain action with the increasing-moving-edge orientations. -/
namespace Paper23.Labels
open Cubical

noncomputable def tupleBoundaryTerm (f : Tuple) (i : Fin 4) : RawChain :=
  match f i with
  | .vertex _ => 0
  | .edge e => movingSign e (List.ofFn f) •
      (basis (List.ofFn (Function.update f i (.vertex (endpoints e).2))) -
       basis (List.ofFn (Function.update f i (.vertex (endpoints e).1))))

noncomputable def faceTermOn (c : RawCube) (t : FaceData) : RawChain :=
  movingSign t.edge c • (basis t.upper - basis t.lower)

theorem movingTerm_eq_on {c : RawCube} {t : FaceData} (ht : t ∈ faces c) :
    t.movingTerm = faceTermOn c t := by
  rw [← faces_spec ht]
  simp [FaceData.movingTerm, faceTermOn, FaceData.cube, movingSign_append]

theorem movingFaces_eq_tupleSum (f : Tuple) :
    ((faces (List.ofFn f)).map FaceData.movingTerm).sum =
      ∑ i : Fin 4, tupleBoundaryTerm f i := by
  have hh : ((faces (List.ofFn f)).map FaceData.movingTerm) =
      (faces (List.ofFn f)).map (faceTermOn (List.ofFn f)) := by
    apply List.map_congr_left
    intro t ht
    exact movingTerm_eq_on ht
  rw [hh]
  cases h0 : f 0 <;> cases h1 : f 1 <;> cases h2 : f 2 <;> cases h3 : f 3 <;>
    simp [faces, List.map_map, Function.comp_def, FaceData.prepend, faceTermOn,
      FaceData.upper, FaceData.lower, tupleBoundaryTerm, Fin.sum_univ_succ,
      h0, h1, h2, h3] <;> abel

theorem boundary_tuple (f : Tuple) (h : (List.ofFn f).Pairwise ClosureDisjoint) :
    boundary (basis (List.ofFn f)) = ∑ i : Fin 4, tupleBoundaryTerm f i := by
  rw [boundary_basis_eq_moving_faces _ h, movingFaces_eq_tupleSum]

/-- A total extension of the relabelling map; only valid cells matter in the
cubical chain subgroups. -/
noncomputable def rawRelabel (p : S4) (c : RawCube) : RawCube := by
  classical
  exact if h : IsCube c then (relabel p ⟨c,h⟩).val else c

noncomputable def chainRelabel (p : S4) : RawChain →ₗ[ℤ] RawChain :=
  Finsupp.lmapDomain ℤ ℤ (rawRelabel p)

@[simp] theorem chainRelabel_basis (p : S4) (c : RawCube) :
    chainRelabel p (basis c) = basis (rawRelabel p c) := by
  simp [chainRelabel, basis, Finsupp.lmapDomain_apply]

theorem rawRelabel_cube (p : S4) (c : Cube) : rawRelabel p c.val = (relabel p c).val := by
  classical
  simp [rawRelabel, c.property]

theorem rawRelabel_ofFn (p : S4) (f : Tuple)
    (h : (List.ofFn f).Pairwise ClosureDisjoint) :
    rawRelabel p (List.ofFn f) = List.ofFn (relabelTuple p f) := by
  have hc : IsCube (List.ofFn f) := ⟨by simp, h⟩
  rw [show List.ofFn f = (ofTuple f h).val from rfl, rawRelabel_cube]
  change List.ofFn (relabelTuple p (tuple (ofTuple f h))) = List.ofFn (relabelTuple p f)
  rw [tuple_ofTuple]

theorem movingSign_relabel (p : S4) (f : Tuple) (e : Edge) :
    movingSign e (List.ofFn (relabelTuple p f)) = movingSign e (List.ofFn f) := by
  have hp := Equiv.Perm.ofFn_comp_perm (p.symm : S4) f
  unfold movingSign smaller
  congr 1
  exact (hp.filter _).length_eq

theorem chainRelabel_tupleTerm (p : S4) (f : Tuple)
    (h : (List.ofFn f).Pairwise ClosureDisjoint) (i : Fin 4) :
    chainRelabel p (tupleBoundaryTerm f i) =
      tupleBoundaryTerm (relabelTuple p f) (p i) := by
  have hc : IsCube (List.ofFn f) := ⟨by simp, h⟩
  have hi : relabelTuple p f (p i) = f i := by
    change f (p.symm (p i)) = f i
    rw [p.symm_apply_apply]
  cases hfi : f i with
  | vertex v => simp [tupleBoundaryTerm, hi, hfi]
  | edge e =>
    have hp := (terminalFace_tuple f i e hfi).isCube hc
    have hm := (initialFace_tuple f i e hfi).isCube hc
    simp only [tupleBoundaryTerm, hi, hfi, map_smul, map_sub, chainRelabel_basis]
    rw [rawRelabel_ofFn p _ hp.2, rawRelabel_ofFn p _ hm.2]
    rw [relabelTuple_update, relabelTuple_update, movingSign_relabel]

/-- Relabelling commutes with the actual boundary. There is no extra
orientation sign, because all summands use graph-edge order. -/
theorem chainRelabel_boundary_basis (p : S4) (c : Cube) :
    chainRelabel p (boundary (basis c.val)) = boundary (chainRelabel p (basis c.val)) := by
  have h := c.property.2
  rw [← ofFn_tuple c] at h ⊢
  rw [boundary_tuple _ h, map_sum]
  simp_rw [chainRelabel_tupleTerm p _ h]
  rw [chainRelabel_basis, rawRelabel_ofFn p _ h]
  have hg : (List.ofFn (relabelTuple p (tuple c))).Pairwise ClosureDisjoint := by
    change (relabel p c).val.Pairwise ClosureDisjoint
    exact (relabel p c).property.2
  rw [boundary_tuple _ hg]
  exact Fintype.sum_equiv p _ _ (fun _ => rfl)

theorem chainRelabel_mem (p : S4) (q : ℕ) (x : RawChain) (hx : x ∈ Chains q) :
    chainRelabel p x ∈ Chains q := by
  apply map_mem_supported _ _ ?_ x hx
  intro c hc
  change IsCube c ∧ degree c = q at hc
  rw [chainRelabel_basis, rawRelabel_cube p ⟨c,hc.1⟩]
  apply Finsupp.single_mem_supported ℤ 1
  exact ⟨(relabel p ⟨c,hc.1⟩).property, (relabel_degree p ⟨c,hc.1⟩).trans hc.2⟩

theorem chainRelabel_boundary (p : S4) (q : ℕ) (x : RawChain) (hx : x ∈ Chains q) :
    chainRelabel p (boundary x) = boundary (chainRelabel p x) := by
  let L := (chainRelabel p).comp boundary - boundary.comp (chainRelabel p)
  have hker : x ∈ LinearMap.ker L := by
    apply map_mem_supported (LinearMap.ker L) LinearMap.id ?_ x hx
    intro c hc
    change IsCube c ∧ degree c = q at hc
    change L (basis c) = 0
    simp only [L, LinearMap.sub_apply, LinearMap.comp_apply, sub_eq_zero]
    exact chainRelabel_boundary_basis p ⟨c,hc.1⟩
  exact sub_eq_zero.mp (LinearMap.mem_ker.mp hker)

end Paper23.Labels
