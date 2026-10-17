import K44K35Free.Geometry
import Mathlib.Data.Fintype.Option
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Explicit normalized equations for the exceptional fiber planes. -/
namespace K44K35Free.Geometry.Fiber

open Polynomial Finset
open scoped BigOperators

/-- A nonconstant affine form, normalized at its first nonzero coefficient
in the order `(v,y,z)`. -/
abbrev Normal (F : Type*) := (F × F) ⊕ (F ⊕ Unit)

/-- The one plane at infinity is shared by all fibers. -/
abbrev Index (F : Type*) := Option (F × Normal F × F)

variable {F : Type*} [Field F]

def eval (n : Normal F) (y z v : F) : F :=
  match n with
  | .inl (g,d) => v + g*y + d*z
  | .inr (.inl d) => y + d*z
  | .inr (.inr _) => z

def onPoint (α : F) (f : F → F) (i : Index F) (p : Param F) : Prop :=
  match i with
  | none => False
  | some (c,n,e) => p 0 = c ∧ eval n (p 1) (p 2) ((p 1)^2-α*(p 2)^2+f (p 0)) = e

noncomputable def fiberSection (α : F) (f : F → F) [Fintype F]
    (i : Index F) : Finset (Param F) := by
  classical
  exact univ.filter (onPoint α f i)

@[simp] theorem mem_section (α : F) (f : F → F) [Fintype F]
    (i : Index F) (p : Param F) :
    p ∈ fiberSection α f i ↔ onPoint α f i p := by
  classical
  simp [fiberSection]

omit [Field F] in
@[simp] theorem card_normal [Fintype F] :
    Fintype.card (Normal F) = Fintype.card F ^ 2 + Fintype.card F + 1 := by
  simp [Normal, pow_two, Nat.add_assoc]

omit [Field F] in
@[simp] theorem card_index [Fintype F] :
    Fintype.card (Index F) =
      Fintype.card F ^ 4 + Fintype.card F ^ 3 + Fintype.card F ^ 2 + 1 := by
  simp only [Index, Fintype.card_option, Fintype.card_prod, card_normal]
  ring

/-- For each normalized direction, exactly one intercept produces a plane
through the given affine point. The fiber itself is forced by `x`. -/
noncomputable def incidenceEquiv (α : F) (f : F → F) (p : Param F) :
    { i : Index F // onPoint α f i p } ≃ Normal F where
  toFun i := match i with
    | ⟨none, h⟩ => False.elim h
    | ⟨some (_, n, _), _⟩ => n
  invFun n := ⟨some (p 0,n,eval n (p 1) (p 2) ((p 1)^2-α*(p 2)^2+f (p 0))),
    ⟨rfl,rfl⟩⟩
  left_inv := by
    rintro ⟨i, hi⟩
    cases i with
    | none => exact False.elim hi
    | some i =>
      rcases i with ⟨c,n,e⟩
      apply Subtype.ext
      simp only [onPoint] at hi
      rcases hi with ⟨rfl,rfl⟩
      rfl
  right_inv n := rfl

 theorem point_incidence_count (α : F) (f : F → F) [Fintype F] (p : Param F) :
    Nat.card { i : Index F // onPoint α f i p } =
      Fintype.card F ^ 2 + Fintype.card F + 1 := by
  rw [Nat.card_congr (incidenceEquiv α f p), Nat.card_eq_fintype_card, card_normal]

/-- Double counting actual solutions of the normalized fiber-plane equations. -/
theorem total_incidence_count (α : F) (f : F → F) [Fintype F] :
    ∑ i : Index F, (fiberSection α f i).card =
      Fintype.card F ^ 3 * (Fintype.card F ^ 2 + Fintype.card F + 1) := by
  classical
  simp only [fiberSection, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  have hp (p : Param F) :
      ∑ i : Index F, (if onPoint α f i p then (1 : ℕ) else 0) =
        Fintype.card F ^ 2 + Fintype.card F + 1 := by
    rw [← card_filter]
    rw [← Fintype.card_subtype]
    simpa [Nat.card_eq_fintype_card] using point_incidence_count α f p
  simp_rw [hp]
  simp [Param]

private theorem quadratic_card_le_two [Fintype F] [DecidableEq F] (a b : F) :
    (univ.filter (fun y : F => y^2+a*y+b=0)).card ≤ 2 := by
  classical
  let P : F[X] := X^2 + C a * X + C b
  have hP : P ≠ 0 := by
    intro h
    have hcoeff := congrArg (fun Q : F[X] => Q.coeff 2) h
    simp [P] at hcoeff
  have hdeg : P.natDegree ≤ 2 := by
    dsimp [P]
    compute_degree
  exact (card_le_degree_of_subset_roots (p := P) (by
    intro y hy
    rw [mem_roots hP]
    simpa [P] using (mem_filter.mp hy).2)).trans hdeg

/-- All sections in a fiber plane have at most twice the field order. -/
theorem section_card_le (α : F) (f : F → F) [Fintype F] (i : Index F) :
    (fiberSection α f i).card ≤ 2 * Fintype.card F := by
  classical
  cases i with
  | none =>
    have hz : fiberSection α f none = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact (mem_section α f none p).mp hp
    rw [hz]
    simp
  | some i =>
    rcases i with ⟨c,n,e⟩
    cases n with
    | inl gd =>
      rcases gd with ⟨g,d⟩
      let S := fiberSection α f (some (c,Sum.inl (g,d),e))
      have hbound (z : F) : (S.filter (fun p => p 2 = z)).card ≤ 2 := by
        let T := univ.filter (fun y : F =>
          y^2+g*y+(-α*z^2+f c+d*z-e)=0)
        have hi : Set.InjOn (fun p : Param F => p 1) (↑(S.filter (fun p => p 2 = z)) : Set (Param F)) := by
          intro p hp q hq hpq
          have hp' := (mem_section α f _ p).mp (mem_filter.mp hp).1
          have hq' := (mem_section α f _ q).mp (mem_filter.mp hq).1
          funext k
          fin_cases k
          · exact hp'.1.trans hq'.1.symm
          · exact hpq
          · exact (mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm
        calc
          (S.filter (fun p => p 2 = z)).card ≤ T.card := by
            apply card_le_card_of_injOn (fun p : Param F => p 1)
            · intro p hp
              have hp' := (mem_section α f _ p).mp (mem_filter.mp hp).1
              have hpz := (mem_filter.mp hp).2
              simp only [onPoint, eval] at hp'
              change p 1 ∈ T
              simp only [T, mem_filter, mem_univ, true_and]
              rw [← hp'.1, ← hpz]
              linear_combination hp'.2
            · exact hi
          _ ≤ 2 := quadratic_card_le_two _ _
      calc
        S.card = ∑ z : F, (S.filter (fun p => p 2 = z)).card :=
          card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)
        _ ≤ ∑ _z : F, 2 := sum_le_sum (fun z _ => hbound z)
        _ = 2 * Fintype.card F := by simp [Nat.mul_comm]
    | inr n =>
      cases n with
      | inl d =>
        have hi : Set.InjOn (fun p : Param F => p 2)
            (↑(fiberSection α f (some (c,Sum.inr (Sum.inl d),e))) : Set (Param F)) := by
          intro p hp q hq hpq
          have hp' := (mem_section α f _ p).mp hp
          have hq' := (mem_section α f _ q).mp hq
          simp only [onPoint,eval] at hp' hq'
          funext k
          fin_cases k
          · exact hp'.1.trans hq'.1.symm
          · change p 1 = q 1
            change p 2 = q 2 at hpq
            linear_combination hp'.2-hq'.2-d*hpq
          · exact hpq
        have hcard : (fiberSection α f (some (c,Sum.inr (Sum.inl d),e))).card ≤ Fintype.card F := by
          simpa using card_le_card_of_injOn (s := fiberSection α f (some (c,Sum.inr (Sum.inl d),e)))
            (t := univ) (fun p : Param F => p 2) (fun _ _ => mem_univ _) hi
        omega
      | inr u =>
        have hi : Set.InjOn (fun p : Param F => p 1)
            (↑(fiberSection α f (some (c,Sum.inr (Sum.inr u),e))) : Set (Param F)) := by
          intro p hp q hq hpq
          have hp' := (mem_section α f _ p).mp hp
          have hq' := (mem_section α f _ q).mp hq
          simp only [onPoint,eval] at hp' hq'
          funext k
          fin_cases k
          · exact hp'.1.trans hq'.1.symm
          · exact hpq
          · exact hp'.2.trans hq'.2.symm
        have hcard : (fiberSection α f (some (c,Sum.inr (Sum.inr u),e))).card ≤ Fintype.card F := by
          simpa using card_le_card_of_injOn (s := fiberSection α f (some (c,Sum.inr (Sum.inr u),e)))
            (t := univ) (fun p : Param F => p 1) (fun _ _ => mem_univ _) hi
        omega

/-- A homogeneous parametrization of each normalized plane. -/
def planeMapFun (i : Index F) (t : Fin 3 → F) : V F :=
  match i with
  | none => ![0,0,t 0,t 1,0,t 2]
  | some (c, .inl (g,d), e) =>
      ![t 0,c*t 0,t 1,t 2,c^2*t 0,e*t 0-g*t 1-d*t 2]
  | some (c, .inr (.inl d), e) =>
      ![t 0,c*t 0,e*t 0-d*t 1,t 1,c^2*t 0,t 2]
  | some (c, .inr (.inr _), e) =>
      ![t 0,c*t 0,t 1,e*t 0,c^2*t 0,t 2]

def planeMap (i : Index F) : (Fin 3 → F) →ₗ[F] V F where
  toFun := planeMapFun i
  map_add' s t := by
    cases i with
    | none => ext k; fin_cases k <;> simp [planeMapFun]
    | some i =>
      rcases i with ⟨c,n,e⟩
      rcases n with ⟨g,d⟩ | (d | u) <;>
        ext k <;> fin_cases k <;> simp [planeMapFun] <;> ring
  map_smul' a t := by
    cases i with
    | none => ext k; fin_cases k <;> simp [planeMapFun]
    | some i =>
      rcases i with ⟨c,n,e⟩
      rcases n with ⟨g,d⟩ | (d | u) <;>
        ext k <;> fin_cases k <;> simp [planeMapFun] <;> ring

@[simp] theorem planeMap_apply (i : Index F) (t : Fin 3 → F) :
    planeMap i t = planeMapFun i t := rfl

 theorem planeMap_injective (i : Index F) : Function.Injective (planeMap i) := by
  intro s t h
  cases i with
  | none =>
    funext k
    fin_cases k
    · exact congrFun h 2
    · exact congrFun h 3
    · exact congrFun h 5
  | some i =>
    rcases i with ⟨c,n,e⟩
    rcases n with ⟨g,d⟩ | (d | u)
    · funext k
      fin_cases k
      · exact congrFun h 0
      · exact congrFun h 2
      · exact congrFun h 3
    · funext k
      fin_cases k
      · exact congrFun h 0
      · exact congrFun h 3
      · exact congrFun h 5
    · funext k
      fin_cases k
      · exact congrFun h 0
      · exact congrFun h 2
      · exact congrFun h 5

/-- The normalized equations define actual three-dimensional homogeneous subspaces. -/
noncomputable def plane (i : Index F) : Plane F :=
  ⟨LinearMap.range (planeMap i), by
    simpa using LinearMap.finrank_range_of_inj (planeMap_injective i)⟩

def equation (i : Index F) (v : V F) : Prop :=
  match i with
  | none => v 0 = 0 ∧ v 1 = 0 ∧ v 4 = 0
  | some (c,n,e) =>
      v 1 = c*v 0 ∧ v 4 = c^2*v 0 ∧ eval n (v 2) (v 3) (v 5) = e*v 0

@[simp] theorem mem_plane_iff (i : Index F) (v : V F) :
    v ∈ (plane i).val ↔ equation i v := by
  change (∃ t, planeMap i t = v) ↔ _
  cases i with
  | none =>
    constructor
    · rintro ⟨t,rfl⟩
      simp [planeMapFun,equation]
    · rintro ⟨hw,hx,hu⟩
      refine ⟨![v 2,v 3,v 5], ?_⟩
      ext k
      fin_cases k <;> simp [planeMapFun,hw,hx,hu]
  | some i =>
    rcases i with ⟨c,n,e⟩
    rcases n with ⟨g,d⟩ | (d | u)
    · constructor
      · rintro ⟨t,rfl⟩
        simp [planeMapFun,equation,eval]
        ring
      · rintro ⟨hx,hu,hv⟩
        refine ⟨![v 0,v 2,v 3], ?_⟩
        simp only [eval] at hv
        ext k
        fin_cases k <;> simp [planeMapFun,hx,hu]
        linear_combination -hv
    · constructor
      · rintro ⟨t,rfl⟩
        simp [planeMapFun,equation,eval]
      · rintro ⟨hx,hu,hy⟩
        refine ⟨![v 0,v 3,v 5], ?_⟩
        simp only [eval] at hy
        ext k
        fin_cases k <;> simp [planeMapFun,hx,hu]
        linear_combination -hy
    · constructor
      · rintro ⟨t,rfl⟩
        simp [planeMapFun,equation,eval]
      · rintro ⟨hx,hu,hz⟩
        refine ⟨![v 0,v 2,v 5], ?_⟩
        simp only [eval] at hz
        ext k
        fin_cases k <;> simp [planeMapFun,hx,hu,hz]

 theorem plane_is_fiber (i : Index F) : FiberExceptional (plane i) := by
  cases i with
  | none =>
    refine ⟨0, ?_⟩
    intro v hv
    have hv' := (mem_plane_iff none v).mp hv
    exact ⟨by simp [hv'.1,hv'.2.1], by simp [hv'.1,hv'.2.2]⟩
  | some i =>
    rcases i with ⟨c,n,e⟩
    refine ⟨c, ?_⟩
    intro v hv
    have hv' := (mem_plane_iff (some (c,n,e)) v).mp hv
    exact ⟨hv'.1,hv'.2.1⟩

@[simp] theorem point_mem_plane (α : F) (c : Quartic F) (i : Index F) (p : Param F) :
    point α c p ∈ (plane i).val ↔ onPoint α (quarticPolynomial c).eval i p := by
  rw [mem_plane_iff]
  cases i with
  | none => simp [equation,point,onPoint]
  | some i =>
    rcases i with ⟨d,n,e⟩
    simp [equation,point,onPoint]
    exact fun h _ => h ▸ rfl

 theorem section_eq_planeSection (α : F) (c : Quartic F) [Fintype F] (i : Index F) :
    fiberSection α (quarticPolynomial c).eval i = planeSection α c (plane i) := by
  classical
  ext p
  rw [mem_section, Geometry.mem_section, point_mem_plane]

private theorem plane_test {i j : Index F} (h : plane i = plane j) (t : Fin 3 → F) :
    equation j (planeMap i t) := by
  apply (mem_plane_iff j _).mp
  rw [← h]
  exact ⟨t,rfl⟩

 theorem plane_injective : Function.Injective (plane (F := F)) := by
  intro i j h
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some j =>
      rcases j with ⟨c,n,e⟩
      have ht := plane_test h.symm ![1,0,0]
      rcases n with ⟨g,d⟩ | (d | u) <;>
        simp [equation,planeMapFun] at ht
  | some i =>
    rcases i with ⟨c,n,e⟩
    cases j with
    | none =>
      have ht := plane_test h ![1,0,0]
      rcases n with ⟨g,d⟩ | (d | u) <;>
        simp [equation,planeMapFun] at ht
    | some j =>
      rcases j with ⟨c',n',e'⟩
      have h0 := plane_test h ![1,0,0]
      have h1 := plane_test h ![0,1,0]
      have h2 := plane_test h ![0,0,1]
      rcases n with ⟨g,d⟩ | (d | u) <;>
        rcases n' with ⟨g',d'⟩ | (d' | u') <;>
        simp [equation,planeMapFun,eval] at h0 h1 h2 ⊢
      all_goals rcases h0 with ⟨rfl,_,he⟩
      all_goals simp_all
      all_goals first
        | exact ⟨by linear_combination -h1, by linear_combination -h2⟩
        | linear_combination -h1

/-- Coordinates `(w,y,z,v)` identify the solid `F_c` with a four-dimensional space. -/
def solidMap (c : F) : (Fin 4 → F) →ₗ[F] V F where
  toFun t := ![t 0,c*t 0,t 1,t 2,c^2*t 0,t 3]
  map_add' s t := by ext k; fin_cases k <;> simp [mul_add]
  map_smul' a t := by ext k; fin_cases k <;> simp <;> ring

 theorem solidMap_injective (c : F) : Function.Injective (solidMap c) := by
  intro s t h
  funext k
  fin_cases k
  · exact congrFun h 0
  · exact congrFun h 2
  · exact congrFun h 3
  · exact congrFun h 5

@[simp] theorem solidMap_apply (c : F) (t : Fin 4 → F) :
    solidMap c t = ![t 0,c*t 0,t 1,t 2,c^2*t 0,t 3] := rfl

 theorem reconstruct_solid {c : F} {v : V F} (hv : v ∈ fiberSubspace c) :
    solidMap c ![v 0,v 2,v 3,v 5] = v := by
  ext k
  fin_cases k <;> simp [hv.1,hv.2]

private theorem dual_coordinates (φ : (Fin 4 → F) →ₗ[F] F) (t : Fin 4 → F) :
    φ t = t 0 * φ ![1,0,0,0] + t 1 * φ ![0,1,0,0] +
      t 2 * φ ![0,0,1,0] + t 3 * φ ![0,0,0,1] := by
  have ht : t = t 0 • ![1,0,0,0] + t 1 • ![0,1,0,0] +
      t 2 • ![0,0,1,0] + t 3 • ![0,0,0,1] := by
    ext k
    fin_cases k <;> simp
  conv_lhs => rw [ht]
  rw [map_add,map_add,map_add,map_smul,map_smul,map_smul,map_smul]
  rfl

/-- Every plane in a fiber solid has exactly one of the normalized equations. -/
theorem exists_index_of_fiber (E : Plane F) (hE : FiberExceptional E) :
    ∃ i : Index F, plane i = E := by
  classical
  obtain ⟨c,hc⟩ := hE
  let W : Submodule F (Fin 4 → F) := E.val.comap (solidMap c)
  have hW : W < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro htop
    have hrange : LinearMap.range (solidMap c) ≤ E.val := by
      rintro v ⟨t,rfl⟩
      have ht : t ∈ W := by rw [htop]; trivial
      exact ht
    have hdim := Submodule.finrank_mono hrange
    have hdim4 : Module.finrank F (LinearMap.range (solidMap c)) = 4 := by
      simpa using LinearMap.finrank_range_of_inj (solidMap_injective c)
    rw [hdim4,E.property] at hdim
    omega
  obtain ⟨φ,hφ,hWφ⟩ := W.exists_dual_map_eq_bot_of_lt_top hW inferInstance
  have hvanish (v : V F) (hv : v ∈ E.val) : φ ![v 0,v 2,v 3,v 5] = 0 := by
    have ht : ![v 0,v 2,v 3,v 5] ∈ W := by
      change solidMap c ![v 0,v 2,v 3,v 5] ∈ E.val
      rw [reconstruct_solid (hc hv)]
      exact hv
    have hm : φ ![v 0,v 2,v 3,v 5] ∈ W.map φ := ⟨_,ht,rfl⟩
    rwa [hWφ,Submodule.mem_bot] at hm
  let a := φ ![1,0,0,0]
  let g := φ ![0,1,0,0]
  let d := φ ![0,0,1,0]
  let b := φ ![0,0,0,1]
  have hlinear (v : V F) (hv : v ∈ E.val) :
      v 0*a+v 2*g+v 3*d+v 5*b=0 := by
    have hh := hvanish v hv
    rw [dual_coordinates] at hh
    exact hh
  have hEq (i : Index F) (hi : E.val ≤ (plane i).val) : plane i = E := by
    apply Subtype.ext
    exact (Submodule.eq_of_le_of_finrank_eq hi (by rw [E.property,(plane i).property])).symm
  by_cases hb : b ≠ 0
  · refine ⟨some (c,Sum.inl (g/b,d/b),-a/b),hEq _ ?_⟩
    intro v hv
    rw [mem_plane_iff]
    refine ⟨(hc hv).1,(hc hv).2,?_⟩
    simp only [eval]
    apply (mul_right_cancel₀ hb)
    field_simp
    linear_combination hlinear v hv
  · have hb0 : b = 0 := not_ne_iff.mp hb
    by_cases hg : g ≠ 0
    · refine ⟨some (c,Sum.inr (Sum.inl (d/g)),-a/g),hEq _ ?_⟩
      intro v hv
      rw [mem_plane_iff]
      refine ⟨(hc hv).1,(hc hv).2,?_⟩
      simp only [eval]
      apply (mul_right_cancel₀ hg)
      field_simp
      have hh := hlinear v hv
      rw [hb0] at hh
      linear_combination hh
    · have hg0 : g = 0 := not_ne_iff.mp hg
      by_cases hd : d ≠ 0
      · refine ⟨some (c,Sum.inr (Sum.inr ()),-a/d),hEq _ ?_⟩
        intro v hv
        rw [mem_plane_iff]
        refine ⟨(hc hv).1,(hc hv).2,?_⟩
        simp only [eval]
        apply (mul_right_cancel₀ hd)
        field_simp
        have hh := hlinear v hv
        rw [hb0,hg0] at hh
        linear_combination hh
      · have hd0 : d = 0 := not_ne_iff.mp hd
        have ha : a ≠ 0 := by
          intro ha0
          apply hφ
          apply LinearMap.ext
          intro t
          change φ t = 0
          rw [dual_coordinates]
          change t 0*a+t 1*g+t 2*d+t 3*b=0
          simp [ha0,hg0,hd0,hb0]
        refine ⟨none,hEq _ ?_⟩
        intro v hv
        have hw : v 0 = 0 := by
          have hh := hlinear v hv
          simp only [hb0,hg0,hd0,mul_zero,add_zero] at hh
          exact (mul_eq_zero.mp hh).resolve_right ha
        rw [mem_plane_iff]
        exact ⟨hw,by rw [(hc hv).1,hw,mul_zero],by rw [(hc hv).2,hw,mul_zero]⟩

/-- The normalized indices enumerate precisely the geometric fiber family. -/
noncomputable def fiberEquiv : Index F ≃ {E : Plane F // FiberExceptional E} :=
  Equiv.ofBijective (fun i => ⟨plane i,plane_is_fiber i⟩) ⟨
    fun i j h => plane_injective (congrArg Subtype.val h), by
      rintro ⟨E,hE⟩
      obtain ⟨i,hi⟩ := exists_index_of_fiber E hE
      exact ⟨i,Subtype.ext hi⟩⟩

/-- Proposition 4, equation (7), for the actual family of homogeneous planes. -/
theorem fiber_family_card [Fintype F] :
    Nat.card {E : Plane F // FiberExceptional E} =
      Fintype.card F ^ 4 + Fintype.card F ^ 3 + Fintype.card F ^ 2 + 1 := by
  rw [← Nat.card_congr fiberEquiv,Nat.card_eq_fintype_card,card_index]

noncomputable def fiberPlanes [Fintype F] : Finset (Plane F) := by
  classical
  exact univ.image plane

@[simp] theorem mem_fiberPlanes [Fintype F] (E : Plane F) :
    E ∈ fiberPlanes ↔ FiberExceptional E := by
  classical
  simp only [fiberPlanes,mem_image,mem_univ,true_and]
  constructor
  · rintro ⟨i,rfl⟩
    exact plane_is_fiber i
  · exact exists_index_of_fiber E

theorem fiberPlanes_card [Fintype F] :
    (fiberPlanes (F := F)).card =
      Fintype.card F ^ 4 + Fintype.card F ^ 3 + Fintype.card F ^ 2 + 1 := by
  classical
  rw [fiberPlanes,card_image_of_injective _ plane_injective,card_univ,card_index]

/-- The fiber contribution to Proposition 4, equation (8). -/
theorem fiber_total_incidence (α : F) (c : Quartic F) [Fintype F] :
    ∑ E ∈ fiberPlanes, (planeSection α c E).card =
      Fintype.card F ^ 3 * (Fintype.card F ^ 2 + Fintype.card F + 1) := by
  classical
  rw [fiberPlanes,sum_image (fun i _ j _ hij => plane_injective hij)]
  simp_rw [← section_eq_planeSection]
  exact total_incidence_count α (quarticPolynomial c).eval

/-- The fiber contribution to Proposition 4, equation (9). -/
theorem fiber_section_bound (α : F) (c : Quartic F) [Fintype F]
    (E : Plane F) (hE : FiberExceptional E) :
    (planeSection α c E).card ≤ 2 * Fintype.card F := by
  obtain ⟨i,rfl⟩ := exists_index_of_fiber E hE
  rw [← section_eq_planeSection]
  exact section_card_le α (quarticPolynomial c).eval i

/-- An identity plane has a free `(x,u)` projection and cannot lie in a fiber solid. -/
theorem identity_fiber_disjoint (α : F) (c : Quartic F) (E : Plane F)
    (hI : IdentityExceptional α c E) : ¬ FiberExceptional E := by
  rintro ⟨d,hd⟩
  obtain ⟨g,hg,_⟩ := hI
  subst E
  have hv : graphMap g ![0,1,0] ∈ (graphPlane g).val := ⟨_,rfl⟩
  have hx := (hd hv).1
  simp [graphMap] at hx

end K44K35Free.Geometry.Fiber
