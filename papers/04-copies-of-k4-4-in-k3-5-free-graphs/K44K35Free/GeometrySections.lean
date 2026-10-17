import K44K35Free.Geometry
import K44K35Free.QuarticSections
import K44K35Free.ProjectivePairing
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

namespace K44K35Free.Geometry

noncomputable section
local instance geometrySectionsLocalInstance1 {F : Type*} : DecidableEq F := Classical.decEq F
open Module

/-- The affine cap calculation in the actual homogeneous coordinates. -/
theorem point_affine_relation {F : Type*} [Field F] (α : F) (c : Quartic F)
    (hα : K44K35Free.IsNonsquare α) (p q r : Param F) (t : F)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (h : point α c r = (1-t) • point α c p + t • point α c q) : p = q := by
  have hrx : r 0 = p 0 + t * (q 0-p 0) := by
    have hx := congrFun h 1
    simp [point] at hx
    linear_combination hx
  have hry : r 1 = p 1 + t * (q 1-p 1) := by
    have hx := congrFun h 2
    simp [point] at hx
    linear_combination hx
  have hrz : r 2 = p 2 + t * (q 2-p 2) := by
    have hx := congrFun h 3
    simp [point] at hx
    linear_combination hx
  have hu := congrFun h 4
  simp [point] at hu
  rw [hrx] at hu
  have hdx : q 0-p 0 = 0 := K44K35Free.u_coord_forces_hx_zero (x := p 0)
    (hx := q 0-p 0) (lam := t) (by linear_combination hu) ht0 ht1
  have hqx : q 0 = p 0 := sub_eq_zero.mp hdx
  have hrx' : r 0 = p 0 := by rw [hrx, hdx, mul_zero, add_zero]
  have hv := congrFun h 5
  simp [point] at hv
  rw [hry, hrz, hrx', hqx] at hv
  have hnorm : (q 1-p 1)^2 - α * (q 2-p 2)^2 = 0 :=
    K44K35Free.v_coord_forces_norm_zero (f := fun x => (quarticPolynomial c).eval x)
      (x := p 0) (y := p 1) (hy := q 1-p 1) (z := p 2) (hz := q 2-p 2)
      (lam := t) (by linear_combination hv) ht0 ht1
  have hpair := K44K35Free.nonsquare_zero_of_sq_sub hα hnorm
  ext i
  fin_cases i
  · exact hqx.symm
  · exact (sub_eq_zero.mp hpair.1).symm
  · exact (sub_eq_zero.mp hpair.2).symm

/-- Every three different points of the cap are linearly independent as homogeneous vectors. -/
theorem point_triple_linearIndependent {F : Type*} [Field F]
    (α : F) (c : Quartic F) (hα : K44K35Free.IsNonsquare α)
    (p q r : Param F) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    LinearIndependent F ![point α c p, point α c q, point α c r] := by
  rw [Fintype.linearIndependent_iff]
  intro a ha
  have hrel : a 0 • point α c p + a 1 • point α c q + a 2 • point α c r = 0 := by
    simpa [Fin.sum_univ_succ, add_assoc] using ha
  have hsum : a 0 + a 1 + a 2 = 0 := by
    have hz := congrFun hrel 0
    simpa [point] using hz
  have ha2 : a 2 = 0 := by
    by_contra hne
    let t := -(a 1)/(a 2)
    have hAff : point α c r = (1-t) • point α c p + t • point α c q := by
      ext i
      have hz := congrFun hrel i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hz ⊢
      dsimp [t]
      field_simp
      linear_combination hz - point α c p i * hsum
    have ht0 : t ≠ 0 := by
      intro hz
      have heq : point α c r = point α c p := by simpa [hz] using hAff
      exact hpr ((point_injective α c) heq).symm
    have ht1 : t ≠ 1 := by
      intro hz
      have heq : point α c r = point α c q := by simpa [hz] using hAff
      exact hqr ((point_injective α c) heq).symm
    exact hpq (point_affine_relation α c hα p q r t ht0 ht1 hAff)
  have hsum' : a 0 = -(a 1) := by linear_combination hsum - ha2
  have ha1 : a 1 = 0 := by
    by_contra hne
    have heq : point α c p = point α c q := by
      ext i
      have hz := congrFun hrel i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hz
      rw [ha2, hsum'] at hz
      have hh : a 1 * (point α c p i-point α c q i) = 0 := by
        linear_combination -hz
      exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hne)
    exact hpq ((point_injective α c) heq)
  have ha0 : a 0 = 0 := by linear_combination hsum - ha1 - ha2
  intro i
  fin_cases i <;> simp [ha0, ha1, ha2]

/-- The actual plane spanned by a triple of different cap points. -/
def triplePlane {F : Type*} [Field F]
    (α : F) (c : Quartic F) (hα : K44K35Free.IsNonsquare α)
    (p q r : Param F) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) : Plane F :=
  ⟨Submodule.span F (Set.range ![point α c p, point α c q, point α c r]), by
    simpa using finrank_span_eq_card
      (point_triple_linearIndependent α c hα p q r hpq hpr hqr)⟩

theorem triplePlane_le {F : Type*} [Field F]
    (α : F) (c : Quartic F) (hα : K44K35Free.IsNonsquare α)
    (p q r : Param F) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (U : Submodule F (V F))
    (hp : point α c p ∈ U) (hq : point α c q ∈ U) (hr : point α c r ∈ U) :
    (triplePlane α c hα p q r hpq hpr hqr).val ≤ U := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  fin_cases i <;> simpa using (by assumption)

theorem plane_eq_of_three_points {F : Type*} [Field F]
    (α : F) (c : Quartic F) (hα : K44K35Free.IsNonsquare α)
    (p q r : Param F) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (E : Plane F)
    (hp : point α c p ∈ E.val) (hq : point α c q ∈ E.val)
    (hr : point α c r ∈ E.val) :
    triplePlane α c hα p q r hpq hpr hqr = E := by
  apply Subtype.ext
  apply Submodule.eq_of_le_of_finrank_eq
    (triplePlane_le α c hα p q r hpq hpr hqr E.val hp hq hr)
  rw [(triplePlane α c hα p q r hpq hpr hqr).property, E.property]

/-- Two different planes cannot share three points of this cap. -/
theorem section_inter_card_le_two {F : Type*} [Field F] [Fintype F]
    (α : F) (c : Quartic F) (hα : K44K35Free.IsNonsquare α)
    (E Q : Plane F) (hEQ : E ≠ Q) :
    ((planeSection α c E) ∩ (planeSection α c Q)).card ≤ 2 := by
  classical
  by_contra hbad
  obtain ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr⟩ :=
    Finset.two_lt_card_iff.mp (by omega : 2 < ((planeSection α c E) ∩
      (planeSection α c Q)).card)
  have hp' := Finset.mem_inter.mp hp
  have hq' := Finset.mem_inter.mp hq
  have hr' := Finset.mem_inter.mp hr
  have he := plane_eq_of_three_points α c hα p q r hpq hpr hqr E
    ((mem_section α c E p).mp hp'.1) ((mem_section α c E q).mp hq'.1)
    ((mem_section α c E r).mp hr'.1)
  have hq := plane_eq_of_three_points α c hα p q r hpq hpr hqr Q
    ((mem_section α c Q p).mp hp'.2) ((mem_section α c Q q).mp hq'.2)
    ((mem_section α c Q r).mp hr'.2)
  exact hEQ (he.symm.trans hq)

/-- Every triple of cap points spans an actual projective plane. -/
theorem exists_plane_of_card_three {F : Type*} [Field F] [Fintype F]
    (α : F) (c : Quartic F) (hα : K44K35Free.IsNonsquare α)
    (X : Finset (Param F)) (hX : X.card = 3) :
    ∃ Q : Plane F, X ⊆ planeSection α c Q ∧
      Submodule.span F (point α c '' (↑X : Set (Param F))) = Q.val := by
  classical
  obtain ⟨p, q, r, hpq, hpr, hqr, rfl⟩ := Finset.card_eq_three.mp hX
  let Q := triplePlane α c hα p q r hpq hpr hqr
  have hpin : point α c p ∈ Q.val := Submodule.subset_span ⟨0, rfl⟩
  have hqin : point α c q ∈ Q.val := Submodule.subset_span ⟨1, rfl⟩
  have hrin : point α c r ∈ Q.val := Submodule.subset_span ⟨2, rfl⟩
  refine ⟨Q, ?_, ?_⟩
  · intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · simpa only [mem_section] using hpin
    · simpa only [mem_section] using hqin
    · simpa only [mem_section] using hrin
  · apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨a, ha, rfl⟩
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl
      · exact hpin
      · exact hqin
      · exact hrin
    · apply triplePlane_le α c hα p q r hpq hpr hqr
      · exact Submodule.subset_span ⟨p, by simp, rfl⟩
      · exact Submodule.subset_span ⟨q, by simp, rfl⟩
      · exact Submodule.subset_span ⟨r, by simp, rfl⟩

/-- Uniqueness of the plane containing a triple of cap points. -/
theorem plane_unique_of_card_three {F : Type*} [Field F] [Fintype F]
    (α : F) (c : Quartic F) (hα : K44K35Free.IsNonsquare α)
    (X : Finset (Param F)) (hX : X.card = 3) (E Q : Plane F)
    (hE : X ⊆ planeSection α c E) (hQ : X ⊆ planeSection α c Q) : E = Q := by
  classical
  by_contra hne
  have hsub : X ⊆ (planeSection α c E) ∩ (planeSection α c Q) :=
    fun p hp => Finset.mem_inter.mpr ⟨hE hp, hQ hp⟩
  have := (Finset.card_le_card hsub).trans (section_inter_card_le_two α c hα E Q hne)
  omega

/-- Projection to the homogeneous parabola coordinates `(w,x,u)`. -/
def projection {F : Type*} [Field F] : V F →ₗ[F] (Fin 3 → F) where
  toFun v := ![v 0, v 1, v 4]
  map_add' a b := by ext i; fin_cases i <;> rfl
  map_smul' a b := by ext i; fin_cases i <;> rfl

def projectRestriction {F : Type*} [Field F] (E : Plane F) :
    E.val →ₗ[F] (Fin 3 → F) := projection.comp E.val.subtype

/-- Distinct x coordinates give the elementary Vandermonde independence. -/
theorem parabola_triple_linearIndependent {F : Type*} [Field F] (x y z : F)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    LinearIndependent F ![![1,x,x^2], ![1,y,y^2], ![1,z,z^2]] := by
  rw [Fintype.linearIndependent_iff]
  intro a ha
  have h0 : a 0+a 1+a 2=0 := by
    simpa [Fin.sum_univ_succ, add_assoc] using congrFun ha 0
  have h1 : a 0*x+a 1*y+a 2*z=0 := by
    simpa [Fin.sum_univ_succ, add_assoc] using congrFun ha 1
  have h2 : a 0*x^2+a 1*y^2+a 2*z^2=0 := by
    simpa [Fin.sum_univ_succ, add_assoc] using congrFun ha 2
  have ha0 : a 0=0 := by
    have hfact : a 0*((x-y)*(x-z))=0 := by
      linear_combination h2-(y+z)*h1+y*z*h0
    exact (mul_eq_zero.mp hfact).resolve_right
      (mul_ne_zero (sub_ne_zero.mpr hxy) (sub_ne_zero.mpr hxz))
  have ha1 : a 1=0 := by
    have hfact : a 1*((y-x)*(y-z))=0 := by
      linear_combination h2-(x+z)*h1+x*z*h0
    exact (mul_eq_zero.mp hfact).resolve_right
      (mul_ne_zero (sub_ne_zero.mpr hxy.symm) (sub_ne_zero.mpr hyz))
  have ha2 : a 2=0 := by linear_combination h0-ha0-ha1
  intro i
  fin_cases i <;> simp [ha0,ha1,ha2]

/-- Three cap points with distinct x coordinates force a graph plane. -/
theorem exists_graphPlane_of_three_x {F : Type*} [Field F]
    (α : F) (c : Quartic F) (E : Plane F) (p q r : Param F)
    (hp : point α c p ∈ E.val) (hq : point α c q ∈ E.val)
    (hr : point α c r ∈ E.val)
    (hpq : p 0 ≠ q 0) (hpr : p 0 ≠ r 0) (hqr : q 0 ≠ r 0) :
    ∃ g : GraphData F, graphPlane g = E := by
  let H := Submodule.span F
    (Set.range ![![1,p 0,(p 0)^2], ![1,q 0,(q 0)^2], ![1,r 0,(r 0)^2]])
  have hfin : finrank F H = 3 := by
    simpa [H] using finrank_span_eq_card
      (parabola_triple_linearIndependent (p 0) (q 0) (r 0) hpq hpr hqr)
  have htop : H = ⊤ := Submodule.eq_top_of_finrank_eq (by simpa using hfin)
  have hle : H ≤ LinearMap.range (projectRestriction E) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨⟨point α c p, hp⟩, rfl⟩
    · exact ⟨⟨point α c q, hq⟩, rfl⟩
    · exact ⟨⟨point α c r, hr⟩, rfl⟩
  have hsurj : Function.Surjective (projectRestriction E) := by
    apply LinearMap.range_eq_top.mp
    exact top_le_iff.mp (by simpa [htop] using hle)
  have hinj : Function.Injective (projectRestriction E) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simpa using E.property)).mpr hsurj
  let e : E.val ≃ₗ[F] (Fin 3 → F) :=
    LinearEquiv.ofBijective (projectRestriction E) ⟨hinj, hsurj⟩
  let L : (Fin 3 → F) →ₗ[F] V F := E.val.subtype.comp e.symm.toLinearMap
  have hproj (t : Fin 3 → F) : projection (L t) = t := by
    change e (e.symm t) = t
    exact e.apply_symm_apply t
  have hcoord (k : Fin 6) (t : Fin 3 → F) :
      linEval (fun i => L (Pi.single i 1) k) t = L t k := by
    have hb (i : Fin 3) : (fun j : Fin 3 => if i = j then (1 : F) else 0) =
        Pi.single i 1 := by
      ext j
      simp [Pi.single_apply, eq_comm]
    have ht := congrFun (LinearMap.pi_apply_eq_sum_univ L t) k
    simp_rw [hb] at ht
    simp [Fin.sum_univ_succ] at ht
    dsimp [linEval]
    linear_combination -ht
  let g : GraphData F := ⟨fun i => L (Pi.single i 1) 2,
    fun i => L (Pi.single i 1) 3, fun i => L (Pi.single i 1) 5⟩
  have hmap : graphMap g = L := by
    apply LinearMap.ext
    intro t
    funext i
    have ht := hproj t
    fin_cases i
    · exact (congrFun ht 0).symm
    · exact (congrFun ht 1).symm
    · exact hcoord 2 t
    · exact hcoord 3 t
    · exact (congrFun ht 2).symm
    · exact hcoord 5 t
  refine ⟨g, Subtype.ext ?_⟩
  change LinearMap.range (graphMap g) = E.val
  rw [hmap]
  ext v
  constructor
  · rintro ⟨t, rfl⟩
    exact (e.symm t).property
  · intro hv
    refine ⟨e ⟨v,hv⟩, ?_⟩
    change ((e.symm (e ⟨v,hv⟩) : E.val) : V F) = v
    rw [e.symm_apply_apply]

/-- A fixed-x fiber of a nonfiber plane contains at most two cap points. -/
theorem fixed_x_section_card_le_two {F : Type*} [Field F] [Fintype F]
    (α : F) (c : Quartic F) (hα : K44K35Free.IsNonsquare α)
    (E : Plane F) (hE : ¬ FiberExceptional E) (d : F) :
    ((planeSection α c E).filter (fun p => p 0 = d)).card ≤ 2 := by
  classical
  by_contra hbad
  obtain ⟨p,q,r,hp,hq,hr,hpq,hpr,hqr⟩ := Finset.two_lt_card_iff.mp
    (by omega : 2 < ((planeSection α c E).filter (fun p => p 0 = d)).card)
  have hp' := Finset.mem_filter.mp hp
  have hq' := Finset.mem_filter.mp hq
  have hr' := Finset.mem_filter.mp hr
  have heq := plane_eq_of_three_points α c hα p q r hpq hpr hqr E
    ((mem_section _ _ _ _).mp hp'.1) ((mem_section _ _ _ _).mp hq'.1)
    ((mem_section _ _ _ _).mp hr'.1)
  apply hE
  refine ⟨d, ?_⟩
  rw [← heq]
  apply triplePlane_le α c hα p q r hpq hpr hqr
  · change p 0 = d * 1 ∧ (p 0)^2 = d^2 * 1
    simp [hp'.2]
  · change q 0 = d * 1 ∧ (q 0)^2 = d^2 * 1
    simp [hq'.2]
  · change r 0 = d * 1 ∧ (r 0)^2 = d^2 * 1
    simp [hr'.2]

/-- If a section uses three x coordinates, its plane has graph form. -/
theorem exists_graphPlane_of_x_image_card {F : Type*} [Field F] [Fintype F]
    (α : F) (c : Quartic F) (E : Plane F)
    (h : 2 < ((planeSection α c E).image (fun p => p 0)).card) :
    ∃ g : GraphData F, graphPlane g = E := by
  classical
  obtain ⟨x,y,z,hx,hy,hz,hxy,hxz,hyz⟩ := Finset.two_lt_card_iff.mp h
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hz
  exact exists_graphPlane_of_three_x α c E p q r
    ((mem_section _ _ _ _).mp hp) ((mem_section _ _ _ _).mp hq)
    ((mem_section _ _ _ _).mp hr) hxy hxz hyz

/-- Outside the concrete identity and fiber families, every plane section has at most four points. -/
theorem nonexceptional_section_card_le_four {F : Type*} [Field F] [Fintype F]
    (α : F) (c : Quartic F) (hα : K44K35Free.IsNonsquare α)
    (E : Plane F) (hE : ¬ Exceptional α c E) :
    (planeSection α c E).card ≤ 4 := by
  classical
  have hI : ¬ IdentityExceptional α c E := fun h => hE (Or.inl h)
  have hF : ¬ FiberExceptional E := fun h => hE (Or.inr h)
  by_cases hg : ∃ g : GraphData F, graphPlane g = E
  · obtain ⟨g,rfl⟩ := hg
    have hpoly : sectionPolynomial α c g ≠ 0 := by
      intro hz
      exact hI ⟨g,rfl,hz⟩
    rw [card_graphPlane_section]
    have hsub : polynomialRootSet (sectionPolynomial α c g) ⊆
        (sectionPolynomial α c g).roots.toFinset := by
      intro x hx
      exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hpoly).mpr
        ((mem_polynomialRootSet _ _).mp hx))
    calc
      (polynomialRootSet (sectionPolynomial α c g)).card ≤
        (sectionPolynomial α c g).roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ (sectionPolynomial α c g).roots.card := Multiset.toFinset_card_le _
      _ ≤ (sectionPolynomial α c g).natDegree := Polynomial.card_roots' _
      _ ≤ 4 := sectionPolynomial_natDegree_le α c g
  · have himage : ((planeSection α c E).image (fun p => p 0)).card ≤ 2 := by
      by_contra hbad
      exact hg (exists_graphPlane_of_x_image_card α c E (by omega))
    rw [Finset.card_eq_sum_card_image (fun p : Param F => p 0) (planeSection α c E)]
    calc
      ∑ d ∈ (planeSection α c E).image (fun p => p 0),
          ((planeSection α c E).filter (fun p => p 0 = d)).card ≤
        ∑ _d ∈ (planeSection α c E).image (fun p => p 0), 2 := by
          apply Finset.sum_le_sum
          intro d hd
          exact fixed_x_section_card_le_two α c hα E hF d
      _ = ((planeSection α c E).image (fun p => p 0)).card * 2 := by simp
      _ ≤ 4 := by omega

/-- Lemma 8, for the actual projective pairing and actual nonexceptional rich planes. -/
theorem lemma_8_controlled_intersections {F : Type*} [Field F] [Fintype F]
    (α : F) (c : Quartic F) (hα : K44K35Free.IsNonsquare α)
    (T : V F ≃ₗ[F] V F) (A C E : Plane F)
    (hpair : A = leftDual T C)
    (hA : ¬ Exceptional α c A) (hC : ¬ Exceptional α c C)
    (hE : Exceptional α c E) :
    ((planeSection α c A) ∩ (planeSection α c (leftDual T E))).card ≤ 2 ∧
    ((planeSection α c C) ∩ (planeSection α c (rightDual T E))).card ≤ 2 := by
  constructor
  · apply section_inter_card_le_two α c hα
    intro h
    have hCE : C = E := (leftDual T).injective (hpair.symm.trans h)
    exact hC (hCE.symm ▸ hE)
  · apply section_inter_card_le_two α c hα
    intro h
    have hAE : A = E := by
      rw [hpair, h]
      exact (leftDual T).apply_symm_apply E
    exact hA (hAE.symm ▸ hE)

end
end K44K35Free.Geometry
