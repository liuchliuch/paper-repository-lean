import K44K35Free.NormCounts
import K44K35Free.Geometry
import K44K35Free.Counts
import Mathlib.Data.Fintype.Sigma

namespace K44K35Free.Geometry

noncomputable section
open scoped BigOperators
open Polynomial
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F]

/-- The five actual coefficients of the section polynomial, in increasing order. -/
def sectionCoefficients (α : F) (c : Quartic F) (g : GraphData F) : Fin 5 → F :=
  ![c 0 + g.A 0 ^ 2 - α * g.B 0 ^ 2 - g.C 0,
    c 1 + 2 * g.A 0 * g.A 1 - 2 * α * g.B 0 * g.B 1 - g.C 1,
    c 2 + g.A 1 ^ 2 + 2 * g.A 0 * g.A 2 -
      α * (g.B 1 ^ 2 + 2 * g.B 0 * g.B 2) - g.C 2,
    c 3 + 2 * g.A 1 * g.A 2 - 2 * α * g.B 1 * g.B 2,
    1 + g.A 2 ^ 2 - α * g.B 2 ^ 2]

lemma sectionPolynomial_expansion (α : F) (c : Quartic F) (g : GraphData F) :
    sectionPolynomial α c g =
      C (sectionCoefficients α c g 0) + C (sectionCoefficients α c g 1) * X +
      C (sectionCoefficients α c g 2) * X ^ 2 +
      C (sectionCoefficients α c g 3) * X ^ 3 +
      C (sectionCoefficients α c g 4) * X ^ 4 := by
  simp [sectionPolynomial, quarticPolynomial, qPolynomial, sectionCoefficients,
    Fin.sum_univ_succ]
  simp only [map_ofNat]
  ring

lemma coeff_sectionPolynomial (α : F) (c : Quartic F) (g : GraphData F) (i : Fin 5) :
    (sectionPolynomial α c g).coeff i = sectionCoefficients α c g i := by
  rw [sectionPolynomial_expansion]
  fin_cases i <;> simp [Polynomial.coeff_add,
    Polynomial.coeff_C, Polynomial.coeff_X]

lemma sectionPolynomial_eq_zero_iff (α : F) (c : Quartic F) (g : GraphData F) :
    sectionPolynomial α c g = 0 ↔ ∀ i, sectionCoefficients α c g i = 0 := by
  constructor
  · intro h i
    rw [← coeff_sectionPolynomial, h, coeff_zero]
  · intro h
    rw [sectionPolynomial_expansion]
    simp [h]

/-- The cubic coefficient vanishes precisely when equation (11) holds. -/
lemma coeff_sectionPolynomial_three (α : F) (c : Quartic F) (g : GraphData F) :
    (sectionPolynomial α c g).coeff 3 =
      c 3 + 2 * g.A 1 * g.A 2 - 2 * α * g.B 1 * g.B 2 := by
  exact coeff_sectionPolynomial α c g 3

/-- The forced quadratic `C` in an identity graph plane. -/
def identityC (α : F) (c : Quartic F) (A B : Fin 3 → F) : Fin 3 → F :=
  ![c 0 + A 0 ^ 2 - α * B 0 ^ 2,
    c 1 + 2 * A 0 * A 1 - 2 * α * B 0 * B 1,
    c 2 + A 1 ^ 2 + 2 * A 0 * A 2 - α * (B 1 ^ 2 + 2 * B 0 * B 2)]

lemma identity_iff (α : F) (c : Quartic F) (g : GraphData F) :
    sectionPolynomial α c g = 0 ↔
      g.A 2 ^ 2 - α * g.B 2 ^ 2 = -1 ∧
      2 * g.A 2 * g.A 1 + (-2 * α * g.B 2) * g.B 1 = -c 3 ∧
      g.C = identityC α c g.A g.B := by
  rw [sectionPolynomial_eq_zero_iff]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · have h4 := h 4
      simp [sectionCoefficients] at h4
      linear_combination h4
    · have h3 := h 3
      simp [sectionCoefficients] at h3
      linear_combination h3
    · funext i
      have hi := h i.castSucc.castSucc
      fin_cases i <;> simp [sectionCoefficients, identityC] at hi ⊢ <;>
        linear_combination -hi
  · rintro ⟨h4, h3, hC⟩ i
    fin_cases i <;> simp only [sectionCoefficients] <;> dsimp
    · rw [hC]; simp [identityC]
    · rw [hC]; simp [identityC]
    · rw [hC]; simp [identityC]
    · linear_combination h3
    · linear_combination h4

/-- Solutions to one nonzero affine-linear equation in two variables. -/
def LinearFiber (u v r : F) := {p : F × F // u * p.1 + v * p.2 = r}

noncomputable def linearFiberEquiv (u v r : F) (huv : u ≠ 0 ∨ v ≠ 0) :
    F ≃ LinearFiber u v r := by
  classical
  by_cases hu : u = 0
  · have hv : v ≠ 0 := huv.resolve_left (not_not.mpr hu)
    refine
      { toFun := fun t => ⟨(t, (r - u * t) / v), ?_⟩
        invFun := fun p => p.val.1
        left_inv := fun _ => rfl
        right_inv := ?_ }
    · dsimp
      field_simp
      ring
    · intro p
      apply Subtype.ext
      change (p.val.1, (r - u * p.val.1) / v) = p.val
      apply Prod.ext
      · rfl
      dsimp
      apply (div_eq_iff hv).mpr
      linear_combination -p.property
  · refine
      { toFun := fun t => ⟨((r - v * t) / u, t), ?_⟩
        invFun := fun p => p.val.2
        left_inv := fun _ => rfl
        right_inv := ?_ }
    · dsimp
      field_simp
      ring
    · intro p
      apply Subtype.ext
      change ((r - v * p.val.2) / u, p.val.2) = p.val
      apply Prod.ext
      · dsimp
        apply (div_eq_iff hu).mpr
        linear_combination -p.property
      · rfl

lemma norm_linear_nonzero (α : F) (h2 : (2 : F) ≠ 0) (n : NormFiber α (-1)) :
    2 * n.val.1 ≠ 0 ∨ -2 * α * n.val.2 ≠ 0 := by
  by_cases ha : n.val.1 = 0
  · right
    intro h
    have hz : α * n.val.2 = 0 := by
      apply (mul_eq_zero.mp (show (-2) * (α * n.val.2) = 0 by linear_combination h)).resolve_left
      exact neg_ne_zero.mpr h2
    have hn := n.property
    rw [ha] at hn
    have : (1 : F) = 0 := by linear_combination hn + n.val.2 * hz
    exact one_ne_zero this
  · exact Or.inl (mul_ne_zero h2 ha)

omit [Field F] in
lemma graphData_eq {g h : GraphData F} (hA : g.A = h.A) (hB : g.B = h.B)
    (hC : g.C = h.C) : g = h := by
  cases g
  cases h
  cases hA
  cases hB
  cases hC
  rfl

/-- Independent choices in equations (10) and (11), followed by the constant terms. -/
def IdentityChoice (α : F) (c : Quartic F) :=
  Σ n : NormFiber α (-1), LinearFiber (2 * n.val.1) (-2 * α * n.val.2) (-c 3) × (F × F)

noncomputable def identityDataEquiv (α : F) (c : Quartic F) :
    IdentityChoice α c ≃ {g : GraphData F // sectionPolynomial α c g = 0} where
  toFun d :=
    let A : Fin 3 → F := ![d.2.2.1, d.2.1.val.1, d.1.val.1]
    let B : Fin 3 → F := ![d.2.2.2, d.2.1.val.2, d.1.val.2]
    ⟨⟨A, B, identityC α c A B⟩,
      (identity_iff α c _).mpr ⟨by simpa [A, B] using d.1.property,
        by simpa [A, B] using d.2.1.property, rfl⟩⟩
  invFun g :=
    let hg := (identity_iff α c g.val).mp g.property
    ⟨⟨(g.val.A 2, g.val.B 2), hg.1⟩,
      ⟨⟨(g.val.A 1, g.val.B 1), hg.2.1⟩, (g.val.A 0, g.val.B 0)⟩⟩
  left_inv d := by
    apply Sigma.ext
    · apply Subtype.ext
      rfl
    · apply heq_of_eq
      apply Prod.ext
      · apply Subtype.ext
        rfl
      · rfl
  right_inv g := by
    apply Subtype.ext
    have hC := ((identity_iff α c g.val).mp g.property).2.2
    apply graphData_eq
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> rfl
    · dsimp
      rw [hC]
      congr 1 <;> funext i <;> fin_cases i <;> rfl

/-- The cubic equation contributes one free field parameter for every leading pair. -/
noncomputable def identityChoiceEquiv (α : F) (c : Quartic F) (h2 : (2 : F) ≠ 0) :
    IdentityChoice α c ≃ NormFiber α (-1) × F × (F × F) :=
  (Equiv.sigmaCongrRight fun n =>
    Equiv.prodCongr (linearFiberEquiv _ _ _ (norm_linear_nonzero α h2 n)).symm
      (Equiv.refl (F × F))).trans (Equiv.sigmaEquivProd _ _)

/-- Equation (6), at the level of the unique graph-plane coefficients. -/
theorem card_identity_graph_data [Fintype F] (α : F) (c : Quartic F)
    (hα : IsNonsquare α) (hF : ringChar F ≠ 2) :
    Nat.card {g : GraphData F // sectionPolynomial α c g = 0} =
      Fintype.card F ^ 3 * (Fintype.card F + 1) := by
  rw [← Nat.card_congr (identityDataEquiv α c),
    Nat.card_congr (identityChoiceEquiv α c (Ring.two_ne_zero hF))]
  simp only [Nat.card_prod, card_norm_neg_one hα hF, Nat.card_eq_fintype_card,
    Fintype.card_prod]
  ring

/-- The graph coefficients and the actual identity planes are in bijection. -/
noncomputable def identityPlaneEquiv (α : F) (c : Quartic F) :
    {g : GraphData F // sectionPolynomial α c g = 0} ≃
      {E : Plane F // IdentityExceptional α c E} :=
  Equiv.ofBijective
    (fun g => ⟨graphPlane g.val, ⟨g.val, rfl, g.property⟩⟩)
    ⟨by
      intro g h heq
      apply Subtype.ext
      exact graphPlane_injective (congrArg Subtype.val heq),
    by
      rintro ⟨E, ⟨g, hE, hg⟩⟩
      exact ⟨⟨g, hg⟩, Subtype.ext hE⟩⟩

/-- Equation (6) for the actual three-dimensional subspaces in homogeneous space. -/
theorem card_identity_planes [Fintype F] (α : F) (c : Quartic F)
    (hα : IsNonsquare α) (hF : ringChar F ≠ 2) :
    Nat.card {E : Plane F // IdentityExceptional α c E} =
      Fintype.card F ^ 3 * (Fintype.card F + 1) := by
  rw [← Nat.card_congr (identityPlaneEquiv α c)]
  exact card_identity_graph_data α c hα hF

/-- The section of an identity graph plane has one point for each x coordinate. -/
noncomputable def identitySectionEquiv (α : F) (c : Quartic F) (g : GraphData F)
    (hg : sectionPolynomial α c g = 0) :
    F ≃ {p : Param F // point α c p ∈ (graphPlane g).val} where
  toFun t := ⟨![t, (qPolynomial g.A).eval t, (qPolynomial g.B).eval t], by
    rw [point_mem_graphPlane_iff]
    simp [hg]⟩
  invFun p := p.val 0
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    have hp := (point_mem_graphPlane_iff α c g p.val).mp p.property
    funext i
    fin_cases i
    · rfl
    · exact hp.1.symm
    · exact hp.2.1.symm

/-- Every actual identity plane contains exactly `q` points of the constructed cap. -/
theorem identity_plane_section_card [Fintype F] (α : F) (c : Quartic F) (E : Plane F)
    (hE : IdentityExceptional α c E) : (planeSection α c E).card = Fintype.card F := by
  classical
  obtain ⟨g, rfl, hg⟩ := hE
  have hc := Nat.card_congr (identitySectionEquiv α c g hg)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_subtype] at hc
  simpa [planeSection] using hc.symm

/-- After fixing a point, only the leading norm pair and the linear pair remain free. -/
def IdentityPointChoice (α : F) (c : Quartic F) :=
  Σ n : NormFiber α (-1), LinearFiber (2 * n.val.1) (-2 * α * n.val.2) (-c 3)

noncomputable def identityDataAtPoint (α : F) (c : Quartic F) (p : Param F)
    (d : IdentityPointChoice α c) : GraphData F :=
  let A : Fin 3 → F :=
    ![p 1 - d.2.val.1 * p 0 - d.1.val.1 * p 0 ^ 2, d.2.val.1, d.1.val.1]
  let B : Fin 3 → F :=
    ![p 2 - d.2.val.2 * p 0 - d.1.val.2 * p 0 ^ 2, d.2.val.2, d.1.val.2]
  ⟨A, B, identityC α c A B⟩

lemma identityDataAtPoint_identity (α : F) (c : Quartic F) (p : Param F)
    (d : IdentityPointChoice α c) : sectionPolynomial α c (identityDataAtPoint α c p d) = 0 := by
  apply (identity_iff α c _).mpr
  exact ⟨by simpa [identityDataAtPoint] using d.1.property,
    by simpa [identityDataAtPoint] using d.2.property, rfl⟩

lemma identityDataAtPoint_mem (α : F) (c : Quartic F) (p : Param F)
    (d : IdentityPointChoice α c) : point α c p ∈ (graphPlane (identityDataAtPoint α c p d)).val := by
  rw [point_mem_graphPlane_iff]
  refine ⟨?_, ?_, ?_⟩
  · simp [identityDataAtPoint]
    ring
  · simp [identityDataAtPoint]
    ring
  · rw [identityDataAtPoint_identity, eval_zero]

noncomputable def identityPointDataEquiv (α : F) (c : Quartic F) (p : Param F) :
    IdentityPointChoice α c ≃
      {g : GraphData F // sectionPolynomial α c g = 0 ∧ point α c p ∈ (graphPlane g).val} where
  toFun d := ⟨identityDataAtPoint α c p d, identityDataAtPoint_identity α c p d,
    identityDataAtPoint_mem α c p d⟩
  invFun g :=
    let hg := (identity_iff α c g.val).mp g.property.1
    ⟨⟨(g.val.A 2, g.val.B 2), hg.1⟩, ⟨(g.val.A 1, g.val.B 1), hg.2.1⟩⟩
  left_inv d := by
    apply Sigma.ext
    · apply Subtype.ext
      rfl
    · apply heq_of_eq
      apply Subtype.ext
      rfl
  right_inv g := by
    apply Subtype.ext
    have hp := (point_mem_graphPlane_iff α c g.val p).mp g.property.2
    have hC := ((identity_iff α c g.val).mp g.property.1).2.2
    have hA : (identityDataAtPoint α c p
        ⟨⟨(g.val.A 2, g.val.B 2), ((identity_iff α c g.val).mp g.property.1).1⟩,
          ⟨(g.val.A 1, g.val.B 1), ((identity_iff α c g.val).mp g.property.1).2.1⟩⟩).A = g.val.A := by
      funext i
      fin_cases i
      · simp [identityDataAtPoint]
        simp only [qPolynomial_eval] at hp
        linear_combination hp.1
      · rfl
      · rfl
    have hB : (identityDataAtPoint α c p
        ⟨⟨(g.val.A 2, g.val.B 2), ((identity_iff α c g.val).mp g.property.1).1⟩,
          ⟨(g.val.A 1, g.val.B 1), ((identity_iff α c g.val).mp g.property.1).2.1⟩⟩).B = g.val.B := by
      funext i
      fin_cases i
      · simp [identityDataAtPoint]
        simp only [qPolynomial_eval] at hp
        linear_combination hp.2.1
      · rfl
      · rfl
    apply graphData_eq hA hB
    exact (congrArg₂ (identityC α c) hA hB).trans hC.symm

noncomputable def identityPointChoiceEquiv (α : F) (c : Quartic F) (h2 : (2 : F) ≠ 0) :
    IdentityPointChoice α c ≃ NormFiber α (-1) × F :=
  (Equiv.sigmaCongrRight fun n =>
    (linearFiberEquiv _ _ _ (norm_linear_nonzero α h2 n)).symm).trans
      (Equiv.sigmaEquivProd _ _)

/-- Exactly `q(q+1)` identity graph planes pass through every fixed cap point. -/
theorem card_identity_graph_data_through_point [Fintype F] (α : F) (c : Quartic F)
    (hα : IsNonsquare α) (hF : ringChar F ≠ 2) (p : Param F) :
    Nat.card {g : GraphData F // sectionPolynomial α c g = 0 ∧
      point α c p ∈ (graphPlane g).val} = Fintype.card F * (Fintype.card F + 1) := by
  rw [← Nat.card_congr (identityPointDataEquiv α c p),
    Nat.card_congr (identityPointChoiceEquiv α c (Ring.two_ne_zero hF)), Nat.card_prod,
    card_norm_neg_one hα hF, Nat.card_eq_fintype_card, mul_comm]

noncomputable def identityPointPlaneEquiv (α : F) (c : Quartic F) (p : Param F) :
    {g : GraphData F // sectionPolynomial α c g = 0 ∧ point α c p ∈ (graphPlane g).val} ≃
      {E : Plane F // IdentityExceptional α c E ∧ point α c p ∈ E.val} :=
  Equiv.ofBijective
    (fun g => ⟨graphPlane g.val, ⟨g.val, rfl, g.property.1⟩, g.property.2⟩)
    ⟨by
      intro g h heq
      apply Subtype.ext
      exact graphPlane_injective (congrArg Subtype.val heq),
    by
      rintro ⟨E, ⟨⟨g, hE, hg⟩, hp⟩⟩
      exact ⟨⟨g, hg, by simpa only [hE] using hp⟩, Subtype.ext hE⟩⟩

/-- Proposition 4's pointwise identity-plane incidence count for actual planes. -/
theorem card_identity_planes_through_point [Fintype F] (α : F) (c : Quartic F)
    (hα : IsNonsquare α) (hF : ringChar F ≠ 2) (p : Param F) :
    Nat.card {E : Plane F // IdentityExceptional α c E ∧ point α c p ∈ E.val} =
      Fintype.card F * (Fintype.card F + 1) := by
  rw [← Nat.card_congr (identityPointPlaneEquiv α c p)]
  exact card_identity_graph_data_through_point α c hα hF p

/-- The finite family of actual identity planes. -/
noncomputable def identityPlanes [Fintype F] (α : F) (c : Quartic F) : Finset (Plane F) := by
  classical
  letI := Fintype.ofFinite (Plane F)
  exact Finset.univ.filter (IdentityExceptional α c)

@[simp] lemma mem_identityPlanes [Fintype F] (α : F) (c : Quartic F) (E : Plane F) :
    E ∈ identityPlanes α c ↔ IdentityExceptional α c E := by
  classical
  simp [identityPlanes]

/-- Finset version of equation (6). -/
theorem identityPlanes_card [Fintype F] (α : F) (c : Quartic F)
    (hα : IsNonsquare α) (hF : ringChar F ≠ 2) :
    (identityPlanes α c).card = Fintype.card F ^ 3 * (Fintype.card F + 1) := by
  classical
  letI := Fintype.ofFinite (Plane F)
  have h := card_identity_planes α c hα hF
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
  simpa only [identityPlanes] using h

/-- The identity planes contribute `q⁴(q+1)` incidences. -/
theorem sum_identityPlanes_section_card [Fintype F] (α : F) (c : Quartic F)
    (hα : IsNonsquare α) (hF : ringChar F ≠ 2) :
    ∑ E ∈ identityPlanes α c, (planeSection α c E).card =
      Fintype.card F ^ 4 * (Fintype.card F + 1) := by
  classical
  have he : ∑ E ∈ identityPlanes α c, (planeSection α c E).card =
      ∑ E ∈ identityPlanes α c, Fintype.card F := by
    apply Finset.sum_congr rfl
    intro E hE
    exact identity_plane_section_card α c E ((mem_identityPlanes α c E).mp hE)
  rw [he, Finset.sum_const, smul_eq_mul, identityPlanes_card α c hα hF]
  ring

/-- Finset version of the pointwise identity-plane incidence formula. -/
theorem identityPlanes_through_point_card [Fintype F] (α : F) (c : Quartic F)
    (hα : IsNonsquare α) (hF : ringChar F ≠ 2) (p : Param F) :
    ((identityPlanes α c).filter (fun E => point α c p ∈ E.val)).card =
      Fintype.card F * (Fintype.card F + 1) := by
  classical
  letI := Fintype.ofFinite (Plane F)
  have h := card_identity_planes_through_point α c hα hF p
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
  simpa [identityPlanes, Finset.filter_filter] using h

/-- Remark 5 for the actual quartic point set and its actual identity planes. -/
theorem point_deletion_obstruction [Fintype F] (α : F) (c : Quartic F)
    (hα : IsNonsquare α) (hF : ringChar F ≠ 2) (X : Finset (Param F))
    (hX : ∀ E : Plane F, IdentityExceptional α c E →
      (X ∩ planeSection α c E).card ≤ 4) :
    X.card ≤ 4 * Fintype.card F ^ 2 := by
  classical
  letI := Fintype.ofFinite (Plane F)
  let I := {E : Plane F // IdentityExceptional α c E}
  letI := Fintype.ofFinite I
  have hr (p : Param F) :
      (Finset.univ.filter fun E : I => p ∈ planeSection α c E.val).card =
        Fintype.card F * (Fintype.card F + 1) := by
    simp only [mem_section]
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    rw [Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
      (IdentityExceptional α c) (fun E => point α c p ∈ E.val))]
    exact card_identity_planes_through_point α c hα hF p
  have hbound := incidence_double_count X (fun E : I => planeSection α c E.val)
    (Fintype.card F * (Fintype.card F + 1)) 4 (fun p _ => hr p)
    (fun E => by simpa only [Finset.inter_comm] using hX E.val E.property)
  have hcard : (Finset.univ : Finset I).card =
      Fintype.card F ^ 3 * (Fintype.card F + 1) := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact card_identity_planes α c hα hF
  rw [hcard] at hbound
  have hh : X.card * (Fintype.card F * (Fintype.card F + 1)) ≤
      (4 * Fintype.card F ^ 2) * (Fintype.card F * (Fintype.card F + 1)) := by
    convert hbound using 1 <;> ring
  exact Nat.le_of_mul_le_mul_right hh (by positivity)

end
end K44K35Free.Geometry
