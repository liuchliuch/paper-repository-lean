import Paper17.Delzant

/-! Independence of the normal fan from a finite vertex presentation. -/
noncomputable section
open scoped BigOperators
namespace Paper17

/-- A fixed positive coefficient in a convex presentation of a point produces
a vertex whose normal cone contains the normal cone at that point. -/
theorem exists_vertex_normalCone_superset {n : ℕ} (P : Polytope n) {v : V n}
    (hv : v ∈ P.carrier) :
    ∃ q ∈ P.verts, (normalConeAt P v : Set (V n)) ⊆ normalConeAt P q := by
  classical
  obtain ⟨w, hw, hsum, hcomb⟩ := Finset.mem_convexHull.mp hv
  have hsumv : ∑ p ∈ P.verts, w p • p = v := by
    simpa only [Finset.centerMass, hsum, inv_one, one_smul, id_eq] using hcomb
  have hpos : ∃ q ∈ P.verts, 0 < w q := by
    by_contra! hn
    have hz : ∀ q ∈ P.verts, w q = 0 := fun q hq => le_antisymm (hn q hq) (hw q hq)
    have : ∑ q ∈ P.verts, w q = 0 := Finset.sum_eq_zero hz
    linarith
  obtain ⟨q, hq, hwq⟩ := hpos
  refine ⟨q, hq, ?_⟩
  intro u hu
  have hle : ∀ p ∈ P.verts, dot u p ≤ dot u v := fun p hp =>
    hu p (subset_convexHull ℝ _ hp)
  let f : V n →ₗ[ℝ] ℝ :=
    { toFun := dot u
      map_add' := dot_add_right u
      map_smul' := fun t x => dot_smul_right t u x }
  have hdot : ∑ p ∈ P.verts, w p * dot u p = dot u v := by
    have hh := congrArg f hsumv
    simpa only [map_sum, map_smul, smul_eq_mul, f, LinearMap.coe_mk, AddHom.coe_mk] using hh
  have hzero : ∑ p ∈ P.verts, w p * (dot u v - dot u p) = 0 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul, hdot, sub_self]
  have hqzero : w q * (dot u v - dot u q) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun p hp => mul_nonneg (hw p hp) (sub_nonneg.mpr (hle p hp)))).mp hzero q hq
  have hval : dot u v = dot u q :=
    sub_eq_zero.mp ((mul_eq_zero.mp hqzero).resolve_left hwq.ne')
  intro y hy
  rw [← hval]
  exact hu y hy

/-- Mutual refinement follows from equality of carriers, even with redundant vertices. -/
theorem normalFan_equiv_of_carrier_eq {n : ℕ} {P Q : Polytope n}
    (h : P.carrier = Q.carrier) : Fan.Equivalent (NormalFan P) (NormalFan Q) := by
  classical
  have haux : ∀ A B : Polytope n, A.carrier = B.carrier → (NormalFan A).refines (NormalFan B) := by
    intro A B hab K hK
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hK
    have hvB : v ∈ B.carrier := hab ▸ subset_convexHull ℝ _ hv
    obtain ⟨q, hq, hqcone⟩ := exists_vertex_normalCone_superset B hvB
    refine ⟨normalConeAt B q, Finset.mem_image.mpr ⟨q, hq, rfl⟩, ?_⟩
    intro u hu
    apply hqcone
    intro y hy
    exact hu y (hab.symm ▸ hy)
  exact ⟨haux P Q h, haux Q P h.symm⟩

end Paper17
