import Verification.Example24Hexagon

/-! Actual product carriers and normal cones of the three-dimensional prisms. -/
noncomputable section
open scoped BigOperators Topology
namespace Paper17.Example24

def planeProjection (x : V 3) : V 2 := ![x 0, x 1]

@[simp] theorem planeProjection_prismPoint (p : V 2) (z : ℝ) :
    planeProjection (prismPoint p z) = p := by
  ext i
  fin_cases i <;> rfl

@[simp] theorem prismPoint_projection (x : V 3) :
    prismPoint (planeProjection x) (x 2) = x := by
  ext i
  fin_cases i <;> rfl

theorem continuous_planeProjection : Continuous planeProjection := by
  apply continuous_pi
  intro i
  fin_cases i <;> exact continuous_apply _

theorem continuous_prismPoint_fixed (z : ℝ) : Continuous (fun p : V 2 => prismPoint p z) := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_apply 0
  · exact continuous_apply 1
  · exact continuous_const

theorem dot_prismPoint (u : V 3) (p : V 2) (z : ℝ) :
    dot u (prismPoint p z) = dot (planeProjection u) p + u 2 * z := by
  simp [dot, prismPoint, planeProjection, Fin.sum_univ_succ]
  ring

/-- The finite vertex construction is precisely the actual product with the
interval, for every positive height. -/
theorem mem_prism_carrier (P : Polytope 2) {a : ℝ} (ha : 0 < a) (x : V 3) :
    x ∈ (prism P a).carrier ↔ planeProjection x ∈ P.carrier ∧ 0 ≤ x 2 ∧ x 2 ≤ a := by
  classical
  have hslice : ∀ z ∈ ({0, a} : Finset ℝ), ∀ p ∈ P.carrier,
      prismPoint p z ∈ (prism P a).carrier := by
    intro z hz
    have hc : Convex ℝ {p : V 2 | prismPoint p z ∈ (prism P a).carrier} := by
      rw [convex_iff_add_mem]
      intro p hp q hq α β hα hβ hab
      have heq : prismPoint (α • p + β • q) z =
          α • prismPoint p z + β • prismPoint q z := by
        ext i
        fin_cases i <;> simp [prismPoint]
        rw [← add_mul, hab, one_mul]
      change prismPoint (α • p + β • q) z ∈ (prism P a).carrier
      rw [heq]
      exact (prism P a).convex hp hq hα hβ hab
    apply convexHull_min _ hc
    intro p hp
    apply subset_convexHull ℝ _
    exact Finset.mem_image.mpr ⟨(p, z), Finset.mem_product.mpr ⟨hp, hz⟩, rfl⟩
  constructor
  · intro hx
    have hc : Convex ℝ {x : V 3 | planeProjection x ∈ P.carrier ∧ 0 ≤ x 2 ∧ x 2 ≤ a} := by
      rw [convex_iff_add_mem]
      intro y hy z hz α β hα hβ hab
      have hp : planeProjection (α • y + β • z) =
          α • planeProjection y + β • planeProjection z := by
        ext i
        fin_cases i <;> rfl
      refine ⟨?_, ?_, ?_⟩
      · rw [hp]
        exact P.convex hy.1 hz.1 hα hβ hab
      · change 0 ≤ α * y 2 + β * z 2
        exact add_nonneg (mul_nonneg hα hy.2.1) (mul_nonneg hβ hz.2.1)
      · change α * y 2 + β * z 2 ≤ a
        calc α * y 2 + β * z 2 ≤ α * a + β * a :=
            add_le_add (mul_le_mul_of_nonneg_left hy.2.2 hα) (mul_le_mul_of_nonneg_left hz.2.2 hβ)
          _ = a := by rw [← add_mul, hab, one_mul]
    apply convexHull_min _ hc hx
    intro y hy
    obtain ⟨⟨p, z⟩, hpz, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hp, hz⟩ := Finset.mem_product.mp hpz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    change planeProjection (prismPoint p z) ∈ P.carrier ∧ 0 ≤ z ∧ z ≤ a
    rw [planeProjection_prismPoint]
    refine ⟨subset_convexHull ℝ _ hp, ?_, ?_⟩
    · rcases hz with rfl | rfl <;> simp [prismPoint, ha.le]
    · rcases hz with rfl | rfl <;> simp [prismPoint, ha.le]
  · rintro ⟨hp, hz0, hza⟩
    have h0 := hslice 0 (by simp) (planeProjection x) hp
    have h1 := hslice a (by simp) (planeProjection x) hp
    have hw : 0 ≤ 1 - x 2 / a := sub_nonneg.mpr ((div_le_one ha).mpr hza)
    have hz : 0 ≤ x 2 / a := div_nonneg hz0 ha.le
    have hh := (prism P a).convex h0 h1 hw hz (by ring : 1 - x 2 / a + x 2 / a = 1)
    have heq : (1 - x 2 / a) • prismPoint (planeProjection x) 0 +
        (x 2 / a) • prismPoint (planeProjection x) a = x := by
      ext i
      fin_cases i <;> simp [prismPoint, planeProjection]
      · ring
      · ring
      · exact div_mul_cancel₀ _ ha.ne'
    exact heq ▸ hh

/-- Nonempty planar interior times a nonempty open interval gives actual
three-dimensional interior. -/
theorem prism_fullDim (P : Polytope 2) (hP : P.IsFullDim) {a : ℝ} (ha : 0 < a) :
    (prism P a).IsFullDim := by
  obtain ⟨p, hp⟩ := hP
  let U : Set (V 3) := {x | planeProjection x ∈ interior P.carrier ∧ 0 < x 2 ∧ x 2 < a}
  have ho : IsOpen U := (isOpen_interior.preimage continuous_planeProjection).inter
    ((isOpen_lt continuous_const (continuous_apply 2)).inter
      (isOpen_lt (continuous_apply 2) continuous_const))
  have hs : U ⊆ (prism P a).carrier := by
    intro x hx
    exact (mem_prism_carrier P ha x).mpr ⟨interior_subset hx.1, hx.2.1.le, hx.2.2.le⟩
  refine ⟨prismPoint p (a / 2), interior_maximal hs ho ?_⟩
  change planeProjection (prismPoint p (a / 2)) ∈ interior P.carrier ∧
    0 < a / 2 ∧ a / 2 < a
  rw [planeProjection_prismPoint]
  exact ⟨hp, by linarith, by linarith⟩

/-- The actual endpoint normal cone is the planar normal cone times the
appropriate vertical half-line. -/
theorem normal_prism_endpoint (P : Polytope 2) {a : ℝ} (ha : 0 < a)
    {p : V 2} (hp : p ∈ P.verts) (b : Bool) (u : V 3) :
    u ∈ normalConeAt (prism P a) (prismPoint p (if b then a else 0)) ↔
      planeProjection u ∈ normalConeAt P p ∧ (if b then 0 ≤ u 2 else u 2 ≤ 0) := by
  have hv : ∀ q ∈ P.verts, ∀ z ∈ ({0, a} : Finset ℝ),
      prismPoint q z ∈ (prism P a).carrier := by
    intro q hq z hz
    apply subset_convexHull ℝ _
    exact Finset.mem_image.mpr ⟨(q, z), Finset.mem_product.mpr ⟨hq, hz⟩, rfl⟩
  constructor
  · intro hu
    have h0 := hu (prismPoint p 0) (hv p hp 0 (by simp))
    have h1 := hu (prismPoint p a) (hv p hp a (by simp))
    rw [dot_prismPoint, dot_prismPoint] at h0 h1
    refine ⟨?_, ?_⟩
    · apply (mem_normalConeAt_iff_vertices P _ _).mpr
      intro q hq
      have hq' := hu (prismPoint q (if b then a else 0)) (hv q hq _ (by cases b <;> simp))
      rw [dot_prismPoint, dot_prismPoint] at hq'
      linarith
    · cases b <;> simp only [Bool.false_eq_true, if_false, if_true] at h0 h1 ⊢ <;> nlinarith
  · rintro ⟨hu, hz⟩
    apply (mem_normalConeAt_iff_vertices _ _ _).mpr
    intro w hw
    obtain ⟨⟨q, z⟩, hqz, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hq, hzmem⟩ := Finset.mem_product.mp hqz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzmem
    rw [dot_prismPoint, dot_prismPoint]
    have hq' := hu q (subset_convexHull ℝ _ hq)
    cases b <;> simp only [Bool.false_eq_true, if_false, if_true] at hz ⊢ <;>
      rcases hzmem with rfl | rfl <;> nlinarith

end Paper17.Example24
