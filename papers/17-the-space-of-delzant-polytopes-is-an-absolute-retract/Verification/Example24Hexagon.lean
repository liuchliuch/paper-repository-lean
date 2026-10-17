import Verification.Example24Radius

/-! The actual hexagon and its six unimodular normal cones. -/
noncomputable section
open scoped BigOperators Topology
namespace Paper17.Example24

def hexagonVertex : Fin 6 → V 2 :=
  ![vec2 2 (-2), vec2 2 1, vec2 1 2, vec2 (-1) 2, vec2 (-2) 1, vec2 (-2) (-2)]

def hexagonBasis : Fin 6 → Fin 2 → V 2 :=
  ![![raysT 5, raysT 0], ![raysT 0, raysT 1], ![raysT 1, raysT 2],
    ![raysT 2, raysT 3], ![raysT 3, raysT 4], ![raysT 4, raysT 5]]

def hexagonCoefficients (i : Fin 6) (u : V 2) : V 2 :=
  match i with
  | 0 => ![-u 1, u 0]
  | 1 => ![u 0 - u 1, u 1]
  | 2 => ![u 0, u 1 - u 0]
  | 3 => ![u 0 + u 1, -u 0]
  | 4 => ![u 1, -u 0 - u 1]
  | 5 => ![-u 0, -u 1]

theorem hexagonVertex_mem (i : Fin 6) : hexagonVertex i ∈ hexagon.verts := by
  fin_cases i <;> simp [hexagonVertex, hexagon, Tverts]

theorem hexagonBasis_normal (i : Fin 6) (j : Fin 2) :
    hexagonBasis i j ∈ normalConeAt hexagon (hexagonVertex i) := by
  rw [mem_normalConeAt_iff_vertices]
  intro w hw
  change w ∈ Tverts at hw
  simp only [Tverts, Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [hexagonBasis, hexagonVertex, raysT, vec2, dot, Fin.sum_univ_two]

/-- These are the actual geometric vertex normal cones, with precisely the
six source rays as consecutive generators. -/
theorem hexagon_normalCone (i : Fin 6) :
    (normalConeAt hexagon (hexagonVertex i) : Set (V 2)) =
      {u | ∃ c : Fin 2 → ℝ, (∀ j, 0 ≤ c j) ∧ u = ∑ j, c j • hexagonBasis i j} := by
  ext u
  constructor
  · intro hu
    have h0 := hu (hexagonVertex 0) (subset_convexHull ℝ _ (hexagonVertex_mem 0))
    have h1 := hu (hexagonVertex 1) (subset_convexHull ℝ _ (hexagonVertex_mem 1))
    have h2 := hu (hexagonVertex 2) (subset_convexHull ℝ _ (hexagonVertex_mem 2))
    have h3 := hu (hexagonVertex 3) (subset_convexHull ℝ _ (hexagonVertex_mem 3))
    have h4 := hu (hexagonVertex 4) (subset_convexHull ℝ _ (hexagonVertex_mem 4))
    have h5 := hu (hexagonVertex 5) (subset_convexHull ℝ _ (hexagonVertex_mem 5))
    refine ⟨hexagonCoefficients i u, ?_, ?_⟩
    · intro j
      fin_cases i <;> fin_cases j <;>
        simp [hexagonCoefficients, hexagonVertex, vec2, dot, Fin.sum_univ_two] at h0 h1 h2 h3 h4 h5 ⊢ <;>
        linarith
    · ext j
      fin_cases i <;> fin_cases j <;>
        simp [hexagonCoefficients, hexagonBasis, raysT, vec2, Fin.sum_univ_two] <;> ring
  · rintro ⟨c, hc, rfl⟩ y hy
    rw [dot_fintype_sum_smul, dot_fintype_sum_smul]
    exact Finset.sum_le_sum (fun j _ =>
      mul_le_mul_of_nonneg_left (hexagonBasis_normal i j y hy) (hc j))

theorem hexagon_cones_smooth (i : Fin 6) :
    Fan.IsSmoothCone (normalConeAt hexagon (hexagonVertex i)) := by
  refine ⟨hexagonBasis i, ?_, ?_, hexagon_normalCone i⟩
  · intro j k
    refine ⟨⌊hexagonBasis i j k⌋, ?_⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      norm_num [hexagonBasis, raysT, vec2]
  · fin_cases i <;> norm_num [hexagonBasis, raysT, vec2, Matrix.det_fin_two]

/-- A nonempty open affine triangle of the listed vertices lies in the
hexagon, so this is a genuinely full-dimensional polygon. -/
theorem hexagon_fullDim : hexagon.IsFullDim := by
  let a : V 2 → ℝ := fun x => (x 1 + 4 * x 0 - 6) / 3
  let b : V 2 → ℝ := fun x => 2 - x 0
  let U : Set (V 2) := {x | 0 < a x ∧ 0 < b x ∧ a x + b x < 1}
  have ha : Continuous a := by fun_prop
  have hb : Continuous b := by fun_prop
  have ho : IsOpen U := (isOpen_lt continuous_const ha).inter
    ((isOpen_lt continuous_const hb).inter (isOpen_lt (ha.add hb) continuous_const))
  have hs : U ⊆ hexagon.carrier := by
    intro x hx
    let w : Fin 3 → ℝ := ![1 - a x - b x, a x, b x]
    let z : Fin 3 → V 2 := ![hexagonVertex 0, hexagonVertex 1, hexagonVertex 2]
    apply mem_convexHull_of_exists_fintype w z
    · intro j
      fin_cases j <;> simp [w] <;> linarith [hx.1, hx.2.1, hx.2.2]
    · simp [w, Fin.sum_univ_succ]
    · intro j
      fin_cases j
      · simpa [z] using hexagonVertex_mem 0
      · simpa [z] using hexagonVertex_mem 1
      · simpa [z] using hexagonVertex_mem 2
    · ext j
      fin_cases j <;> simp [w, z, hexagonVertex, vec2, a, b, Fin.sum_univ_succ] <;> ring
  refine ⟨vec2 (5 / 3) (1 / 3), interior_maximal hs ho ?_⟩
  norm_num [U, a, b, vec2]

/-- The stated hexagon is an actual Delzant polytope. -/
theorem hexagon_isDelzant : IsDelzant hexagon := by
  classical
  refine ⟨hexagon_fullDim, ?_⟩
  intro C hC hi
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hC
  have he : ∃ i, hexagonVertex i = v := by
    change v ∈ Tverts at hv
    simp only [Tverts, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  obtain ⟨i, rfl⟩ := he
  exact hexagon_cones_smooth i

/-- All listed vertices occur in the explicit cyclic enumeration. -/
theorem hexagon_verts_enumerated {v : V 2} (hv : v ∈ hexagon.verts) :
    ∃ i, hexagonVertex i = v := by
  change v ∈ Tverts at hv
  simp only [Tverts, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩
  · exact ⟨5, rfl⟩

def hexagonRayIndex : Fin 6 → Fin 2 → Fin 6 :=
  ![![5, 0], ![0, 1], ![1, 2], ![2, 3], ![3, 4], ![4, 5]]

theorem hexagonBasis_eq_ray (i : Fin 6) (j : Fin 2) :
    hexagonBasis i j = raysT (hexagonRayIndex i j) := by
  fin_cases i <;> fin_cases j <;> rfl

def hexagonHeights : Fin 6 → ℝ
  | 0 => 2
  | 1 => 3
  | 2 => 2
  | 3 => 3
  | 4 => 2
  | 5 => 2

theorem hexagon_support_rays (i : Fin 6) :
    supportFunction hexagon.carrier (raysT i) = hexagonHeights i := by
  have hb : hexagonBasis i 1 = raysT i := by fin_cases i <;> rfl
  have hn : raysT i ∈ normalConeAt hexagon (hexagonVertex i) :=
    hb ▸ hexagonBasis_normal i 1
  rw [supportFunction_eq_of_normal hexagon
    (subset_convexHull ℝ _ (hexagonVertex_mem i)) hn]
  fin_cases i <;> norm_num [hexagonHeights, raysT, hexagonVertex, vec2, dot, Fin.sum_univ_two]

/-- The six displayed outward rays give the whole actual carrier. -/
theorem hexagon_eq_supporting_halfspaces :
    hexagon.carrier = {x | ∀ i, dot (raysT i) x ≤ supportFunction hexagon.carrier (raysT i)} := by
  apply Set.Subset.antisymm
  · intro x hx i
    exact supportFunction_ub hexagon.isCompact hx
  · apply subset_of_forall_dot_le_supportFunction hexagon.isCompact hexagon.nonempty hexagon.convex
    intro u x hx
    obtain ⟨v, hv, hmax⟩ := exists_mem_verts_isMaxOn hexagon u
    obtain ⟨i, rfl⟩ := hexagon_verts_enumerated hv
    have hu : u ∈ (normalConeAt hexagon (hexagonVertex i) : Set (V 2)) := hmax
    rw [hexagon_normalCone] at hu
    obtain ⟨c, hc, hu⟩ := hu
    have hh : ∀ j, supportFunction hexagon.carrier (hexagonBasis i j) =
        dot (hexagonBasis i j) (hexagonVertex i) := fun j =>
      supportFunction_eq_of_normal hexagon (subset_convexHull ℝ _ (hexagonVertex_mem i))
        (hexagonBasis_normal i j)
    calc dot u x = ∑ j, c j * dot (hexagonBasis i j) x := by rw [hu, dot_fintype_sum_smul]
      _ ≤ ∑ j, c j * supportFunction hexagon.carrier (hexagonBasis i j) := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (by rw [hexagonBasis_eq_ray]; exact hx _) (hc j)
      _ = ∑ j, c j * dot (hexagonBasis i j) (hexagonVertex i) := by simp_rw [hh]
      _ = dot u (hexagonVertex i) := by rw [hu, dot_fintype_sum_smul]
      _ ≤ supportFunction hexagon.carrier u :=
        supportFunction_ub hexagon.isCompact (subset_convexHull ℝ _ (hexagonVertex_mem i))

/-- The exact H-description stated in the source. -/
theorem mem_hexagon_iff (x : V 2) : x ∈ hexagon.carrier ↔
    -2 ≤ x 0 ∧ x 0 ≤ 2 ∧ -2 ≤ x 1 ∧ x 1 ≤ 2 ∧ x 0 + x 1 ≤ 3 ∧ -x 0 + x 1 ≤ 3 := by
  rw [hexagon_eq_supporting_halfspaces]
  simp only [Set.mem_setOf_eq, hexagon_support_rays]
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    have h4 := h 4
    have h5 := h 5
    norm_num [raysT, hexagonHeights, vec2, dot, Fin.sum_univ_two] at h0 h1 h2 h3 h4 h5
    exact ⟨by linarith, h0, by linarith, h2, h1, by linarith⟩
  · rintro ⟨hxl, hxu, hyl, hyu, hd1, hd2⟩ i
    fin_cases i <;> norm_num [raysT, hexagonHeights, vec2, dot, Fin.sum_univ_two] <;> linarith

def hexagonTargetA : Fin 6 → V 2 :=
  ![vec2 1 0, vec2 1 0, vec2 0 1, vec2 0 1, vec2 0 1, vec2 0 0]
def hexagonTargetB : Fin 6 → V 2 :=
  ![vec2 0 0, vec2 0 1, vec2 0 1, vec2 0 1, vec2 (-1) 0, vec2 (-1) 0]

private theorem hexagon_refines_triangle_of_rays (s : ℤ) (p : Fin 6 → V 2)
    (hp : ∀ i, p i ∈ (triangle s).verts)
    (hn : ∀ i j, hexagonBasis i j ∈ normalConeAt (triangle s) (p i)) :
    (NormalFan hexagon).refines (NormalFan (triangle s)) := by
  classical
  intro C hC
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hC
  obtain ⟨i, rfl⟩ := hexagon_verts_enumerated hv
  refine ⟨normalConeAt (triangle s) (p i), Finset.mem_image.mpr ⟨p i, hp i, rfl⟩, ?_⟩
  intro u hu y hy
  change u ∈ (normalConeAt hexagon (hexagonVertex i) : Set (V 2)) at hu
  rw [hexagon_normalCone] at hu
  obtain ⟨c, hc, rfl⟩ := hu
  rw [dot_fintype_sum_smul, dot_fintype_sum_smul]
  exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hn i j y hy) (hc j))

/-- The six-ray smooth fan actually refines both source triangle fans. -/
theorem hexagon_refines_triangles :
    (NormalFan hexagon).refines (NormalFan (triangle 1)) ∧
      (NormalFan hexagon).refines (NormalFan (triangle (-1))) := by
  constructor
  · apply hexagon_refines_triangle_of_rays 1 hexagonTargetA
    · intro i
      fin_cases i <;> simp [hexagonTargetA, triangle]
    · intro i j
      rw [mem_normalConeAt_iff_vertices]
      intro w hw
      simp only [triangle, Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl <;> fin_cases i <;> fin_cases j <;>
        norm_num [hexagonBasis, hexagonTargetA, raysT, vec2, dot, Fin.sum_univ_two]
  · apply hexagon_refines_triangle_of_rays (-1) hexagonTargetB
    · intro i
      fin_cases i <;> simp [hexagonTargetB, triangle]
    · intro i j
      rw [mem_normalConeAt_iff_vertices]
      intro w hw
      simp only [triangle, Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl <;> fin_cases i <;> fin_cases j <;>
        norm_num [hexagonBasis, hexagonTargetB, raysT, vec2, dot, Fin.sum_univ_two]

end Paper17.Example24
