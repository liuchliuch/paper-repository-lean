import Verification.Example24Hexagon

/-! The complete five-ray geometric normal fan of the actual planar sum. -/
noncomputable section
open scoped BigOperators Topology Pointwise
namespace Paper17.Example24

@[simp] theorem vec2_add (a b c d : ℝ) : vec2 a b + vec2 c d = vec2 (a + c) (b + d) := by
  ext i
  fin_cases i <;> rfl

def pentagonVertex : Fin 5 → V 2
  | 0 => vec2 1 0
  | 1 => vec2 1 1
  | 2 => vec2 0 2
  | 3 => vec2 (-1) 1
  | 4 => vec2 (-1) 0

def pentagon : Polytope 2 where
  verts := {vec2 1 0, vec2 1 1, vec2 0 2, vec2 (-1) 1, vec2 (-1) 0}
  nonempty_verts' := ⟨vec2 1 0, by simp⟩

theorem pentagonVertex_mem (i : Fin 5) : pentagonVertex i ∈ pentagon.verts := by
  fin_cases i <;> simp [pentagonVertex, pentagon]

theorem pentagon_verts_enumerated {v : V 2} (hv : v ∈ pentagon.verts) :
    ∃ i, pentagonVertex i = v := by
  simp only [pentagon, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩

/-- The actual Minkowski sum, including its redundant original listed points,
is exactly the five-vertex source pentagon. -/
theorem triangle_sum_carrier_pentagon :
    ((triangle 1).add (triangle (-1))).carrier = pentagon.carrier := by
  classical
  have hvertices : ∀ i : Fin 5, pentagonVertex i ∈ pentagon.carrier :=
    fun i => subset_convexHull ℝ _ (pentagonVertex_mem i)
  have hzero : vec2 0 0 ∈ pentagon.carrier := by
    have hh := pentagon.convex (hvertices 4) (hvertices 0)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    convert hh using 1 <;> ext i <;> fin_cases i <;> norm_num [pentagonVertex, vec2]
  have hmid : vec2 0 1 ∈ pentagon.carrier := by
    have hh := pentagon.convex (hvertices 3) (hvertices 1)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    convert hh using 1 <;> ext i <;> fin_cases i <;> norm_num [pentagonVertex, vec2]
  apply Set.Subset.antisymm
  · apply convexHull_min _ pentagon.convex
    intro x hx
    obtain ⟨⟨p, q⟩, hpq, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hp, hq⟩ := Finset.mem_product.mp hpq
    simp only [triangle, Finset.mem_insert, Finset.mem_singleton, Int.cast_one,
      Int.cast_neg] at hp hq
    rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
    all_goals
      norm_num only [vec2_add]
      first | exact hzero | exact hmid | exact hvertices 0 | exact hvertices 1 |
        exact hvertices 2 | exact hvertices 3 | exact hvertices 4
  · apply convexHull_min _ ((triangle 1).add (triangle (-1))).convex
    intro x hx
    obtain ⟨i, rfl⟩ := pentagon_verts_enumerated hx
    rw [carrier_add_eq]
    have hh : ∀ p ∈ (triangle 1).verts, ∀ q ∈ (triangle (-1)).verts,
        p + q ∈ (triangle 1).carrier + (triangle (-1)).carrier :=
      fun p hp q hq => Set.add_mem_add (subset_convexHull ℝ _ hp) (subset_convexHull ℝ _ hq)
    fin_cases i
    · simpa only [pentagonVertex, Matrix.cons_val_zero, vec2_add, add_zero] using
        hh (vec2 1 0) (by simp [triangle]) (vec2 0 0) (by simp [triangle])
    · simpa [pentagonVertex, vec2_add, one_add_one_eq_two] using
        hh (vec2 1 0) (by simp [triangle]) (vec2 0 1) (by simp [triangle])
    · simpa [pentagonVertex, vec2_add, one_add_one_eq_two] using
        hh (vec2 0 1) (by simp [triangle]) (vec2 0 1) (by simp [triangle])
    · simpa [pentagonVertex, vec2_add, one_add_one_eq_two] using
        hh (vec2 0 1) (by simp [triangle]) (vec2 (-1) 0) (by simp [triangle])
    · simpa [pentagonVertex, vec2_add, one_add_one_eq_two] using
        hh (vec2 0 0) (by simp [triangle]) (vec2 (-1) 0) (by simp [triangle])

def pentagonBasis : Fin 5 → Fin 2 → V 2 :=
  ![![raysSum 4, raysSum 0], ![raysSum 0, raysSum 1], ![raysSum 1, raysSum 2],
    ![raysSum 2, raysSum 3], ![raysSum 3, raysSum 4]]

def pentagonCoefficients (i : Fin 5) (u : V 2) : V 2 :=
  match i with
  | 0 => ![-u 1, u 0]
  | 1 => ![u 0 - u 1, u 1]
  | 2 => ![(u 0 + u 1) / 2, (-u 0 + u 1) / 2]
  | 3 => ![u 1, -u 0 - u 1]
  | 4 => ![-u 0, -u 1]

theorem pentagonBasis_normal (i : Fin 5) (j : Fin 2) :
    pentagonBasis i j ∈ normalConeAt pentagon (pentagonVertex i) := by
  rw [mem_normalConeAt_iff_vertices]
  intro w hw
  simp only [pentagon, Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [pentagonBasis, pentagonVertex, raysSum, vec2, dot, Fin.sum_univ_two]

/-- All five consecutive pairs in the stated ray list generate the actual
maximal normal cones of the sum, including its nonsmooth upper cone. -/
theorem pentagon_normalCone (i : Fin 5) :
    (normalConeAt pentagon (pentagonVertex i) : Set (V 2)) =
      {u | ∃ c : Fin 2 → ℝ, (∀ j, 0 ≤ c j) ∧ u = ∑ j, c j • pentagonBasis i j} := by
  ext u
  constructor
  · intro hu
    have h0 := hu (pentagonVertex 0) (subset_convexHull ℝ _ (pentagonVertex_mem 0))
    have h1 := hu (pentagonVertex 1) (subset_convexHull ℝ _ (pentagonVertex_mem 1))
    have h2 := hu (pentagonVertex 2) (subset_convexHull ℝ _ (pentagonVertex_mem 2))
    have h3 := hu (pentagonVertex 3) (subset_convexHull ℝ _ (pentagonVertex_mem 3))
    have h4 := hu (pentagonVertex 4) (subset_convexHull ℝ _ (pentagonVertex_mem 4))
    refine ⟨pentagonCoefficients i u, ?_, ?_⟩
    · intro j
      fin_cases i <;> fin_cases j <;>
        simp [pentagonCoefficients, pentagonVertex, vec2, dot, Fin.sum_univ_two] at h0 h1 h2 h3 h4 ⊢ <;>
        linarith
    · ext j
      fin_cases i <;> fin_cases j <;>
        simp [pentagonCoefficients, pentagonBasis, raysSum, vec2, Fin.sum_univ_two] <;> ring
  · rintro ⟨c, hc, rfl⟩ y hy
    rw [dot_fintype_sum_smul, dot_fintype_sum_smul]
    exact Finset.sum_le_sum (fun j _ =>
      mul_le_mul_of_nonneg_left (pentagonBasis_normal i j y hy) (hc j))

/-- The five-ray description is exhaustive up to the carrier-independent
normal-fan equivalence, even though the original sum lists redundant points. -/
theorem triangle_sum_five_ray_fan :
    Fan.Equivalent (NormalFan ((triangle 1).add (triangle (-1)))) (NormalFan pentagon) ∧
      ∀ i, (normalConeAt ((triangle 1).add (triangle (-1))) (pentagonVertex i) : Set (V 2)) =
        {u | ∃ c : Fin 2 → ℝ, (∀ j, 0 ≤ c j) ∧ u = ∑ j, c j • pentagonBasis i j} := by
  refine ⟨normalFan_equiv_of_carrier_eq triangle_sum_carrier_pentagon, ?_⟩
  intro i
  rw [← pentagon_normalCone]
  ext u
  change (∀ y ∈ ((triangle 1).add (triangle (-1))).carrier, dot u y ≤ dot u (pentagonVertex i)) ↔
    (∀ y ∈ pentagon.carrier, dot u y ≤ dot u (pentagonVertex i))
  rw [triangle_sum_carrier_pentagon]

end Paper17.Example24
