import Paper17.Example24
import Paper17.ChainGeometry
import Mathlib.LinearAlgebra.Matrix.Determinant.Misc

/-! Actual normal cones and smoothness for the triangles in Example 2.4. -/
noncomputable section
open scoped BigOperators Pointwise Topology
namespace Paper17

/-- Testing a geometric normal cone at a finite set of generators suffices. -/
theorem mem_normalConeAt_iff_vertices {n : ℕ} (P : Polytope n) (u v : V n) :
    u ∈ normalConeAt P v ↔ ∀ w ∈ P.verts, dot u w ≤ dot u v := by
  constructor
  · intro h w hw
    exact h w (subset_convexHull ℝ _ hw)
  · intro h
    have hc : Convex ℝ {w : V n | dot u w ≤ dot u v} := by
      rw [convex_iff_add_mem]
      intro x hx y hy a b ha hb hab
      change dot u (a • x + b • y) ≤ dot u v
      rw [dot_add_right, dot_smul_right, dot_smul_right]
      have hax := mul_le_mul_of_nonneg_left hx ha
      have hby := mul_le_mul_of_nonneg_left hy hb
      calc a * dot u x + b * dot u y ≤ a * dot u v + b * dot u v := add_le_add hax hby
        _ = dot u v := by rw [← add_mul, hab, one_mul]
    exact convexHull_min h hc

/-- Smoothness of a full-dimensional normal cone does not depend on whether
the chosen finite presentation lists its vertex. -/
theorem normalConeAt_isSmooth_of_fan {n : ℕ} (P : Polytope n)
    (hP : (NormalFan P).IsSmooth) {v : V n} (hv : v ∈ P.carrier)
    (hi : (interior (normalConeAt P v : Set (V n))).Nonempty) :
    Fan.IsSmoothCone (normalConeAt P v) := by
  classical
  obtain ⟨q, hq, hsub⟩ := exists_vertex_normalCone_superset P hv
  have heq := eq_of_normalCone_interior_subset P hv (subset_convexHull ℝ _ hq) hi hsub
  subst q
  exact hP _ (Finset.mem_image.mpr ⟨v, hq, rfl⟩) hi

namespace Example24

/-- The two triangles are the cases `s = 1` and `s = -1`. -/
def triangle (s : ℤ) : Polytope 2 where
  verts := {vec2 0 0, vec2 s 0, vec2 0 1}
  nonempty_verts' := by simp

@[simp] theorem dot_vec2 (u : V 2) (a b : ℝ) : dot u (vec2 a b) = u 0 * a + u 1 * b := by
  simp [dot, vec2, Fin.sum_univ_two]

theorem normal_triangle_zero (s : ℤ) (u : V 2) :
    u ∈ normalConeAt (triangle s) (vec2 0 0) ↔ (s : ℝ) * u 0 ≤ 0 ∧ u 1 ≤ 0 := by
  rw [mem_normalConeAt_iff_vertices]
  simp [triangle, vec2, mul_comm]

theorem normal_triangle_side (s : ℤ) (u : V 2) :
    u ∈ normalConeAt (triangle s) (vec2 s 0) ↔ 0 ≤ (s : ℝ) * u 0 ∧ u 1 ≤ (s : ℝ) * u 0 := by
  rw [mem_normalConeAt_iff_vertices]
  simp [triangle, vec2, mul_comm]

theorem normal_triangle_top (s : ℤ) (u : V 2) :
    u ∈ normalConeAt (triangle s) (vec2 0 1) ↔ 0 ≤ u 1 ∧ (s : ℝ) * u 0 ≤ u 1 := by
  rw [mem_normalConeAt_iff_vertices]
  simp [triangle, vec2, mul_comm]

theorem triangle_fullDim (s : ℤ) (hs : s = 1 ∨ s = -1) : (triangle s).IsFullDim := by
  have hs2 : (s : ℝ) * (s : ℝ) = 1 := by rcases hs with rfl | rfl <;> norm_num
  let U : Set (V 2) := {x | 0 < (s : ℝ) * x 0 ∧ 0 < x 1 ∧ (s : ℝ) * x 0 + x 1 < 1}
  have hUopen : IsOpen U := (isOpen_lt continuous_const
    (continuous_const.mul (continuous_apply 0))).inter
      ((isOpen_lt continuous_const (continuous_apply 1)).inter
        (isOpen_lt ((continuous_const.mul (continuous_apply 0)).add (continuous_apply 1)) continuous_const))
  have hUsub : U ⊆ (triangle s).carrier := by
    intro x hx
    let w : Fin 3 → ℝ := ![1 - (s : ℝ) * x 0 - x 1, (s : ℝ) * x 0, x 1]
    let z : Fin 3 → V 2 := ![vec2 0 0, vec2 s 0, vec2 0 1]
    apply mem_convexHull_of_exists_fintype w z
    · intro i
      fin_cases i <;> dsimp [w] <;> linarith [hx.1, hx.2.1, hx.2.2]
    · simp [w, Fin.sum_univ_succ]
    · intro i
      fin_cases i <;> simp [z, triangle]
    · ext i
      fin_cases i
      · simp [w, z, vec2, Fin.sum_univ_succ]
        rcases hs with rfl | rfl <;> norm_num at * <;> nlinarith
      · simp [w, z, vec2, Fin.sum_univ_succ]
  refine ⟨vec2 ((s : ℝ) / 4) (1 / 4), ?_⟩
  apply interior_maximal hUsub hUopen
  change 0 < (s : ℝ) * ((s : ℝ) / 4) ∧ 0 < (1 / 4 : ℝ) ∧
    (s : ℝ) * ((s : ℝ) / 4) + 1 / 4 < 1
  constructor
  · rcases hs with rfl | rfl <;> norm_num
  · constructor <;> (rcases hs with rfl | rfl <;> norm_num)

theorem triangle_zero_smooth (s : ℤ) (hs : s = 1 ∨ s = -1) :
    Fan.IsSmoothCone (normalConeAt (triangle s) (vec2 0 0)) := by
  have hs2 : (s : ℝ) * (s : ℝ) = 1 := by rcases hs with rfl | rfl <;> norm_num
  refine ⟨![vec2 (-s) 0, vec2 0 (-1)], ?_, ?_, ?_⟩
  · intro i j
    refine ⟨(![![-s, 0], ![0, -1]] : Fin 2 → Fin 2 → ℤ) i j, ?_⟩
    fin_cases i <;> fin_cases j <;> norm_num [vec2]
  · rcases hs with rfl | rfl <;> norm_num [Matrix.det_fin_two, vec2]
  · ext x
    change (x ∈ normalConeAt (triangle s) (vec2 0 0)) ↔ _
    rw [normal_triangle_zero]
    constructor
    · rintro ⟨hx, hy⟩
      refine ⟨![-(s : ℝ) * x 0, -x 1], ?_, ?_⟩
      · intro i
        fin_cases i <;> simp <;> linarith
      · ext i
        fin_cases i <;> simp [vec2, Fin.sum_univ_two]
        rcases hs with rfl | rfl <;> norm_num at * <;> nlinarith
    · rintro ⟨t, ht, heq⟩
      have h0 := congrFun heq 0
      have h1 := congrFun heq 1
      simp [vec2, Fin.sum_univ_two] at h0 h1
      constructor
      · rcases hs with rfl | rfl <;> norm_num at * <;> linarith
      · linarith [ht 1]

theorem triangle_side_smooth (s : ℤ) (hs : s = 1 ∨ s = -1) :
    Fan.IsSmoothCone (normalConeAt (triangle s) (vec2 s 0)) := by
  have hs2 : (s : ℝ) * (s : ℝ) = 1 := by rcases hs with rfl | rfl <;> norm_num
  refine ⟨![vec2 s 1, vec2 0 (-1)], ?_, ?_, ?_⟩
  · intro i j
    refine ⟨(![![s, 1], ![0, -1]] : Fin 2 → Fin 2 → ℤ) i j, ?_⟩
    fin_cases i <;> fin_cases j <;> norm_num [vec2]
  · rcases hs with rfl | rfl <;> norm_num [Matrix.det_fin_two, vec2]
  · ext x
    change (x ∈ normalConeAt (triangle s) (vec2 s 0)) ↔ _
    rw [normal_triangle_side]
    constructor
    · rintro ⟨hx, hy⟩
      refine ⟨![(s : ℝ) * x 0, (s : ℝ) * x 0 - x 1], ?_, ?_⟩
      · intro i
        fin_cases i <;> simp <;> linarith
      · ext i
        fin_cases i <;> simp [vec2, Fin.sum_univ_two]
        rcases hs with rfl | rfl <;> norm_num at * <;> nlinarith
    · rintro ⟨t, ht, heq⟩
      have h0 := congrFun heq 0
      have h1 := congrFun heq 1
      simp [vec2, Fin.sum_univ_two] at h0 h1
      rcases hs with rfl | rfl <;> norm_num at * <;> constructor <;> linarith

theorem triangle_top_smooth (s : ℤ) (hs : s = 1 ∨ s = -1) :
    Fan.IsSmoothCone (normalConeAt (triangle s) (vec2 0 1)) := by
  have hs2 : (s : ℝ) * (s : ℝ) = 1 := by rcases hs with rfl | rfl <;> norm_num
  refine ⟨![vec2 s 1, vec2 (-s) 0], ?_, ?_, ?_⟩
  · intro i j
    refine ⟨(![![s, 1], ![-s, 0]] : Fin 2 → Fin 2 → ℤ) i j, ?_⟩
    fin_cases i <;> fin_cases j <;> norm_num [vec2]
  · rcases hs with rfl | rfl <;> norm_num [Matrix.det_fin_two, vec2]
  · ext x
    change (x ∈ normalConeAt (triangle s) (vec2 0 1)) ↔ _
    rw [normal_triangle_top]
    constructor
    · rintro ⟨hx, hy⟩
      refine ⟨![x 1, x 1 - (s : ℝ) * x 0], ?_, ?_⟩
      · intro i
        fin_cases i <;> simp <;> linarith
      · ext i
        fin_cases i <;> simp [vec2, Fin.sum_univ_two]
        rcases hs with rfl | rfl <;> norm_num at * <;> nlinarith
    · rintro ⟨t, ht, heq⟩
      have h0 := congrFun heq 0
      have h1 := congrFun heq 1
      simp [vec2, Fin.sum_univ_two] at h0 h1
      rcases hs with rfl | rfl <;> norm_num at * <;> constructor <;> linarith

/-- Both triangles in the example satisfy the actual Delzant definition. -/
theorem triangle_isDelzant (s : ℤ) (hs : s = 1 ∨ s = -1) : IsDelzant (triangle s) := by
  classical
  refine ⟨triangle_fullDim s hs, ?_⟩
  intro C hC _
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hC
  simp only [triangle, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · exact triangle_zero_smooth s hs
  · exact triangle_side_smooth s hs
  · exact triangle_top_smooth s hs

/-- A cone bounded by the two primitive rays `(1,1)` and `(-1,1)`
cannot be the positive span of any integral basis. -/
theorem not_smooth_wedge (C : Cone 2)
    (hC : (C : Set (V 2)) = {x | x 0 ≤ x 1 ∧ -x 0 ≤ x 1}) :
    ¬ Fan.IsSmoothCone C := by
  intro h
  obtain ⟨u, hint, hdet, hspan⟩ := h
  have hrow : ∀ i, u i 0 ≤ u i 1 ∧ -(u i 0) ≤ u i 1 := by
    intro i
    have hm : u i ∈ (C : Set (V 2)) := by
      rw [hspan]
      refine ⟨Pi.single i 1, ?_, ?_⟩
      · intro j
        simp only [Pi.single_apply]
        split_ifs <;> norm_num
      · simp
    simpa only [hC, Set.mem_setOf_eq] using hm
  have hboundary : ∀ a : ℝ, a = 1 ∨ a = -1 → ∃ i, u i 1 = a * u i 0 := by
    intro a ha
    have hv : vec2 a 1 ∈ (C : Set (V 2)) := by
      rw [hC]
      rcases ha with rfl | rfl <;> norm_num [vec2]
    rw [hspan] at hv
    obtain ⟨t, ht, heq⟩ := hv
    have h0 := congrFun heq 0
    have h1 := congrFun heq 1
    simp [vec2, Fin.sum_univ_two] at h0 h1
    have hgap : ∀ i, 0 ≤ u i 1 - a * u i 0 := by
      intro i
      rcases ha with rfl | rfl <;> norm_num <;> linarith [(hrow i).1, (hrow i).2]
    have htotal : t 0 * (u 0 1 - a * u 0 0) + t 1 * (u 1 1 - a * u 1 0) = 0 := by
      rcases ha with rfl | rfl <;> norm_num at * <;> nlinarith
    have hz0 : t 0 * (u 0 1 - a * u 0 0) = 0 := by
      nlinarith [mul_nonneg (ht 0) (hgap 0), mul_nonneg (ht 1) (hgap 1)]
    have hz1 : t 1 * (u 1 1 - a * u 1 0) = 0 := by
      nlinarith [mul_nonneg (ht 0) (hgap 0), mul_nonneg (ht 1) (hgap 1)]
    have hp : 0 < t 0 ∨ 0 < t 1 := by
      by_contra hn
      push_neg at hn
      have ht0 : t 0 = 0 := le_antisymm hn.1 (ht 0)
      have ht1 : t 1 = 0 := le_antisymm hn.2 (ht 1)
      simp [ht0, ht1] at h1
    rcases hp with hp | hp
    · exact ⟨0, sub_eq_zero.mp ((mul_eq_zero.mp hz0).resolve_left hp.ne')⟩
    · exact ⟨1, sub_eq_zero.mp ((mul_eq_zero.mp hz1).resolve_left hp.ne')⟩
  obtain ⟨i, hi⟩ := hboundary 1 (Or.inl rfl)
  obtain ⟨j, hj⟩ := hboundary (-1) (Or.inr rfl)
  obtain ⟨a, ha⟩ := hint 0 0
  obtain ⟨b, hb⟩ := hint 0 1
  obtain ⟨c, hc⟩ := hint 1 0
  obtain ⟨d, hd⟩ := hint 1 1
  have hdetZ : |a * d - b * c| = (1 : ℤ) := by
    rw [Matrix.det_fin_two, ha, hb, hc, hd] at hdet
    exact_mod_cast hdet
  fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd] at hi hj
  · have hba : b = a := by exact_mod_cast hi
    have hbn : b = -a := by exact_mod_cast hj
    have haz : a = 0 := by omega
    have hbz : b = 0 := by omega
    simp [haz, hbz] at hdetZ
  · have hba : b = a := by exact_mod_cast hi
    have hdc : d = -c := by exact_mod_cast hj
    have heq : a * d - b * c = -2 * (a * c) := by rw [hba, hdc]; ring
    rw [heq, abs_mul] at hdetZ
    norm_num at hdetZ
    omega
  · have hdc : d = c := by exact_mod_cast hi
    have hbn : b = -a := by exact_mod_cast hj
    have heq : a * d - b * c = 2 * (a * c) := by rw [hdc, hbn]; ring
    rw [heq, abs_mul] at hdetZ
    norm_num at hdetZ
    omega
  · have hdc : d = c := by exact_mod_cast hi
    have hdn : d = -c := by exact_mod_cast hj
    have hcz : c = 0 := by omega
    have hdz : d = 0 := by omega
    simp [hcz, hdz] at hdetZ

/-- The actual normal cone at the upper vertex of the Minkowski sum. -/
theorem sum_top_normalCone :
    (normalConeAt ((triangle 1).add (triangle (-1))) (vec2 0 2) : Set (V 2)) =
      {x | x 0 ≤ x 1 ∧ -x 0 ≤ x 1} := by
  have ht : vec2 0 1 + vec2 0 1 = vec2 0 2 := by ext i; fin_cases i <;> norm_num [vec2]
  rw [← ht, normalConeAt_add (subset_convexHull ℝ _ (by simp [triangle]))
    (subset_convexHull ℝ _ (by simp [triangle]))]
  ext x
  change (x ∈ normalConeAt (triangle 1) (vec2 0 1) ∧
    x ∈ normalConeAt (triangle (-1)) (vec2 0 1)) ↔ _
  rw [normal_triangle_top, normal_triangle_top]
  norm_num
  constructor
  · tauto
  · rintro ⟨h0, h1⟩
    exact ⟨⟨by linarith, h0⟩, ⟨by linarith, h1⟩⟩

/-- The singular cone in the sum is full dimensional. -/
theorem sum_top_normalCone_interior :
    (interior (normalConeAt ((triangle 1).add (triangle (-1))) (vec2 0 2) : Set (V 2))).Nonempty := by
  rw [sum_top_normalCone]
  let U : Set (V 2) := {x | x 0 < x 1 ∧ -x 0 < x 1}
  have ho : IsOpen U := (isOpen_lt (continuous_apply 0) (continuous_apply 1)).inter
    (isOpen_lt (continuous_apply 0).neg (continuous_apply 1))
  have hsub : U ⊆ {x : V 2 | x 0 ≤ x 1 ∧ -x 0 ≤ x 1} := fun x hx => ⟨hx.1.le, hx.2.le⟩
  refine ⟨vec2 0 1, interior_maximal hsub ho ?_⟩
  norm_num [U, vec2]

/-- The two actual Delzant triangles have a non-Delzant Minkowski sum. -/
theorem triangle_sum_not_isDelzant : ¬ IsDelzant ((triangle 1).add (triangle (-1))) := by
  intro h
  apply not_smooth_wedge _ sum_top_normalCone
  have htop : vec2 0 2 ∈ ((triangle 1).add (triangle (-1))).carrier := by
    rw [carrier_add_eq]
    have ht : vec2 0 1 + vec2 0 1 = vec2 0 2 := by ext i; fin_cases i <;> norm_num [vec2]
    rw [← ht]
    exact Set.add_mem_add (subset_convexHull ℝ _ (by simp [triangle]))
      (subset_convexHull ℝ _ (by simp [triangle]))
  exact normalConeAt_isSmooth_of_fan _ h.2 htop sum_top_normalCone_interior

end Example24
end Paper17
