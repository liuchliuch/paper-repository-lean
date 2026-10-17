import Verification.Example24Prism

/-! Smoothness and refinement of actual three-dimensional prism fans. -/
noncomputable section
open scoped BigOperators Topology
namespace Paper17.Example24

def prismBasis (v : Fin 2 → V 2) (b : Bool) : Fin 3 → V 3 :=
  ![prismPoint (v 0) 0, prismPoint (v 1) 0, ![0, 0, if b then 1 else -1]]

/-- Appending the correctly signed vertical unit to an actual planar lattice
basis gives the actual endpoint normal cone of the prism. -/
theorem smooth_prism_endpoint (P : Polytope 2) {a : ℝ} (ha : 0 < a)
    {p : V 2} (hp : p ∈ P.verts) (b : Bool)
    (hs : Fan.IsSmoothCone (normalConeAt P p)) :
    Fan.IsSmoothCone (normalConeAt (prism P a) (prismPoint p (if b then a else 0))) := by
  obtain ⟨v, hvint, hvdet, hvcone⟩ := hs
  refine ⟨prismBasis v b, ?_, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j
    · exact hvint 0 0
    · exact hvint 0 1
    · exact ⟨0, by simp [prismBasis, prismPoint]⟩
    · exact hvint 1 0
    · exact hvint 1 1
    · exact ⟨0, by simp [prismBasis, prismPoint]⟩
    · exact ⟨0, by simp [prismBasis, prismPoint]⟩
    · exact ⟨0, by simp [prismBasis, prismPoint]⟩
    · refine ⟨(if b then 1 else -1 : ℤ), ?_⟩
      cases b <;> norm_num [prismBasis]
  · have hd : Matrix.det (fun i j => prismBasis v b i j) =
        (if b then 1 else -1) * Matrix.det (fun i j => v i j) := by
      cases b <;> simp [prismBasis, prismPoint, Matrix.det_fin_three, Matrix.det_fin_two] <;> ring
    rw [hd, abs_mul, hvdet]
    cases b <;> norm_num
  · ext u
    change (u ∈ normalConeAt (prism P a) (prismPoint p (if b then a else 0))) ↔ _
    rw [normal_prism_endpoint P ha hp b u]
    constructor
    · rintro ⟨hu, hz⟩
      change planeProjection u ∈ (normalConeAt P p : Set (V 2)) at hu
      rw [hvcone] at hu
      obtain ⟨c, hc, huc⟩ := hu
      let d : Fin 3 → ℝ := ![c 0, c 1, if b then u 2 else -u 2]
      refine ⟨d, ?_, ?_⟩
      · intro j
        fin_cases j
        · exact hc 0
        · exact hc 1
        · cases b <;> simp [d] at hz ⊢ <;> linarith
      · have h0 := congrFun huc 0
        have h1 := congrFun huc 1
        simp [planeProjection, Fin.sum_univ_two] at h0 h1
        ext j
        fin_cases j <;> cases b <;>
          simp [d, prismBasis, prismPoint, Fin.sum_univ_succ] <;> linarith
    · rintro ⟨c, hc, huc⟩
      have h0 := congrFun huc 0
      have h1 := congrFun huc 1
      have h2 := congrFun huc 2
      simp [prismBasis, prismPoint, Fin.sum_univ_succ] at h0 h1 h2
      refine ⟨?_, ?_⟩
      · change planeProjection u ∈ (normalConeAt P p : Set (V 2))
        rw [hvcone]
        refine ⟨![c 0, c 1], ?_, ?_⟩
        · intro j
          fin_cases j
          · exact hc 0
          · exact hc 1
        · ext j
          fin_cases j <;> simp [planeProjection, Fin.sum_univ_two] <;> linarith
      · cases b <;> simp at h2 ⊢ <;> linarith [hc 2]

/-- Interior of a prism endpoint normal cone forces interior of its planar
normal cone, by an actual fixed-height affine slice of an open set. -/
theorem planar_normal_interior_of_prism (P : Polytope 2) {a : ℝ} (ha : 0 < a)
    {p : V 2} (hp : p ∈ P.verts) (b : Bool)
    (hi : (interior (normalConeAt (prism P a) (prismPoint p (if b then a else 0)) :
      Set (V 3))).Nonempty) : (interior (normalConeAt P p : Set (V 2))).Nonempty := by
  obtain ⟨u, hu⟩ := hi
  let U : Set (V 2) := {q | prismPoint q (u 2) ∈
    interior (normalConeAt (prism P a) (prismPoint p (if b then a else 0)) : Set (V 3))}
  have ho : IsOpen U := isOpen_interior.preimage (continuous_prismPoint_fixed (u 2))
  have hs : U ⊆ (normalConeAt P p : Set (V 2)) := by
    intro q hq
    have hh := ((normal_prism_endpoint P ha hp b _).mp (interior_subset hq)).1
    simpa only [planeProjection_prismPoint] using hh
  refine ⟨planeProjection u, interior_maximal hs ho ?_⟩
  change prismPoint (planeProjection u) (u 2) ∈
    interior (normalConeAt (prism P a) (prismPoint p (if b then a else 0)) : Set (V 3))
  rwa [prismPoint_projection]

/-- Products of actual Delzant polygons with a nondegenerate interval are
actual Delzant three-polytopes. Redundant planar vertices are allowed. -/
theorem prism_isDelzant (P : Polytope 2) (hP : IsDelzant P) {a : ℝ} (ha : 0 < a) :
    IsDelzant (prism P a) := by
  classical
  refine ⟨prism_fullDim P hP.1 ha, ?_⟩
  intro C hC hi
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hC
  obtain ⟨⟨p, z⟩, hpz, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hp, hz⟩ := Finset.mem_product.mp hpz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  have hh : ∀ b : Bool,
      (interior (normalConeAt (prism P a) (prismPoint p (if b then a else 0)) :
        Set (V 3))).Nonempty →
      Fan.IsSmoothCone (normalConeAt (prism P a) (prismPoint p (if b then a else 0))) := by
    intro b hi
    apply smooth_prism_endpoint P ha hp b
    exact hP.2 (normalConeAt P p) (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
      (planar_normal_interior_of_prism P ha hp b hi)
  rcases hz with rfl | rfl
  · exact hh false hi
  · exact hh true hi

/-- Actual prism normal fans preserve a given planar refinement. -/
theorem normalFan_prism_refines {P Q : Polytope 2}
    (h : (NormalFan P).refines (NormalFan Q)) {a : ℝ} (ha : 0 < a) :
    (NormalFan (prism P a)).refines (NormalFan (prism Q a)) := by
  classical
  intro C hC
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hC
  obtain ⟨⟨p, z⟩, hpz, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hp, hz⟩ := Finset.mem_product.mp hpz
  obtain ⟨D, hD, hsub⟩ := h (normalConeAt P p) (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hD
  refine ⟨normalConeAt (prism Q a) (prismPoint q z), ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨prismPoint q z,
      Finset.mem_image.mpr ⟨(q, z), Finset.mem_product.mpr ⟨hq, hz⟩, rfl⟩, rfl⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    have hh : ∀ b : Bool, (normalConeAt (prism P a) (prismPoint p (if b then a else 0)) :
        Set (V 3)) ⊆ normalConeAt (prism Q a) (prismPoint q (if b then a else 0)) := by
      intro b u hu
      obtain ⟨hu, huz⟩ := (normal_prism_endpoint P ha hp b u).mp hu
      exact (normal_prism_endpoint Q ha hq b u).mpr ⟨hsub hu, huz⟩
    rcases hz with rfl | rfl
    · exact hh false
    · exact hh true

/-- The three actual source prisms are Delzant and the hexagon prism refines
both triangle prisms. -/
theorem source_prisms_delzant_refinement :
    IsDelzant (prism (triangle 1) 1) ∧ IsDelzant (prism (triangle (-1)) 1) ∧
      IsDelzant exampleS ∧
      (NormalFan exampleS).refines (NormalFan (prism (triangle 1) 1)) ∧
      (NormalFan exampleS).refines (NormalFan (prism (triangle (-1)) 1)) := by
  exact ⟨prism_isDelzant _ (triangle_isDelzant 1 (Or.inl rfl)) (by norm_num),
    prism_isDelzant _ (triangle_isDelzant (-1) (Or.inr rfl)) (by norm_num),
    prism_isDelzant _ hexagon_isDelzant (by norm_num),
    normalFan_prism_refines hexagon_refines_triangles.1 (by norm_num),
    normalFan_prism_refines hexagon_refines_triangles.2 (by norm_num)⟩

end Paper17.Example24
