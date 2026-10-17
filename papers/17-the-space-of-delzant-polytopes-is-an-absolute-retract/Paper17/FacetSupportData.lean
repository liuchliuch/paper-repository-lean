import Paper17.HalfspaceComplex

/-!
# Realizing an integral cone complex by actual supporting data

Heights, feasible vertices, and their exact active constraints are concrete
geometric input. The finite polytope and equality of its actual normal cones
are derived below; no Delzant or resolution conclusion is stored as a field.
-/
noncomputable section
open scoped BigOperators Topology
namespace Paper17
namespace IntegralConeComplex
variable {n : ℕ}

/-- Concrete supporting hyperplanes and points realizing the maximal cones. -/
structure FacetSupportData (K : IntegralConeComplex n) where
  heights : K.index → ℝ
  vertex : K.complex.facets → V n
  feasible : ∀ s, ∀ i, dot (realRays K.rays i) (vertex s) ≤ heights i
  active : ∀ s, ∀ i, dot (realRays K.rays i) (vertex s) = heights i ↔ i ∈ s.val
  interiorPoint : V n
  strictInterior : ∀ i, dot (realRays K.rays i) interiorPoint < heights i
  complete : K.support = Set.univ

namespace FacetSupportData
variable {K : IntegralConeComplex n} (R : FacetSupportData K)

include R in
theorem facets_nonempty : K.complex.facets.Nonempty := by
  have hz : (0 : V n) ∈ K.support := by rw [R.complete]; trivial
  obtain ⟨s, hs, _⟩ := Set.mem_iUnion₂.mp hz
  exact ⟨s, hs⟩

/-- The actual finite polytope whose vertices are the supplied feasible points. -/
def polytope : Polytope n where
  verts := K.complex.facets.attach.image R.vertex
  nonempty_verts' := by
    obtain ⟨s, hs⟩ := R.facets_nonempty
    exact ⟨R.vertex ⟨s, hs⟩, Finset.mem_image.mpr ⟨⟨s, hs⟩, by simp, rfl⟩⟩

theorem vertex_mem (s : K.complex.facets) : R.vertex s ∈ R.polytope.carrier := by
  apply subset_convexHull ℝ _
  exact Finset.mem_image.mpr ⟨s, by simp, rfl⟩

/-- Completeness of the actual cones proves that the finite convex hull is
exactly the halfspace intersection specified by the heights. -/
theorem carrier_eq_halfspaces :
    R.polytope.carrier = finiteHalfspaces (realRays K.rays) R.heights := by
  apply Set.Subset.antisymm
  · apply convexHull_min _ (finiteHalfspaces_convex _ _)
    intro x hx
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hx
    exact R.feasible s
  · apply subset_of_forall_dot_le_supportFunction R.polytope.isCompact R.polytope.nonempty R.polytope.convex
    intro u x hx
    have hu : u ∈ K.support := by rw [R.complete]; trivial
    obtain ⟨s, hs, ⟨c, hc0, hcs, hu⟩⟩ := Set.mem_iUnion₂.mp hu
    let p := R.vertex ⟨s, hs⟩
    have hmax : dot u p = ∑ i, c i * R.heights i := by
      rw [hu, dot_fintype_sum_smul]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ s
      · rw [(R.active ⟨s, hs⟩ i).mpr hi]
      · simp [hcs i hi]
    calc dot u x = ∑ i, c i * dot (realRays K.rays i) x := by rw [hu, dot_fintype_sum_smul]
      _ ≤ ∑ i, c i * R.heights i :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hx i) (hc0 i))
      _ = dot u p := hmax.symm
      _ ≤ supportFunction R.polytope.carrier u := supportFunction_ub R.polytope.isCompact (R.vertex_mem _)

theorem interior_nonempty : (interior R.polytope.carrier).Nonempty := by
  rw [R.carrier_eq_halfspaces]
  let U : Set (V n) := {x | ∀ i, dot (realRays K.rays i) x < R.heights i}
  have hUopen : IsOpen U := by
    simpa only [U, Set.setOf_forall] using isOpen_iInter_of_finite
      (fun i : K.index => isOpen_lt (continuous_dot (realRays K.rays i)) continuous_const)
  have hsub : U ⊆ finiteHalfspaces (realRays K.rays) R.heights := fun x hx i => (hx i).le
  exact ⟨R.interiorPoint, interior_maximal hsub hUopen R.strictInterior⟩

/-- The actual normal cone at each supplied vertex is exactly the corresponding
maximal cone of the integral complex. -/
theorem normalCone_eq (s : K.complex.facets) :
    (normalConeAt R.polytope (R.vertex s) : Set (V n)) = raySpan (realRays K.rays) s.val := by
  have hact : activeConstraints (realRays K.rays) R.heights (R.vertex s) = s.val := by
    ext i
    exact (mem_activeConstraints _ _ _ i).trans (R.active s i)
  have hs : s.val.card = n := K.fullCard s.val s.property
  have hdet : (constraintMatrix (realRays K.rays) s.val hs).det ≠ 0 := by
    change ((cellMatrix K.rays s.val hs).map (fun z => (z : ℝ))).det ≠ 0
    rw [← Int.cast_det]
    exact_mod_cast cellMatrix_det_ne_zero K.rays s.val hs (K.complex.independent s.val s.property)
  have hs' : (activeConstraints (realRays K.rays) R.heights (R.vertex s)).card = n := by rw [hact]; exact hs
  have hdet' : (constraintMatrix (realRays K.rays)
      (activeConstraints (realRays K.rays) R.heights (R.vertex s)) hs').det ≠ 0 := by
    have htransport : ∀ t : Finset K.index, ∀ ht : t.card = n, t = s.val →
        (constraintMatrix (realRays K.rays) t ht).det ≠ 0 := by
      intro t ht heq
      subst t
      exact hdet
    exact htransport _ hs' hact
  have hn := normalCone_finiteHalfspaces (realRays K.rays) R.heights (R.feasible s) hs' hdet'
  rw [hact] at hn
  have hcone : (normalConeAt R.polytope (R.vertex s) : Set (V n)) =
      carrierNormalCone (finiteHalfspaces (realRays K.rays) R.heights) (R.vertex s) := by
    ext u
    change (∀ y ∈ R.polytope.carrier, dot u y ≤ dot u (R.vertex s)) ↔ _
    rw [R.carrier_eq_halfspaces]
    rfl
  exact hcone.trans hn

/-- Unimodularity of the integral complex gives an actual Delzant polytope. -/
theorem isDelzant (hsmooth : ∀ s ∈ K.complex.facets, coneMultiplicity K.rays s = 1) :
    IsDelzant R.polytope := by
  classical
  refine ⟨R.interior_nonempty, ?_⟩
  intro C hC _
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hC
  obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hp
  have hs := K.fullCard s.val s.property
  have heq : normalConeAt R.polytope (R.vertex s) = latticeConeObject (cellMatrix K.rays s.val hs) := by
    apply Cone.ext
    exact (R.normalCone_eq s).trans (raySpan_eq_latticeCone K.rays s.val hs)
  rw [heq]
  apply latticeConeObject_isSmooth
  simpa only [coneMultiplicity_of_card K.rays s.val hs] using hsmooth s.val s.property

end FacetSupportData
end IntegralConeComplex

/-- A simple finite halfspace polytope supplies concrete supporting data for
its actual normal complex. The interior point is an actual strict solution. -/
def halfspaceFacetSupportData {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (v : ι → Fin n → ℤ) (h : ι → ℝ) (hgen : GeneralPositionHeights (realRays v) h)
    (hcompact : IsCompact (finiteHalfspaces (realRays v) h)) (z : V n)
    (hz : ∀ i, dot (realRays v i) z < h i) :
    IntegralConeComplex.FacetSupportData (integralHalfspaceComplex v h hgen) where
  heights := h
  vertex := fun s => constraintVertex (realRays v) h s.val
  feasible := fun s => (halfspaceFacet_spec (realRays v) h hgen s.property).choose_spec.2.1
  active := by
    intro s i
    have heq := (halfspaceFacet_spec (realRays v) h hgen s.property).choose_spec.2.2.1
    change dot (realRays v i) (constraintVertex (realRays v) h s.val) = h i ↔ i ∈ s.val
    rw [← mem_activeConstraints (realRays v) h (constraintVertex (realRays v) h s.val) i, heq]
  interiorPoint := z
  strictInterior := hz
  complete := halfspaceConeComplex_complete (realRays v) h hgen hcompact ⟨z, fun i => (hz i).le⟩

end Paper17
