import Paper17.HalfspaceVertices
import Paper17.SimplicialFanResolution

/-!
# The genuine normal cone complex of a simple halfspace polytope

Maximal cells are feasible nonsingular active systems. Common ray intersections
are proved from equality of maximizing values and positive slack at inactive
constraints. Completeness follows from the actual finite vertex realization.
-/
noncomputable section
open scoped BigOperators
namespace Paper17
section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- The finite collection of actual feasible full-size active systems. -/
def halfspaceFacets (a : ι → V n) (h : ι → ℝ) : Finset (Finset ι) := by
  classical
  exact Finset.univ.powerset.filter (AdmissibleConstraintSet a h)

theorem mem_halfspaceFacets (a : ι → V n) (h : ι → ℝ) (s : Finset ι) :
    s ∈ halfspaceFacets a h ↔ AdmissibleConstraintSet a h s := by
  classical
  simp only [halfspaceFacets, Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]

/-- Actual feasible vertex data for a maximal cell. -/
theorem halfspaceFacet_spec (a : ι → V n) (h : ι → ℝ)
    (hgen : GeneralPositionHeights a h) {s : Finset ι} (hs : s ∈ halfspaceFacets a h) :
    ∃ hcard : s.card = n, (constraintMatrix a s hcard).det ≠ 0 ∧
      constraintVertex a h s ∈ finiteHalfspaces a h ∧
      activeConstraints a h (constraintVertex a h s) = s ∧
      carrierNormalCone (finiteHalfspaces a h) (constraintVertex a h s) = raySpan a s := by
  obtain ⟨hcard, hdet, hfeas⟩ := (mem_halfspaceFacets a h s).mp hs
  have heq := activeConstraints_constraintVertex a h hgen s hcard hdet hfeas
  have hcard' : (activeConstraints a h (constraintVertex a h s)).card = n := by rw [heq]; exact hcard
  have hdet' : (constraintMatrix a (activeConstraints a h (constraintVertex a h s)) hcard').det ≠ 0 := by
    have htransport : ∀ t : Finset ι, ∀ ht : t.card = n, t = s →
        (constraintMatrix a t ht).det ≠ 0 := by
      intro t ht he
      subst t
      exact hdet
    exact htransport _ hcard' heq
  refine ⟨hcard, hdet, hfeas, heq, ?_⟩
  simpa only [heq] using normalCone_finiteHalfspaces a h hfeas hcard' hdet'

/-- The actual active ray vectors of a maximal cell are linearly independent. -/
theorem halfspaceFacet_independent (a : ι → V n) (h : ι → ℝ)
    {s : Finset ι} (hs : s ∈ halfspaceFacets a h) :
    LinearIndependent ℝ (fun i : ↑s => a i.val) := by
  obtain ⟨hcard, hdet, _⟩ := (mem_halfspaceFacets a h s).mp hs
  let e := cellEnumeration s hcard
  have hrows := Matrix.linearIndependent_rows_of_det_ne_zero hdet
  have hh := hrows.comp e.symm e.symm.injective
  change LinearIndependent ℝ (fun i : ↑s => a (e (e.symm i)).val) at hh
  simpa only [Equiv.apply_symm_apply] using hh

/-- Actual normal cones from distinct vertices intersect in the positive span
of their common active normals. -/
theorem halfspaceFacet_intersection (a : ι → V n) (h : ι → ℝ)
    (hgen : GeneralPositionHeights a h) {s t : Finset ι}
    (hs : s ∈ halfspaceFacets a h) (ht : t ∈ halfspaceFacets a h) :
    raySpan a s ∩ raySpan a t = raySpan a (s ∩ t) := by
  classical
  obtain ⟨hsn, hsdet, hps, hactS, hconeS⟩ := halfspaceFacet_spec a h hgen hs
  obtain ⟨htn, htdet, hpT, hactT, hconeT⟩ := halfspaceFacet_spec a h hgen ht
  let p := constraintVertex a h s
  let q := constraintVertex a h t
  apply Set.Subset.antisymm
  · rintro u ⟨hus, hut⟩
    have hnormalP : u ∈ carrierNormalCone (finiteHalfspaces a h) p := hconeS.symm ▸ hus
    have hnormalQ : u ∈ carrierNormalCone (finiteHalfspaces a h) q := hconeT.symm ▸ hut
    have hmax : dot u p = dot u q := le_antisymm (hnormalQ p hps) (hnormalP q hpT)
    obtain ⟨c, hc0, hcs, hu⟩ := hus
    have hnonneg : ∀ i, 0 ≤ c i * (h i - dot (a i) q) :=
      fun i => mul_nonneg (hc0 i) (sub_nonneg.mpr (hpT i))
    have hp : (∑ i, c i * h i) = dot u p := by
      rw [hu, dot_fintype_sum_smul]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ s
      · rw [(mem_activeConstraints a h p i).mp (hactS ▸ hi)]
      · simp [hcs i hi]
    have hq : (∑ i, c i * dot (a i) q) = dot u q := by rw [hu, dot_fintype_sum_smul]
    have hzero : ∑ i, c i * (h i - dot (a i) q) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      rw [hp, hq, hmax, sub_self]
    have hterm : ∀ i, c i * (h i - dot (a i) q) = 0 :=
      fun i => (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg j)).mp hzero i (Finset.mem_univ i)
    refine ⟨c, hc0, ?_, hu⟩
    intro i hi
    by_cases his : i ∈ s
    · have hit : i ∉ t := fun hit => hi (Finset.mem_inter.mpr ⟨his, hit⟩)
      have hstrict : dot (a i) q < h i := lt_of_le_of_ne (hpT i) (fun heq =>
        hit (hactT ▸ (mem_activeConstraints a h q i).mpr heq))
      exact (mul_eq_zero.mp (hterm i)).resolve_right (sub_pos.mpr hstrict).ne'
    · exact hcs i his
  · intro u hu
    exact ⟨raySpan_mono a Finset.inter_subset_left hu, raySpan_mono a Finset.inter_subset_right hu⟩

/-- The genuine geometric simplicial complex of active normal systems. -/
def halfspaceConeComplex (a : ι → V n) (h : ι → ℝ)
    (hgen : GeneralPositionHeights a h) : SimplicialConeComplex a where
  facets := halfspaceFacets a h
  independent := fun _ hs => halfspaceFacet_independent a h hs
  intersection := fun _ hs _ ht => halfspaceFacet_intersection a h hgen hs ht

/-- The normal complex covers the entire ambient dual space. -/
theorem halfspaceConeComplex_complete (a : ι → V n) (h : ι → ℝ)
    (hgen : GeneralPositionHeights a h) (hcompact : IsCompact (finiteHalfspaces a h))
    (hne : (finiteHalfspaces a h).Nonempty) :
    (⋃ s ∈ (halfspaceConeComplex a h hgen).facets, raySpan a s) = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro u
  let P := halfspacePolytope a h hgen hcompact hne
  obtain ⟨p, hp, hmax⟩ := exists_mem_verts_isMaxOn P u
  obtain ⟨s, hs, heq⟩ := Finset.mem_image.mp hp
  have hfacet : s ∈ halfspaceFacets a h := hs
  obtain ⟨hcard, hdet, hfeas, hact, hcone⟩ := halfspaceFacet_spec a h hgen hfacet
  have hnorm : u ∈ carrierNormalCone (finiteHalfspaces a h) (constraintVertex a h s) := by
    intro y hy
    rw [← halfspacePolytope_carrier a h hgen hcompact hne] at hy
    simpa only [heq] using hmax y hy
  exact Set.mem_iUnion₂.mpr ⟨s, hfacet, hcone ▸ hnorm⟩

/-- Integral supporting normals give an actual full-dimensional integral
simplicial normal complex, ready for the terminating resolution algorithm. -/
def integralHalfspaceComplex (v : ι → Fin n → ℤ) (h : ι → ℝ)
    (hgen : GeneralPositionHeights (realRays v) h) : IntegralConeComplex n where
  index := ι
  rays := v
  complex := halfspaceConeComplex (realRays v) h hgen
  fullCard := by
    intro s hs
    exact Classical.choose ((mem_halfspaceFacets (realRays v) h s).mp hs)

end
end Paper17
