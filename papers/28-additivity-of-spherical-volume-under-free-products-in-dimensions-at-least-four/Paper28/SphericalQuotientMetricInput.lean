import Paper28.RegularSphereAction
import Paper28.NormFoldings

/-! Explicit published metric-object input for Song's spherical quotient.
The underlying l2 space, unit sphere, regular action and orbit quotient are
native constructions above. This signature only realizes the standard round
quotient metric on that exact quotient, pinned by its arccos/infimum formula
and quotient topology (Song arXiv:2202.10636v6, Section 3.1, pp.20-21).
There is no map, deformation, current, mass, approximation or sharp estimate
in this input. Its standard metric realization is not rebuilt here.
-/
set_option autoImplicit false
noncomputable section
namespace Paper28
open scoped InnerProductSpace
variable (G : Type*) [Group G] [DecidableEq G] [Countable G]

structure SphericalQuotientMetricInput where
  quotientMetric : MetricSpace (RegularOrbitQuotient G)
  topology_eq : (inferInstance : TopologicalSpace (RegularOrbitQuotient G)) =
    quotientMetric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  distance_eq : ∀ u v : RegularSphere G,
    @dist (RegularOrbitQuotient G) quotientMetric.toDist (regularQuotientMap u) (regularQuotientMap v) =
      sInf (Set.range (fun γ : G => angular u.val (leftRegular γ v.val)))

/-- Preserve the already constructed actual quotient topology definitionally. -/
abbrev SphericalQuotientMetricInput.metric (M : SphericalQuotientMetricInput G) :
    MetricSpace (RegularOrbitQuotient G) := M.quotientMetric.replaceTopology M.topology_eq

variable {G} (M : SphericalQuotientMetricInput G)

theorem spherical_quotient_distance (u v : RegularSphere G) :
    @dist (RegularOrbitQuotient G) M.metric.toDist (regularQuotientMap u) (regularQuotientMap v) =
      sInf (Set.range (fun γ : G => angular u.val (leftRegular γ v.val))) := M.distance_eq u v

/-- The quotient distance is bounded by every representative angular distance. -/
theorem spherical_quotient_dist_le_angle (u v : RegularSphere G) (γ : G) :
    @dist (RegularOrbitQuotient G) M.metric.toDist (regularQuotientMap u) (regularQuotientMap v) ≤ angular u.val (leftRegular γ v.val) := by
  letI := M.metric
  rw [spherical_quotient_distance M]
  apply csInf_le
  · exact ⟨0,by rintro a ⟨δ,rfl⟩; exact Real.arccos_nonneg _⟩
  · exact Set.mem_range_self γ

/-- Representatives can approach the actual quotient distance arbitrarily
closely; no attainment of the group infimum is assumed. -/
theorem spherical_quotient_exists_angle_lt (u v : RegularSphere G) (ε : ℝ) (hε : 0 < ε) :
    ∃ γ : G, angular u.val (leftRegular γ v.val) <
      @dist (RegularOrbitQuotient G) M.metric.toDist (regularQuotientMap u) (regularQuotientMap v)+ε := by
  letI := M.metric
  by_contra h
  have hb : dist (regularQuotientMap u) (regularQuotientMap v)+ε ≤
      sInf (Set.range (fun γ : G => angular u.val (leftRegular γ v.val))) := by
    apply le_csInf (Set.range_nonempty _)
    rintro a ⟨γ,rfl⟩
    exact not_lt.mp (not_exists.mp h γ)
  rw [← spherical_quotient_distance M] at hb
  linarith

end Paper28
